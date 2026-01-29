import argparse
import hashlib
import json
import random
import re
import time
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple
from urllib.parse import urljoin, urlparse, parse_qs, urlencode, urlunparse, unquote

import requests
from bs4 import BeautifulSoup


# -----------------------------
# Config (FAST + SAFE)
# -----------------------------

DEFAULT_MAX_JOBS_PER_SEED = 2000
DEFAULT_MAX_PAGES_PER_SEED = 120

CANDIDATE_TIMEOUT = 5
DETAIL_TIMEOUT = 10

CANDIDATE_RETRIES = 0
DETAIL_RETRIES = 1

BACKOFF_BASE_SEC = 0.6
SLEEP_BETWEEN_REQUESTS_SEC = 0.05

JOB_RECORDS_PER_PAGE_TRY = 100
FALLBACK_PAGE_STEP = 20

MAX_DNS_FAILS_PER_HOST = 2

USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Edge/122 Safari/537.36",
]

SEED_BAD_KEYWORDS = [
    "mailredir.php", "accommodationrequest", "unsubscribe", "ltrk/",
    "docs.avature.net", "marketing.avature.net",
    "campusandeventssolution.pdf", ".pdf",
    "event", "events", "eventlisting", "eventregistration",
    "projectdetail", "pipelinedetail",
    "talentnetwork", "talentcommunity", "quickapply",
    "formcompletionrequest", "profile", "login",
    "_linkedinapiv2", "shareurl=", "ref=",
    "resetpassword", "talentportal", "/careers/home", "/jobs/home", "/home",
]

JOB_DETAIL_HINTS = [
    "/JobDetail/", "/jobdetail/", "/JobRoom/JobDetail/",
    "jobdetail?jobid=", "jobdetail?jobId=",
]

INVITE_HINTS = ["/InviteToApply", "/invitetoapply"]

BAD_LINK_KEYWORDS = [
    "SaveJob", "SaveJobSuccess", "Register", "unsubscribe",
    "mailRedir.php", "Accommodationrequest", "Profile",
]

BASE_PATHS = ["careers", "jobs", "external", "opportunities", "talent"]


#  Label aliases (title fix: "Job Advert Title" add)
FIELD_ALIASES = {
    "title": [
        "Job Advert Title",      #  important for Astellas-like tenants
        "Job Title", "Title", "Position Title", "Job", "Role", "Position",
        "Posting Title", "Job Posting Title",
    ],
    "location": [
        "Location", "Job Location", "Work Location", "Posting Location",
        "Advertising location", "Advertising Location",
    ],
    "posted": [
        "Date Posted", "Posted Date", "Posted", "Date",
        "Date Published", "Publish Date", "Publication Date",
    ],
  
}

BAD_TITLE_SNIPPETS = {
    "home page", "careers", "jobs", "careers marketplace", "login", "register"
}


@dataclass
class JobItem:
    job_url: str
    source_url: str
    source_site: str
    job_id: Optional[str]
    title: Optional[str]
    location: Optional[str]
    posted_at: Optional[str]
    apply_url: Optional[str]
    description_html: Optional[str]
    description_text: Optional[str]
    scraped_at: str


# -----------------------------
# Small helpers
# -----------------------------
def now_utc_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def normalize_space(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "")).strip()


def enforce_https(u: str) -> str:
    p = urlparse(u)
    if p.scheme.lower() == "http":
        return urlunparse(p._replace(scheme="https"))
    if not p.scheme:
        return "https://" + u.lstrip("/")
    return u


def canonicalize_url(u: str) -> str:
    """
    Keep important params; drop fragments and tracking noise.
    """
    p = urlparse(u)
    qs = parse_qs(p.query)

    keep_keys = {"jobid", "id", "joboffset", "jobrecordsperpage"}
    keep: Dict[str, List[str]] = {}

    for k, v in qs.items():
        lk = (k or "").lower()
        if lk in keep_keys:
            keep[k] = v
            continue
        if lk.startswith("utm_"):
            continue
        if lk in ("source", "src", "ref", "shareurl", "recommendation", "tags", "user", "formvalues"):
            continue
        keep[k] = v

    flat = []
    for k, vals in keep.items():
        for vv in vals:
            flat.append((k, vv))
    new_query = urlencode(flat, doseq=True)

    return urlunparse(p._replace(query=new_query, fragment=""))


def make_session() -> requests.Session:
    s = requests.Session()
    s.headers.update({
        "User-Agent": random.choice(USER_AGENTS),
        "Accept": "text/html,application/json;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
        "Connection": "keep-alive",
    })
    return s


def is_dns_failure(err_msg: str) -> bool:
    em = (err_msg or "").lower()
    return ("failed to resolve" in em) or ("name resolution" in em) or ("getaddrinfo failed" in em)


def fetch(
    session: requests.Session,
    url: str,
    timeout: int,
    retries: int,
    rotate_ua_on_403: bool = True
) -> Tuple[Optional[requests.Response], Optional[str]]:
    tries = max(1, retries + 1)
    last_err = None

    for attempt in range(tries):
        try:
            resp = session.get(url, timeout=timeout, allow_redirects=True)

            if rotate_ua_on_403 and resp.status_code in (403, 406):
                session.headers["User-Agent"] = random.choice(USER_AGENTS)
                try:
                    resp2 = session.get(url, timeout=timeout, allow_redirects=True)
                    return resp2, None
                except requests.exceptions.RequestException as e2:
                    return None, str(e2)

            return resp, None

        except requests.exceptions.RequestException as e:
            last_err = str(e)
            if attempt < tries - 1:
                time.sleep(BACKOFF_BASE_SEC + random.uniform(0, 0.25))

    return None, last_err


def is_bad_link(href: str) -> bool:
    if not href:
        return True
    h = href.lower()
    return any(k.lower() in h for k in BAD_LINK_KEYWORDS)


def looks_like_job_detail(u: str) -> bool:
    ul = u.lower()
    return any(h.lower() in ul for h in JOB_DETAIL_HINTS)


def looks_like_invite(u: str) -> bool:
    ul = u.lower()
    return any(h.lower() in ul for h in INVITE_HINTS)


def extract_job_id(url: str) -> Optional[str]:
    qs = parse_qs(urlparse(url).query)
    for key in ["jobId", "jobid", "id"]:
        if key in qs and qs[key]:
            return qs[key][0]
    path = urlparse(url).path
    m = re.search(r"/(\d{2,})/?$", path)
    return m.group(1) if m else None


def seed_is_garbage(u: str) -> bool:
    if not u:
        return True
    ul = u.strip().lower()
    if "avature.net" not in ul:
        return True
    if any(k in ul for k in SEED_BAD_KEYWORDS):
        return True
    return False


def normalize_seed(u: str) -> str:
    u = enforce_https(u.strip())
    u = canonicalize_url(u)
    return u.rstrip("/")


def load_seed_file(input_dir: Path, mode: str) -> Tuple[List[str], Dict[str, int]]:
    file_map = {
        "raw": input_dir / "avature_sites_raw.txt",
        "clean": input_dir / "avature_sites_clean.txt",
    }
    p = file_map[mode]
    if not p.exists():
        raise FileNotFoundError(f"Missing input file: {p}")

    raw_lines = p.read_text(encoding="utf-8", errors="ignore").splitlines()

    seen: Set[str] = set()
    seeds: List[str] = []
    stats = {"loaded_lines": 0, "garbage_ignored": 0, "deduped": 0}

    for line in raw_lines:
        stats["loaded_lines"] += 1
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if seed_is_garbage(line):
            stats["garbage_ignored"] += 1
            continue
        s = normalize_seed(line)
        if s in seen:
            stats["deduped"] += 1
            continue
        seen.add(s)
        seeds.append(s)

    return seeds, stats


# -----------------------------
# Candidate discovery
# -----------------------------
def build_search_candidates(seed_url: str) -> List[str]:
    seed_url = seed_url.rstrip("/")
    p = urlparse(seed_url)
    root = f"{p.scheme}://{p.netloc}"

    candidates: List[str] = [seed_url]

    for base in BASE_PATHS:
        candidates.append(f"{root}/{base}")
        candidates.append(f"{root}/{base}/SearchJobs")
        candidates.append(f"{root}/{base}/SearchJobsAllJobs")
        candidates.append(f"{root}/{base}/SearchJobs?jobOffset=0&jobRecordsPerPage={JOB_RECORDS_PER_PAGE_TRY}")
        candidates.append(f"{root}/{base}/SearchJobsAllJobs?jobOffset=0&jobRecordsPerPage={JOB_RECORDS_PER_PAGE_TRY}")

    out, seen = [], set()
    for c in candidates:
        c = canonicalize_url(c)
        if c not in seen:
            seen.add(c)
            out.append(c)
    return out


def load_first_working_candidate(
    session: requests.Session,
    seed_url: str,
    host_dns_fails: Dict[str, int],
    dead_hosts: Set[str],
) -> Optional[str]:
    host = urlparse(seed_url).netloc
    if host in dead_hosts:
        return None

    for c in build_search_candidates(seed_url):
        resp, err = fetch(session, c, timeout=CANDIDATE_TIMEOUT, retries=CANDIDATE_RETRIES)
        time.sleep(SLEEP_BETWEEN_REQUESTS_SEC)

        if not resp:
            if err and is_dns_failure(err):
                host_dns_fails[host] = host_dns_fails.get(host, 0) + 1
                if host_dns_fails[host] >= MAX_DNS_FAILS_PER_HOST:
                    dead_hosts.add(host)
                    return None
            continue

        if resp.status_code == 200 and resp.text and len(resp.text) > 200:
            return str(resp.url)

    return None


def canonical_search_base(u: str) -> str:
    u = enforce_https(canonicalize_url(u))
    p = urlparse(u)
    path = p.path or "/"

    m = re.search(r"(.*?/(SearchJobsAllJobs|SearchJobs))(?:/.*)?$", path, re.IGNORECASE)
    if m:
        base_path = m.group(1)
        return urlunparse(p._replace(path=base_path, query="", fragment=""))

    return urlunparse(p._replace(query="", fragment=""))


# -----------------------------
# Listing parsing + pagination
# -----------------------------
def ensure_params(url: str, params: Dict[str, str]) -> str:
    p = urlparse(url)
    qs = parse_qs(p.query)
    for k, v in params.items():
        qs[k] = [str(v)]
    flat = []
    for k, vals in qs.items():
        for vv in vals:
            flat.append((k, vv))
    return urlunparse(p._replace(query=urlencode(flat, doseq=True)))


def convert_invite_to_jobdetail(invite_url: str) -> Optional[str]:
    jid = extract_job_id(invite_url)
    if not jid:
        return None
    p = urlparse(invite_url)
    root = f"{p.scheme}://{p.netloc}"
    path = p.path.lower()
    base = "careers" if "/careers/" in path else "jobs"
    return f"{root}/{base}/JobDetail?jobId={jid}"


def find_job_links_from_html(html: str, page_url: str) -> List[str]:
    links: Set[str] = set()

    for m in re.finditer(r'href=["\']([^"\']+)["\']', html, re.IGNORECASE):
        href = (m.group(1) or "").strip()
        if not href or is_bad_link(href):
            continue

        abs_u = canonicalize_url(urljoin(page_url, href))

        if looks_like_job_detail(abs_u):
            links.add(abs_u)
        elif looks_like_invite(abs_u):
            jd = convert_invite_to_jobdetail(abs_u)
            if jd:
                links.add(canonicalize_url(jd))

    for m in re.finditer(r'https?://[^\s"\']+', html):
        u = canonicalize_url(m.group(0))
        if is_bad_link(u):
            continue
        if looks_like_job_detail(u):
            links.add(u)
        elif looks_like_invite(u):
            jd = convert_invite_to_jobdetail(u)
            if jd:
                links.add(canonicalize_url(jd))

    return sorted(links)


def collect_job_links_with_pagination(
    session: requests.Session,
    base_page_url: str,
    max_pages: int,
    max_jobs: int
) -> List[str]:
    all_links: Set[str] = set()
    page_signatures: Set[str] = set()
    empty_pages = 0

    base_l = base_page_url.lower()
    is_search = ("searchjobs" in base_l) or ("searchjobsalljobs" in base_l)

    if not is_search:
        resp, _ = fetch(session, base_page_url, timeout=DETAIL_TIMEOUT, retries=DETAIL_RETRIES)
        time.sleep(SLEEP_BETWEEN_REQUESTS_SEC)
        if resp and resp.status_code == 200 and resp.text:
            return find_job_links_from_html(resp.text, str(resp.url))
        return []

    offset = 0
    step_guess: Optional[int] = None

    for _ in range(max_pages):
        page_url = ensure_params(base_page_url, {
            "jobOffset": str(offset),
            "jobRecordsPerPage": str(JOB_RECORDS_PER_PAGE_TRY),
        })

        resp, _ = fetch(session, page_url, timeout=DETAIL_TIMEOUT, retries=DETAIL_RETRIES)
        time.sleep(SLEEP_BETWEEN_REQUESTS_SEC)

        if not resp or resp.status_code != 200 or not resp.text:
            empty_pages += 1
            if empty_pages >= 2:
                break
            offset += (step_guess or FALLBACK_PAGE_STEP)
            continue

        html = resp.text

        sig = hashlib.md5(html[:2000].encode("utf-8", errors="ignore")).hexdigest()
        if sig in page_signatures:
            break
        page_signatures.add(sig)

        links = find_job_links_from_html(html, str(resp.url))
        extracted_count = len(links)

        if step_guess is None:
            if 0 < extracted_count < int(JOB_RECORDS_PER_PAGE_TRY * 0.6):
                step_guess = max(extracted_count, FALLBACK_PAGE_STEP)
            else:
                step_guess = JOB_RECORDS_PER_PAGE_TRY

        new_count = 0
        for u in links:
            if u not in all_links:
                all_links.add(u)
                new_count += 1

        if new_count == 0:
            empty_pages += 1
            if empty_pages >= 2:
                break
        else:
            empty_pages = 0

        if len(all_links) >= max_jobs:
            break

        offset += (step_guess or FALLBACK_PAGE_STEP)

    return sorted(all_links)


# -----------------------------
# Detail parsing (MAX coverage)
# -----------------------------
def extract_label_value_map(soup: BeautifulSoup) -> Dict[str, str]:
    out: Dict[str, str] = {}
    fields = soup.select(".article__content__view__field")
    for f in fields:
        ld = f.select_one(".article__content__view__field__label")
        vd = f.select_one(".article__content__view__field__value")
        if not ld or not vd:
            continue
        k = normalize_space(ld.get_text(" ", strip=True)).lower()
        v = normalize_space(vd.get_text(" ", strip=True))
        if k and v and k not in out:
            out[k] = v
    return out


def get_by_alias(fields: Dict[str, str], aliases: List[str]) -> Optional[str]:
    for a in aliases:
        v = fields.get(a.lower())
        if v:
            return v
    return None


def normalize_posted_date(raw: Optional[str]) -> Optional[str]:
    if not raw:
        return None
    raw = raw.strip()

    if re.match(r"^\d{4}-\d{2}-\d{2}$", raw):
        return raw

    numeric_fmts = (
        "%m/%d/%Y", "%m/%d/%y",
        "%d/%m/%Y", "%d/%m/%y",
        "%m-%d-%Y", "%m-%d-%y",
        "%d-%m-%Y", "%d-%m-%y",
    )
    for fmt in numeric_fmts:
        try:
            dt = datetime.strptime(raw, fmt)
            return dt.strftime("%Y-%m-%d")
        except Exception:
            pass

    for fmt in ("%A, %B %d, %Y", "%b %d, %Y", "%B %d, %Y"):
        try:
            dt = datetime.strptime(raw, fmt)
            return dt.strftime("%Y-%m-%d")
        except Exception:
            pass

    return raw


def clean_title(t: Optional[str]) -> Optional[str]:
    if not t:
        return None
    t = normalize_space(t)
    t = re.sub(r"\s*-\s*Careers Marketplace\s*$", "", t, flags=re.IGNORECASE)
    t = re.sub(r"\s*\|\s*Careers\s*$", "", t, flags=re.IGNORECASE)
    t = re.sub(r"\s*-\s*Careers\s*$", "", t, flags=re.IGNORECASE)
    return t or None


def is_garbage_title(title: Optional[str]) -> bool:
    if not title:
        return True
    tl = normalize_space(title).lower()
    if len(tl) < 3:
        return True
    for snip in BAD_TITLE_SNIPPETS:
        if snip in tl:
            return True
    return False


def extract_title_from_title_block(soup: BeautifulSoup) -> Optional[str]:
    el = soup.select_one(".article__content__view__field.title .article__content__view__field__value")
    if el:
        t = normalize_space(el.get_text(" ", strip=True))
        return clean_title(t)

    el2 = soup.select_one(".article__content__view__field[class*='title'] .article__content__view__field__value")
    if el2:
        t = normalize_space(el2.get_text(" ", strip=True))
        return clean_title(t)
    return None


def extract_title_fallback_from_html(html: str) -> Optional[str]:
    m = re.search(r'aria-label="Share\s+([^"]+?)\s+with\s+(Facebook|X|a friend)', html, re.IGNORECASE)
    if m:
        return clean_title(m.group(1))

    m = re.search(r'data-jobname="([^"]+)"', html, re.IGNORECASE)
    if m:
        return clean_title(m.group(1))

    # twitter intent has text=...
    m = re.search(r"twitter\.com/intent/tweet\?[^\"']*text=([^&\"']+)", html, re.IGNORECASE)
    if m:
        try:
            t = unquote(m.group(1)).replace("+", " ")
            return clean_title(t)
        except Exception:
            pass

    m = re.search(r"mailto:\?subject=([^&]+)", html, re.IGNORECASE)
    if m:
        try:
            t = unquote(m.group(1)).replace("+", " ")
            return clean_title(t)
        except Exception:
            pass

    m = re.search(r"<title[^>]*>\s*(.*?)\s*</title>", html, re.IGNORECASE | re.DOTALL)
    if m:
        t = normalize_space(re.sub(r"<[^>]+>", " ", m.group(1)))
        return clean_title(t)

    return None


def parse_job_detail(session: requests.Session, job_url: str, source_url: str) -> Optional[JobItem]:
    resp, _ = fetch(session, job_url, timeout=DETAIL_TIMEOUT, retries=DETAIL_RETRIES)
    time.sleep(SLEEP_BETWEEN_REQUESTS_SEC)
    if not resp or resp.status_code != 200 or not resp.text or len(resp.text) < 200:
        return None

    final_url = canonicalize_url(str(resp.url))
    html = resp.text

    try:
        soup = BeautifulSoup(html, "lxml")
    except Exception:
        soup = BeautifulSoup(html, "html.parser")

    fields = extract_label_value_map(soup)

    # --- TITLE (max coverage) ---
    title = get_by_alias(fields, FIELD_ALIASES["title"])

    if not title:
        title = extract_title_from_title_block(soup)

    if not title:
        h1 = soup.find("h1")
        if h1:
            title = normalize_space(h1.get_text(" ", strip=True))

    if not title:
        og = soup.find("meta", attrs={"property": "og:title"})
        if og and og.get("content"):
            title = normalize_space(og["content"])

    if not title and soup.title and soup.title.string:
        title = normalize_space(soup.title.string)

    title = clean_title(title)
    if is_garbage_title(title):
        tf = extract_title_fallback_from_html(html)
        if tf:
            title = tf

    title = clean_title(title)

    # --- LOCATION ---
    location = get_by_alias(fields, FIELD_ALIASES["location"])

    if not location:
        adv = fields.get("advertising location")
        if adv:
            location = adv

    if not location:
        city = fields.get("posting city") or fields.get("city")
        state = fields.get("posting state") or fields.get("state")
        country = fields.get("posting country") or fields.get("country")
        parts = [p for p in [city, state, country] if p]
        if parts:
            location = ", ".join(parts)

    # --- POSTED DATE ---
    posted_raw = get_by_alias(fields, FIELD_ALIASES["posted"])
    posted_at = normalize_posted_date(posted_raw)

   

    # --- DESCRIPTION ---
    desc_html = None
    desc_text = None

    section1 = soup.select_one("#section1__content")
    if section1:
        desc_html = str(section1)
        desc_text = normalize_space(section1.get_text(" ", strip=True))
    else:
        rich = soup.select_one(".field--rich-text .article__content__view__field__value")
        if rich:
            desc_html = str(rich)
            desc_text = normalize_space(rich.get_text(" ", strip=True))
        else:
            main = soup.select_one("#main-panel") or soup.select_one("main")
            if main:
                desc_html = str(main)
                desc_text = normalize_space(main.get_text(" ", strip=True))

    job_id = extract_job_id(final_url)

    # --- APPLY URL ---
    apply_url = None
    apply_a = soup.select_one('a[href*="ApplicationMethods"]')
    if apply_a and apply_a.get("href"):
        apply_url = canonicalize_url(urljoin(final_url, apply_a["href"]))
    elif job_id:
        root = f"{urlparse(final_url).scheme}://{urlparse(final_url).netloc}"
        path = urlparse(final_url).path.lower()
        base = "careers" if "/careers/" in path else "jobs"
        apply_url = f"{root}/{base}/ApplicationMethods?jobId={job_id}"
    else:
        apply_url = final_url

    # Quality gate (avoid garbage pages)
    if (not desc_text or len(desc_text) < 80) and (not title or len(title) < 3):
        return None

    source_site = urlparse(source_url).netloc or urlparse(final_url).netloc

    return JobItem(
        job_url=final_url,
        source_url=source_url,
        source_site=source_site,
        job_id=job_id,
        title=title,
        location=location,
        posted_at=posted_at,
        apply_url=apply_url,
        description_html=desc_html,
        description_text=desc_text,
        scraped_at=now_utc_iso(),
    )


# -----------------------------
# Output helpers
# -----------------------------
def save_json(path: Path, data: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")


def load_existing_json(path: Path) -> Dict[str, dict]:
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}


def load_existing_jsonl_keys(path: Path) -> Set[str]:
    keys: Set[str] = set()
    if not path.exists():
        return keys
    try:
        with path.open("r", encoding="utf-8", errors="ignore") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                    source_site = obj.get("source_site") or ""
                    job_id = obj.get("job_id") or ""
                    job_url = obj.get("job_url") or ""
                    key = f"{source_site}:{job_id}" if (source_site and job_id) else job_url
                    if key:
                        keys.add(key)
                except Exception:
                    continue
    except Exception:
        pass
    return keys


def append_jsonl(path: Path, item: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(item, ensure_ascii=False) + "\n")


# -----------------------------
# Main
# -----------------------------
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seeds", choices=["raw", "clean"], required=True)
    parser.add_argument("--max-seeds", type=int, default=0, help="0 = all")
    parser.add_argument("--output", default="", help="Optional output filename")
    parser.add_argument("--format", choices=["json", "jsonl"], default="json")

    # dedup behavior (crawler level)
    parser.add_argument("--dedup-mode", choices=["base", "host", "none"], default="base")

    #  caps / pagination tuning
    parser.add_argument("--cap-jobs", type=int, default=DEFAULT_MAX_JOBS_PER_SEED, help="Max jobs per seed (cap)")
    parser.add_argument("--max-pages", type=int, default=DEFAULT_MAX_PAGES_PER_SEED, help="Max listing pages per seed")

    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    input_dir = root / "input"
    output_dir = root / "output"
    output_dir.mkdir(parents=True, exist_ok=True)

    out_name = args.output.strip()
    if not out_name:
        out_name = "jobs.jsonl" if args.format == "jsonl" else "jobs.json"

    if args.format == "jsonl" and not out_name.lower().endswith(".jsonl"):
        out_name += ".jsonl"
    if args.format == "json" and not out_name.lower().endswith(".json"):
        out_name += ".json"

    out_path = output_dir / out_name
    summary_path = output_dir / f"run_summary_{args.seeds}.json"

    seeds, stats = load_seed_file(input_dir, args.seeds)
    if args.max_seeds and args.max_seeds > 0:
        seeds = seeds[:args.max_seeds]

    # ✅ Logs back to old-style (seed-by-seed)
    print("=== Avature ATS Scraper (raw/clean + safe pagination + base dedup) ===")
    print(f"Seed mode: {args.seeds}")
    print(f"Loaded lines: {stats['loaded_lines']}, garbage: {stats['garbage_ignored']}, dedup: {stats['deduped']}")
    print(f"Final seeds: {len(seeds)}")
    print(f"Format: {args.format}")
    print(f"Dedup mode: {args.dedup_mode}")
    print(f"Cap jobs/seed: {args.cap_jobs}")
    print(f"Max pages/seed: {args.max_pages}")
    print(f"Output: {out_path}\n")

    session = make_session()

    processed_hosts: Set[str] = set()
    processed_bases: Set[str] = set()

    host_dns_fails: Dict[str, int] = {}
    dead_hosts: Set[str] = set()

    seeds_ok = 0
    seeds_failed = 0

    jobs_json: Dict[str, dict] = {}
    seen_jsonl: Set[str] = set()

    if args.format == "json":
        jobs_json = load_existing_json(out_path)
        if not jobs_json:
            save_json(out_path, {})
    else:
        seen_jsonl = load_existing_jsonl_keys(out_path)
        if not out_path.exists():
            out_path.write_text("", encoding="utf-8")

    total_new = 0
    dup_local = 0

    for i, seed in enumerate(seeds, start=1):
        host = urlparse(seed).netloc

        print(f"[{i}/{len(seeds)}] Seed: {seed}")

        if host in dead_hosts:
            print("  ❌ Host marked dead (DNS failures). Skipping.\n")
            seeds_failed += 1
            continue

        if args.dedup_mode == "host" and (host in processed_hosts):
            print("  ↩️ Host already processed successfully. Skipping duplicate seed.\n")
            continue

        candidate = load_first_working_candidate(session, seed, host_dns_fails, dead_hosts)
        if not candidate:
            print("  ❌ Cannot load any candidate page. Skipping.\n")
            seeds_failed += 1
            continue

        base_key = canonical_search_base(candidate)
        if args.dedup_mode == "base" and (base_key in processed_bases):
            print("  ↩️ Tenant base already processed. Skipping duplicate seed.\n")
            continue

        job_links = collect_job_links_with_pagination(
            session=session,
            base_page_url=candidate,
            max_pages=args.max_pages,
            max_jobs=args.cap_jobs
        )
        job_links = [u for u in job_links if not is_bad_link(u)]

        if not job_links:
            print("  ⚠️ No job links found. Skipping.\n")
            seeds_failed += 1
            continue

        seeds_ok += 1
        print(f"  🔗 Found job detail links: {len(job_links)} (cap {args.cap_jobs})")

        processed_this_seed = 0
        limit = min(len(job_links), args.cap_jobs)

        for idx_j, job_url in enumerate(job_links[:args.cap_jobs], start=1):
            if idx_j % 10 == 0 or idx_j == limit:
                print(f"    ...processing {idx_j}/{limit} job details")

            job = parse_job_detail(session, job_url, seed)
            if not job:
                continue

            key = f"{job.source_site}:{job.job_id}" if job.job_id else job.job_url

            if args.format == "json":
                if key in jobs_json:
                    dup_local += 1
                    continue
                jobs_json[key] = asdict(job)
                total_new += 1
                processed_this_seed += 1
                if total_new % 100 == 0:
                    save_json(out_path, jobs_json)
            else:
                if key in seen_jsonl:
                    dup_local += 1
                    continue
                append_jsonl(out_path, asdict(job))
                seen_jsonl.add(key)
                total_new += 1
                processed_this_seed += 1

        if processed_this_seed > 0:
            if args.dedup_mode == "host":
                processed_hosts.add(host)
            elif args.dedup_mode == "base":
                processed_bases.add(base_key)

        if args.format == "json":
            save_json(out_path, jobs_json)

        total_jobs_now = len(jobs_json) if args.format == "json" else len(seen_jsonl)
        print(f"   Done seed. New jobs this seed: {processed_this_seed}. Total jobs so far: {total_jobs_now}\n")

    total_jobs = len(jobs_json) if args.format == "json" else len(seen_jsonl)

    #  Minimal summary (important only) + no good/bad seed files
    summary = {
        "seed_mode": args.seeds,
        "format": args.format,
        "dedup_mode": args.dedup_mode,
        "total_lines_loaded": stats["loaded_lines"],
        "garbage_ignored": stats["garbage_ignored"],
        "deduped": stats["deduped"],
        "final_seeds_tried": len(seeds),
        "sites_ok_with_jobs": seeds_ok,
        "sites_failed_or_empty": seeds_failed,
        "total_jobs": total_jobs,
        "jobs_new_this_run": total_new,
        "dup_local_skipped": dup_local,
        "jobs_file": str(out_path),
        "finished_at_utc": now_utc_iso(),
        "notes": {
            "cap_jobs_per_seed": args.cap_jobs,
            "max_pages_per_seed": args.max_pages,
            "jobRecordsPerPage_try": JOB_RECORDS_PER_PAGE_TRY,
        }
    }
    save_json(summary_path, summary)

    print("=== Completed ===")
    print(f"Total jobs scraped: {total_jobs}")
    print(f"New jobs this run: {total_new}")
    print(f"Local duplicates skipped: {dup_local}")
    print(f"Output written to: {out_path}")
    print(f"Summary written to: {summary_path}")


if __name__ == "__main__":
    main()
