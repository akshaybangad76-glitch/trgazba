#!/usr/bin/env python3
"""
Firebase Hunter v7.0 — Telegram Bot for Railway
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Pure Telegram bot. Runs a tiny HTTP health server on $PORT for Railway.
"""
from __future__ import annotations

import argparse
import http.client
import json
import os
import random
import re
import secrets
import sqlite3
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse, parse_qsl, urlencode, quote_plus
from urllib.request import Request, urlopen
from urllib.error import URLError, HTTPError

import requests


# ═══════════════════════════════════════════════════════════════
#  CONFIG
# ═══════════════════════════════════════════════════════════════
BASE = Path(__file__).resolve().parent
DATA = BASE / "data"
DATA.mkdir(exist_ok=True)
DB = DATA / "bulk.sqlite3"
ACTIVE_FILE = DATA / "active.txt"
VERIFIED_FILE = DATA / "valid.txt"
PLAY_JSON = DATA / "playstore_names.json"
PLAY_TXT = DATA / "playstore_names.txt"

TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "").strip()
TG_API = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}" if TELEGRAM_BOT_TOKEN else ""

WORKERS = max(1, min(128, int(os.getenv("BULK_WORKERS", "32"))))
MAX_URLS = max(1, int(os.getenv("BULK_MAX_URLS", "100000")))
MAX_BYTES = max(4096, int(os.getenv("BULK_MAX_BYTES", "10485760")))
TIMEOUT = max(2, min(30, int(os.getenv("BULK_TIMEOUT", "6"))))
MAX_PROBE = 64 * 1024

AUTO_MAX_URLS = max(100, int(os.getenv("BULK_AUTO_MAX_URLS", "10000000")))
AUTO_BATCH = max(50, min(10000, int(os.getenv("BULK_AUTO_BATCH", "500"))))
AUTO_EXPAND = os.getenv("BULK_AUTO_EXPAND", "1") == "1"
AUTO_REGIONAL_PROB = float(os.getenv("BULK_REGIONAL_PROB", "0.05"))

FIREBASE_DEFAULT_KEY = os.getenv("FIREBASE_DEFAULT_KEY", "12")
VERIFY_TIMEOUT = 10
VERIFY_KEYS = [FIREBASE_DEFAULT_KEY, "", None]

FILE_INTERVAL = int(os.getenv("FILE_INTERVAL_MIN", "30")) * 60
RATE_WINDOW = 60
RATE_LIMIT = int(os.getenv("BULK_RATE_LIMIT", "30"))
USER_RATE: dict = {}
RATE_LOCK = threading.Lock()

ACTIVE_URLS: set = set()
VERIFIED_URLS: set = set()
ACTIVE_LOCK = threading.Lock()
VERIFIED_LOCK = threading.Lock()
_TLS = threading.local()
STOP = threading.Event()
LOG_LOCK = threading.Lock()
GEN_LOCK = threading.Lock()

USER_STATE: dict = {}
ACTIVE_MESSAGES: dict = {}
UPDATES_OFFSET = 0

PROJECT_ID_RE = re.compile(r"^[a-z][a-z0-9-]{4,28}[a-z0-9]$")
RE_LEGACY_HOST = re.compile(r"^[a-z0-9][a-z0-9-]*\.firebaseio\.com$", re.I)
RE_REGIONAL_HOST = re.compile(
    r"^[a-z0-9][a-z0-9-]*\.[a-z0-9-]+\.firebasedatabase\.app$", re.I
)


# ═══════════════════════════════════════════════════════════════
#  PLAY STORE NAMES
# ═══════════════════════════════════════════════════════════════
def _load_play_names() -> list[str]:
    if PLAY_JSON.exists():
        try:
            data = json.loads(PLAY_JSON.read_text(encoding="utf-8"))
            if isinstance(data, dict) and data:
                items = sorted(
                    ((k, int(v)) for k, v in data.items()
                     if isinstance(k, str) and k),
                    key=lambda kv: (-kv[1], kv[0]),
                )
                return [k for k, _ in items]
        except Exception:
            pass
    if PLAY_TXT.exists():
        try:
            return [line.strip() for line in
                    PLAY_TXT.read_text(encoding="utf-8").splitlines()
                    if line.strip()]
        except Exception:
            pass
    return []


PLAY_NAMES: list[str] = _load_play_names()


# ═══════════════════════════════════════════════════════════════
#  WORD POOLS
# ═══════════════════════════════════════════════════════════════
NAMES_M = """
raj rahul sanjay ramesh sonu manish karan amit suman rohit arvind deepak
sivam ajay shivam navin pintu krisna sumit anvith yogesh ram ravi shiva
raja arjun vikram abhishek aman anil ankit ashok balaji bhavesh chetan
dinesh ganesh gaurav gopal hari harish hemant jagdish kamal kishor kumar
lalit madan mahesh mohan mukesh naresh nikhil nilesh nitin omkar pankaj
prakash prasad praveen prem rajat rakesh ranjan rohan sachin sahil
sameer sandeep santosh satish saurabh shreyas siddharth sudhir suresh
surya tarun uday umesh varun vijay vinod vipin vishal vivek yash yuvraj
aditya akshay arnav atharva bhargav darsh dhanush dhruv harsh hitesh
jayesh kalpesh kartik kaushik krishna lokesh nandan nayan nishant nitish
parth pranav pratik rishi ritik sahith sai samarth shlok shubham sid
soham srikant sriram suraj tej tanmay tushar utkarsh vedant vihaan
vineet vinay virat vishnu zaid ansh bhavya chirag dev divyansh faizan
farhan gagan gurpreet hemanshu ishaan jai jaspreet kabir kailash
manav mihir mohit naman neeraj ojas om pandit parag prithvi raghav
rishabh rudra saarthak samay shashank shivansh shourya siddhesh sooraj
srikar tanay tejas tirth vaibhav ved vyom yashwant
""".split()

NAMES_F = """
priya pooja khushi anjali siya kavya riya neha sneha ritu sita geeta
meera radha lakshmi sunita kavita nisha shilpa shweta tanvi tara trisha
vidya yamini zara aditi aishwarya amrita ananya anisha asha bhavna chitra
deepa divya ekta gauri gayatri hema indira ishita jaya jyoti kalpana
kiran komal kripa lata madhu madhuri mala manisha meena naina namrata
nandini nayana neelam nidhi nirmala pallavi parul payal pragya pratibha
preeti priyanka pushpa radhika rani rashmi reena rekha renuka reshma
rina ruchi rupali sadhana sangeeta sarita savita seema shanti sheela
shobha shraddha shruti sindhu smita sonal sonia sridevi sudha sujata
sunanda supriya swati tanuja uma urmila usha vaishali vandana varsha
veena vimala vinita yashodha ahana alisha amaira anika arushi avni
dhriti diya hetvi ira ishani jhanvi kaira kiara kritika kushi mahika
myra naisha navya netra pari piya saanvi sara saumya shreya tanya trixi
vedika zoya aaradhya akansha alka amala anita aparna archana bharti
bhumi chandni chhaya damini darshana devika dhanvi esha falguni gargi
gitanjali guddi harshita hemangi jagruti janvi jasmine kalindi kamini
karishma kashish kumkum lakshita lalita lavanya leela madhavi mahima
megha mohini mridula mukta nalini namita narmada neelima nikita nirali
nivedita padma palak pankti paridhi pinal poonam prerna priti punam
rachna ragini rajni rashi ratri roma roshni rupal rutvi sachi sagarika
sakshi samiksha saniya saroj shalini shanta sharda shashi sheetal
shubhi simran sonam srishti stuti sudiksha suhani sumitra sunaina
swara sweta tanisha tanu tarini trupti tvisha udita urja vaidehi vani
vidhi vijaya vipasha vishakha yashasvi yukti zarna
""".split()

SURNAMES = """
sharma verma gupta agarwal jain singh kumar yadav rao reddy naidu
patel shah mehta desai iyer iyengar pillai nair menon chowdhury
banerjee mukherjee chatterjee bose das dutta ghosh sen roy
khan ali syed sheikh ansari qureshi pathan mirza
kaur ahluwalia grewal sandhu dhillon gill sidhu brar bajwa
joshi trivedi pandey mishra tiwari dubey shukla chaturvedi saxena
srivastava bhattacharya mahajan kapoor khanna malhotra chopra
sethi arora bedi bhalla ahuja sachdeva
""".split()

BANKS = """
sbi hdfc icici axis kotak pnb bob boi uco canara union indian idbi
yes federal rbl bandhan idfc au ujjivan equitas indusind dcb
cbi central bankofindia bankofbaroda punjab national overseas
syndicate corporation andhra vijaya dena allahabad oriental
paytm phonepe gpay googlepay bhim freecharge mobikwik
""".split()

GOVT_SCHEMES = """
pmkisan kisan kisan-samman rto upi aadhaar pan ration mgnrega
pmay ayushman jan-dhan mudra pmjay pmfby pm-svanidhi pm-vishwakarma
pm-awas yojana scheme sarkari sarkar govt government indian
e-shram eshram ekyc kyc e-mitra emitra csc janseva e-seva
passport voter election result admit-card result-exam
scholarship pension pradhan-mantri pradhanmantri
pmkisan-samman-man-dhan kisan-credit-card
fasal-bima jeevan-jyoti jeevan-bima atal-pension sukanya-samriddhi
""".split()

PUBLIC_SERVICE = """
hospital clinic medical health pharmacy medicine doctor patient
school college university coaching tuition exam result admission
panchayat gram nagar-palika municipal corporation ward
police thana kotwali court kachehri collector tehsil tahsildar
patwari lekhpal bdo dm sdm sdo
railway irctc train bus transport roadways rto transport
electricity bijli power water jal gas lpg
""".split()

PORTAL_WORDS = """
panel portal dashboard admin backend service office department
ministry scheme yojana mission abhiyan program project
india bharat bhartiya desi jai-hind vande-mataram
new purana naya latest official real genuine verified
online digital smart e-cyber tech
""".split()

RELATIONAL = """
bhai bhaiya bhabhi didi babu baba chacha mama mami papa mummy beta
beti devar nanad sasur saas nani nana dadi dada chotu monu golu
chintu bablu raju kaka kaki mausa mausi fufa bua deewana yaar dost
behan maa baap ghar parivar khandan sansar
""".split()

ENGLISH = """
app test demo chat user data shop blog game hotel food cafe store
site note todo task list quick smart fast easy cool nice good best
dev prod beta alpha core main team work home office school college
study music video photo book foodie kart pay money cash wallet loan
bill tax hospital clinic doctor pharmacy restaurant market mall
travel flight train bus cab auto yatra trip tour package booking
ticket payment transfer recharge billpay invest credit debit
savings spy clone strange vibe download sorry spirit flash engine
power union axis reliable cogulent privatesok yellow green
dream hope faith truth lie light dark night day sun moon star sky
sea ocean river mountain fire water earth wind storm rain snow
""".split()

CELEB = """
rohit virat sachin dhoni kohli dhawan bumrah hardik salman aamir
shahrukh srk akshay ajay hrithik ranbir ranveer deepika katrina
priyanka anushka alia kareena kangana jacqueline modi rahul-gandhi
kejriwal amit-shah yogi mamata nitish laloo heisenberg jamesbond
pablo pablo-escobar don vito michael tommy batman superman spiderman
ironman thor hulk captain-america flash arrow naruto sasuke itachi
kakashi luffy zoro goku vegeta pokemon pikachu krishna krish arjun
karna bhishma drona duryodhan veerappan manikarnika shivaji
maharana-pratap tipu-sultan akbar babur humayun shah-jahan aurangzeb
maradona messi ronaldo neymar mbappe beckham pele
""".split()

LOVE = """
love pyar ishq mohabbat dosti breakup broken heart dil dilbar dildaar
jaan jaanu jaaneman sanam mehboob mehbooba aashiq aashiqui deewana
deewani pagal paagal yaari judaai milan intezaar forever alone akela
akeli tanha tanhai khushi gham dard rona ansu aansu missyou loveyou
iloveyou loveu sad happy cutie sweetie baby babu shona sona sweety
cutiepie kiss hug chahat aarzoo tamanna khwahish hasrat dhadkan saath
wafa bewafa
""".split()

GAALI = """
chutiyapa chutiyagiri chutkabaal chutmarani bhosdi bhosdike bhosdiwala
bhenchod bhencho bhenchood madarchod madarchood mc bc bkl chodu
chutiye chutiyon gaand gandu gandfat randi randi-ka randi-ka-bachcha
lund lauda lode laund laude lauda-lele tera-maa tera-baap
behen-ke gaandu chakka hijra khusra kinnar
lodu lodugiri lode-laga dogla doglapan dogle kutta kutiya
kutta-kamina kamina kamine harami haramkhor haramzada
saala saali saale sale-kutta badtameez badmaash badmash
""".split()

FIR_AUTOGEN = ["fir", "my-first-project", "first-project", "firebase-app",
               "firebase-demo", "my-app", "my-project", "project-1", "untitled"]

HEX5 = "0123456789abcdef"
KEYBOARD_ROWS = ["qwertyuiop", "asdfghjkl", "zxcvbnm"]
KEYBOARD_ALL = "asdfghjklqwertyuiopzxcvbnm1234567890"
LEET_MAP = str.maketrans({"a": "4", "e": "3", "i": "1", "o": "0", "s": "5"})
REGIONS = ["us-central1", "us-east1", "us-west1", "europe-west1",
           "europe-west2", "asia-southeast1", "asia-east1",
           "asia-northeast1", "australia-southeast1", "southamerica-east1"]
MODIFIERS = ["admin", "panel", "pannel", "penal", "dash", "dashboard",
             "backend", "manager", "owner", "super", "mega", "ultra",
             "plus", "pro", "premium", "vip", "gold", "silver", "king",
             "queen", "master", "boss", "god", "root", "base", "core",
             "temp", "tmp", "old", "new", "real", "original", "clone",
             "copy", "official", "private", "main"]
YEARS = ["2018", "2019", "2020", "2021", "2022", "2023", "2024",
         "2025", "2026", "2027"]

_ALL_NAMES = NAMES_M + NAMES_F
_SECTOR = BANKS + GOVT_SCHEMES + PUBLIC_SERVICE + PORTAL_WORDS


# ═══════════════════════════════════════════════════════════════
#  SCHEMA
# ═══════════════════════════════════════════════════════════════
SCHEMA = """
CREATE TABLE IF NOT EXISTS jobs (
 id INTEGER PRIMARY KEY AUTOINCREMENT,
 token TEXT UNIQUE NOT NULL,
 filename TEXT NOT NULL,
 total INTEGER NOT NULL,
 processed INTEGER NOT NULL DEFAULT 0,
 active INTEGER NOT NULL DEFAULT 0,
 inactive INTEGER NOT NULL DEFAULT 0,
 no_data INTEGER NOT NULL DEFAULT 0,
 unreachable INTEGER NOT NULL DEFAULT 0,
 too_large INTEGER NOT NULL DEFAULT 0,
 status TEXT NOT NULL DEFAULT 'pending',
 error TEXT,
 job_type TEXT NOT NULL DEFAULT 'manual',
 seeds TEXT,
 chat_id INTEGER,
 created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
 started_at TEXT,
 completed_at TEXT,
 updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
);
CREATE TABLE IF NOT EXISTS items (
 id INTEGER PRIMARY KEY AUTOINCREMENT,
 job_id INTEGER NOT NULL,
 url TEXT NOT NULL,
 status TEXT NOT NULL DEFAULT 'pending',
 http_status INTEGER,
 error TEXT,
 latency_ms INTEGER,
 checked_at TEXT,
 FOREIGN KEY(job_id) REFERENCES jobs(id) ON DELETE CASCADE
);
CREATE INDEX IF NOT EXISTS idx_items_pending ON items(job_id,status,id);
CREATE INDEX IF NOT EXISTS idx_items_active ON items(job_id,status);
CREATE INDEX IF NOT EXISTS idx_jobs_status ON jobs(status,id);

CREATE TABLE IF NOT EXISTS active_urls (
 id INTEGER PRIMARY KEY AUTOINCREMENT,
 url TEXT UNIQUE NOT NULL,
 first_seen_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
 last_seen_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
 source_job_id INTEGER,
 http_status INTEGER,
 latency_ms INTEGER,
 device_count INTEGER DEFAULT -1
);
CREATE INDEX IF NOT EXISTS idx_active_urls_url ON active_urls(url);

CREATE TABLE IF NOT EXISTS verified_urls (
 id INTEGER PRIMARY KEY AUTOINCREMENT,
 url TEXT UNIQUE NOT NULL,
 first_seen_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
 last_seen_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
 source_job_id INTEGER,
 device_count INTEGER DEFAULT 0,
 http_status INTEGER,
 latency_ms INTEGER
);
CREATE INDEX IF NOT EXISTS idx_verified_urls_url ON verified_urls(url);

CREATE TABLE IF NOT EXISTS seed_stats (
 seed TEXT PRIMARY KEY,
 attempts INTEGER NOT NULL DEFAULT 0,
 active INTEGER NOT NULL DEFAULT 0,
 last_hit_at TEXT,
 first_seen_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
);
CREATE INDEX IF NOT EXISTS idx_seed_stats_rate ON seed_stats(active, attempts);
"""


# ═══════════════════════════════════════════════════════════════
#  UTILITIES
# ═══════════════════════════════════════════════════════════════
def log(msg: str):
    with LOG_LOCK:
        ts = datetime.now().strftime("%H:%M:%S")
        print(f"[{ts}] {msg}", flush=True)


def now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def esc_html(s) -> str:
    return (str(s or "")
            .replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))


def elapsed_seconds(started_at, ended_at=None) -> int:
    if not started_at:
        return 0
    try:
        s = datetime.fromisoformat(started_at.replace("Z", "+00:00"))
    except Exception:
        return 0
    if ended_at:
        try:
            e = datetime.fromisoformat(ended_at.replace("Z", "+00:00"))
        except Exception:
            e = datetime.now(timezone.utc)
    else:
        e = datetime.now(timezone.utc)
    if s.tzinfo is None: s = s.replace(tzinfo=timezone.utc)
    if e.tzinfo is None: e = e.replace(tzinfo=timezone.utc)
    return max(0, int((e - s).total_seconds()))


def human_duration(sec: int) -> str:
    if sec < 60: return f"{sec}s"
    if sec < 3600: return f"{sec//60}m {sec%60}s"
    return f"{sec//3600}h {(sec%3600)//60}m"


def db():
    c = sqlite3.connect(DB, timeout=60, isolation_level=None)
    c.row_factory = sqlite3.Row
    c.execute("PRAGMA journal_mode=WAL")
    c.execute("PRAGMA synchronous=NORMAL")
    c.execute("PRAGMA foreign_keys=ON")
    c.execute("PRAGMA busy_timeout=60000")
    return c


def init_db():
    c = db()
    c.executescript(SCHEMA)
    cols = {r["name"] for r in c.execute("PRAGMA table_info(jobs)").fetchall()}
    for col, ddl in [
        ("job_type", "ALTER TABLE jobs ADD COLUMN job_type TEXT NOT NULL DEFAULT 'manual'"),
        ("seeds", "ALTER TABLE jobs ADD COLUMN seeds TEXT"),
        ("chat_id", "ALTER TABLE jobs ADD COLUMN chat_id INTEGER"),
    ]:
        if col not in cols:
            try: c.execute(ddl)
            except sqlite3.OperationalError: pass
    c.execute("UPDATE jobs SET status='pending', started_at=NULL "
              "WHERE status='processing' AND job_type='manual'")
    c.execute("UPDATE jobs SET status='stopped' "
              "WHERE status='processing' AND job_type IN ('auto','auto-random')")
    c.close()


def atomic_write_file(path: Path, lines: list):
    try:
        tmp = path.with_suffix(path.suffix + ".tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            f.write("\n".join(lines) + ("\n" if lines else ""))
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    except Exception as e:
        log(f"atomic_write_file error: {e}")


def load_all_persistent():
    try:
        c = db()
        arows = c.execute("SELECT url FROM active_urls ORDER BY id").fetchall()
        vrows = c.execute("SELECT url FROM verified_urls ORDER BY id").fetchall()
        c.close()
        with ACTIVE_LOCK: ACTIVE_URLS.update(r["url"] for r in arows)
        with VERIFIED_LOCK: VERIFIED_URLS.update(r["url"] for r in vrows)
    except Exception as e:
        log(f"load DB error: {e}")

    for fpath, target, lock in [
        (ACTIVE_FILE, ACTIVE_URLS, ACTIVE_LOCK),
        (VERIFIED_FILE, VERIFIED_URLS, VERIFIED_LOCK),
    ]:
        if fpath.exists():
            try:
                with open(fpath, "r", encoding="utf-8") as f:
                    urls = [line.strip() for line in f if line.strip()]
                with lock: target.update(urls)
            except Exception as e:
                log(f"load {fpath.name} error: {e}")

    log(f"📦 Loaded {len(ACTIVE_URLS)} active, {len(VERIFIED_URLS)} verified")


def persist_active(url, source_job_id=None, http_status=None, latency_ms=None):
    url = str(url).strip().rstrip("/")
    if not url: return False
    with ACTIVE_LOCK:
        if url in ACTIVE_URLS:
            try:
                c = db()
                c.execute("UPDATE active_urls SET last_seen_at=?, source_job_id=? "
                          "WHERE url=?", (now(), source_job_id, url))
                c.close()
            except Exception: pass
            return False
        try:
            c = db()
            c.execute("INSERT OR IGNORE INTO active_urls"
                      "(url,last_seen_at,source_job_id,http_status,latency_ms) "
                      "VALUES(?,?,?,?,?)",
                      (url, now(), source_job_id, http_status, latency_ms))
            inserted = c.total_changes == 1
            c.close()
        except Exception as e:
            log(f"persist_active error: {e}"); return False
        if not inserted:
            ACTIVE_URLS.add(url); return False
        ACTIVE_URLS.add(url)
    try:
        with open(ACTIVE_FILE, "a", encoding="utf-8") as f:
            f.write(url + "\n")
    except Exception: pass
    return True


def persist_verified(url, source_job_id=None, device_count=0,
                     http_status=None, latency_ms=None):
    url = str(url).strip().rstrip("/")
    if not url: return False
    with VERIFIED_LOCK:
        if url in VERIFIED_URLS:
            try:
                c = db()
                c.execute("UPDATE verified_urls SET last_seen_at=?, source_job_id=?, "
                          "device_count=MAX(device_count,?) WHERE url=?",
                          (now(), source_job_id, device_count, url))
                c.close()
            except Exception: pass
            return False
        try:
            c = db()
            c.execute("INSERT OR IGNORE INTO verified_urls"
                      "(url,last_seen_at,source_job_id,device_count,http_status,latency_ms) "
                      "VALUES(?,?,?,?,?,?)",
                      (url, now(), source_job_id, device_count, http_status, latency_ms))
            inserted = c.total_changes == 1
            c.close()
        except Exception as e:
            log(f"persist_verified error: {e}"); return False
        if not inserted:
            VERIFIED_URLS.add(url); return False
        VERIFIED_URLS.add(url)
    try:
        with open(VERIFIED_FILE, "a", encoding="utf-8") as f:
            f.write(url + "\n")
    except Exception: pass
    return True


def save_all_files():
    with ACTIVE_LOCK: atomic_write_file(ACTIVE_FILE, sorted(ACTIVE_URLS))
    with VERIFIED_LOCK: atomic_write_file(VERIFIED_FILE, sorted(VERIFIED_URLS))


def record_seed_attempt(seed: str, is_active: bool):
    if not seed: return
    seed = seed.strip().lower()[:60]
    try:
        c = db()
        c.execute("INSERT INTO seed_stats(seed, attempts, active) VALUES(?, 1, ?) "
                  "ON CONFLICT(seed) DO UPDATE SET "
                  "attempts = attempts + 1, active = active + ?, "
                  "last_hit_at = CASE WHEN ? = 1 THEN ? ELSE last_hit_at END",
                  (seed, 1 if is_active else 0, 1 if is_active else 0,
                   1 if is_active else 0, now()))
        c.close()
    except Exception: pass


# ═══════════════════════════════════════════════════════════════
#  CANONICALIZATION
# ═══════════════════════════════════════════════════════════════
def validate_project_id(pid: str) -> bool:
    if not pid or not isinstance(pid, str): return False
    pid = pid.strip().lower()
    if len(pid) < 6 or len(pid) > 30: return False
    if not pid[0].isalpha() or not pid[0].islower(): return False
    if pid.endswith("-") or "--" in pid: return False
    return bool(PROJECT_ID_RE.match(pid))


def canonical_host(host: str):
    if not host: return None
    host = host.lower().rstrip(".")
    if RE_LEGACY_HOST.match(host): return host
    if RE_REGIONAL_HOST.match(host): return host
    return None


def host_to_project(host: str):
    host = host.lower().rstrip(".")
    if host.endswith(".firebaseio.com"):
        base = host[:-len(".firebaseio.com")]
        if base.endswith("-default-rtdb"):
            base = base[:-len("-default-rtdb")]
        return base if validate_project_id(base) else None
    m = re.match(r"^(.+)\.([a-z0-9-]+)\.firebasedatabase\.app$", host)
    if m:
        base = m.group(1)
        if base.endswith("-default-rtdb"):
            base = base[:-len("-default-rtdb")]
        return base if validate_project_id(base) else None
    return None


def canonical_url(raw: str):
    if not raw: return None
    raw = raw.strip()
    if not raw or raw.startswith("#"): return None
    if not re.match(r"^https?://", raw, re.I):
        raw = "https://" + raw
    raw = re.sub(r"^http://", "https://", raw, flags=re.I)
    try:
        u = urlparse(raw)
    except Exception:
        return None
    if u.username or u.password: return None
    canon = canonical_host(u.hostname or "")
    if not canon: return None
    return f"https://{canon}"


# ═══════════════════════════════════════════════════════════════
#  GENERATORS
# ═══════════════════════════════════════════════════════════════
def _hex5() -> str:
    return "".join(random.choices(HEX5, k=5))


def _num_tail() -> str:
    r = random.random()
    if r < 0.4: return f"{random.randint(0, 99):02d}"
    if r < 0.75: return str(random.randint(100, 9999))
    return str(random.randint(10000, 999999))


def _keyboard_mash() -> str:
    r = random.random()
    if r < 0.35:
        c = random.choice("abcdefghijklmnopqrstuvwxyz")
        return c * random.randint(4, 12)
    if r < 0.70:
        row = random.choice(KEYBOARD_ROWS)
        return "".join(random.choices(row, k=random.randint(5, 12)))
    return "".join(random.choices(KEYBOARD_ALL, k=random.randint(6, 15)))


def _leetspeak(word: str) -> str:
    return word.translate(LEET_MAP)


def _drop_vowels(word: str) -> str:
    if len(word) <= 4: return word
    return word[0] + "".join(c for c in word[1:] if c not in "aeiou")


def _validate(raw: str):
    raw = re.sub(r"[^a-z0-9-]", "", raw.lower())
    raw = re.sub(r"-{2,}", "-", raw).strip("-")
    if not raw or not raw[0].isalpha(): raw = "u" + raw
    if len(raw) < 6 or len(raw) > 30: return None
    return raw if validate_project_id(raw) else None


def _pick_base() -> str:
    r = random.random()
    if r < 0.18: return random.choice(_ALL_NAMES)
    if r < 0.30:
        n = random.choice(_ALL_NAMES)
        if random.random() < 0.5:
            return f"{n}-{random.choice(SURNAMES)}"
        w = random.choice(ENGLISH + RELATIONAL)
        return f"{n}{random.choice(['-', ''])}{w}"
    if r < 0.46:
        sector = random.choice(_SECTOR)
        style = random.random()
        if style < 0.35: return f"{sector}-{random.choice(MODIFIERS)}"
        if style < 0.60: return f"{random.choice(MODIFIERS)}-{sector}"
        if style < 0.75: return f"new-{sector}"
        if style < 0.88: return f"{sector}-{random.choice(['india', 'in', 'hq', 'pro', 'official'])}"
        other = random.choice(_SECTOR)
        return f"{sector}-{other}"
    if r < 0.54:
        if random.random() < 0.5:
            return f"{random.choice(MODIFIERS)}-{random.choice(_ALL_NAMES)}"
        return f"{random.choice(_ALL_NAMES)}-{random.choice(MODIFIERS)}"
    if r < 0.60: return random.choice(GAALI)
    if r < 0.66: return random.choice(LOVE)
    if r < 0.70: return random.choice(CELEB)
    if r < 0.72: return f"{random.choice(ENGLISH)}-{random.choice(ENGLISH)}"
    if r < 0.79: return _keyboard_mash()
    if r < 0.88:
        a = random.choice(ENGLISH); b = random.choice(ENGLISH)
        c = random.choice(["app", "hq", "pro", "v1", "v2", "ba1", "app1"])
        return f"{a}-{b}-{c}"
    if r < 0.98 and PLAY_NAMES: return random.choice(PLAY_NAMES)
    return random.choice(FIR_AUTOGEN)


def _apply_suffix(base: str) -> str:
    r = random.random()
    if r < 0.35: return f"{base}-{_hex5()}"
    if r < 0.48: return base
    if r < 0.58: return f"{base}-{random.choice(MODIFIERS)}"
    if r < 0.66: return f"{base}-{_num_tail()}"
    if r < 0.73: return f"{base}-{random.choice(YEARS)}"
    if r < 0.78: return f"{base}-{random.randint(1, 30):02d}"
    if r < 0.83: return f"{base}-{random.choice(MODIFIERS)}-{_hex5()}"
    if r < 0.88: return f"{base}-{random.choice(ENGLISH)}"
    if r < 0.93: return f"{base}-{base}"
    if r < 0.97: return f"{random.choice(MODIFIERS)}-{base}"
    return f"{_leetspeak(base)}-{_hex5()}"


def generate_project_id() -> str:
    for _ in range(40):
        base = _pick_base()
        r = random.random()
        if r < 0.06: base = _leetspeak(base)
        elif r < 0.12: base = _drop_vowels(base)
        if random.random() < 0.08:
            base = base + random.choice("abcdxyz123")
        pid = _validate(_apply_suffix(base))
        if pid: return pid
    return f"user-{_hex5()}"


def build_firebase_url(project_id: str, region=None):
    if not validate_project_id(project_id): return None
    instance = f"{project_id}-default-rtdb"
    if random.random() >= AUTO_REGIONAL_PROB:
        return f"https://{instance}.firebaseio.com"
    reg = region or random.choice(REGIONS)
    return f"https://{instance}.{reg}.firebasedatabase.app"


def sanitize_seed(s):
    s = (s or "").strip().lower()
    s = re.sub(r"[^a-z0-9\-_]", "", s)
    return s[:60]


def _strip_auto_suffix(pid: str) -> str:
    for pat in (r"^(.+)-[0-9a-f]{5}$", r"^(.+)-([0-9]{1,6})$"):
        m = re.match(pat, pid)
        if m and len(m.group(1)) >= 5:
            return m.group(1)
    return pid


def extract_project(url: str) -> str:
    try:
        host = (urlparse(url).hostname or "").lower()
    except Exception:
        return ""
    return host_to_project(host) or ""


def _seed_variants(seed: str) -> list:
    out = set()
    seed = re.sub(r"-{2,}", "-", seed).strip("-").lower()
    if validate_project_id(seed): out.add(seed)
    base = _strip_auto_suffix(seed)
    if base != seed and validate_project_id(base): out.add(base)
    for _ in range(5):
        v = _validate(f"{base}-{_hex5()}")
        if v: out.add(v)
    for _ in range(3):
        v = _validate(f"{base}-{_num_tail()}")
        if v: out.add(v)
    for _ in range(2):
        v = _validate(f"{base}-{random.randint(1, 30):02d}")
        if v: out.add(v)
    for mod in ("admin", "panel", "pannel", "penal", "official", "new", "pro"):
        for cand in (f"{base}-{mod}", f"{mod}-{base}", f"{base}-{mod}-{_hex5()}"):
            v = _validate(cand)
            if v: out.add(v)
    for _ in range(4):
        sector = random.choice(_SECTOR)
        for cand in (f"{base}-{sector}", f"{sector}-{base}"):
            v = _validate(cand)
            if v: out.add(v)
    for y in random.sample(YEARS, k=2):
        v = _validate(f"{base}-{y}")
        if v: out.add(v)
    for _ in range(2):
        w = random.choice(RELATIONAL + ENGLISH)
        for cand in (f"{base}-{w}", f"{w}-{base}"):
            v = _validate(cand)
            if v: out.add(v)
    ls = _validate(_leetspeak(base))
    if ls: out.add(ls)
    for _ in range(2):
        v = _validate(f"{base}{random.randint(1, 999)}")
        if v: out.add(v)
    return list(out)


def generate_random_batch(job_id, batch_size):
    try:
        c = db()
        existing = {r["url"] for r in c.execute(
            "SELECT url FROM items WHERE job_id=?", (job_id,)).fetchall()}
        c.close()
        new_items, attempts = [], 0
        max_attempts = batch_size * 20
        while len(new_items) < batch_size and attempts < max_attempts:
            attempts += 1
            pid = generate_project_id()
            if not pid: continue
            url = build_firebase_url(pid)
            if not url or url in existing: continue
            existing.add(url)
            new_items.append((job_id, url))
        if new_items:
            c = db()
            c.executemany("INSERT INTO items(job_id,url) VALUES(?,?)", new_items)
            c.execute("UPDATE jobs SET total=total+?, updated_at=? WHERE id=?",
                      (len(new_items), now(), job_id))
            c.close()
        return len(new_items)
    except Exception as e:
        log(f"generate_random_batch error: {e}")
        return 0


def generate_auto_batch(job_id, seeds, batch_size):
    try:
        c = db()
        existing = {r["url"] for r in c.execute(
            "SELECT url FROM items WHERE job_id=?", (job_id,)).fetchall()}
        active_projects = []
        if AUTO_EXPAND:
            for r in c.execute(
                "SELECT url FROM items WHERE job_id=? AND status='active' LIMIT 500",
                (job_id,)).fetchall():
                p = extract_project(r["url"])
                if p and p not in active_projects:
                    active_projects.append(p)
        c.close()
        pool = list(seeds) + active_projects
        if not pool: return 0
        weighted = list(seeds) + active_projects * 3
        new_items, attempts = [], 0
        max_attempts = batch_size * 20
        while len(new_items) < batch_size and attempts < max_attempts:
            attempts += 1
            base = random.choice(weighted)
            variants = _seed_variants(base)
            random.shuffle(variants)
            for m in variants:
                url = build_firebase_url(m)
                if not url or url in existing: continue
                existing.add(url)
                new_items.append((job_id, url))
                if len(new_items) >= batch_size: break
            if len(new_items) >= batch_size: break
        if new_items:
            c = db()
            c.executemany("INSERT INTO items(job_id,url) VALUES(?,?)", new_items)
            c.execute("UPDATE jobs SET total=total+?, updated_at=? WHERE id=?",
                      (len(new_items), now(), job_id))
            c.close()
        return len(new_items)
    except Exception as e:
        log(f"generate_auto_batch error: {e}")
        return 0


# ═══════════════════════════════════════════════════════════════
#  PROBE
# ═══════════════════════════════════════════════════════════════
def _get_conn(host, port):
    cache = getattr(_TLS, "conn", None)
    if cache and cache[0] == (host, port): return cache[1]
    if cache:
        try: cache[1].close()
        except Exception: pass
    conn = http.client.HTTPSConnection(host, port, timeout=TIMEOUT)
    _TLS.conn = ((host, port), conn)
    return conn


def probe(url):
    started = time.monotonic()
    try:
        u = urlparse(url)
        host, port = u.hostname, u.port or 443
        base = u.path or "/"
        if not base.endswith(".json"):
            base = base.rstrip("/") + "/.json" if base != "/" else "/.json"
        q = [(k, v) for k, v in parse_qsl(u.query, keep_blank_values=True)
             if k.lower() not in {"orderby", "limittofirst"}]
        q += [("orderBy", '"$key"'), ("limitToFirst", "1")]
        path = base + "?" + urlencode(q)

        def _do():
            conn = _get_conn(host, port)
            conn.request("GET", path,
                         headers={"Accept": "application/json",
                                  "User-Agent": "FB-Checker/7.0"})
            return conn.getresponse()

        try:
            resp = _do()
        except (http.client.HTTPException, ConnectionError, OSError):
            _TLS.conn = None
            resp = _do()

        code = resp.status
        latency = int((time.monotonic() - started) * 1000)
        if code != 200:
            resp.read(16 * 1024)
            return "inactive", code, f"HTTP {code}", latency

        chunks, total = [], 0
        while total <= MAX_PROBE:
            chunk = resp.read(min(8192, MAX_PROBE + 1 - total))
            if not chunk: break
            chunks.append(chunk); total += len(chunk)
            if total > MAX_PROBE:
                return "response_too_large", code, "Response > 64KB", latency

        body = b"".join(chunks)
        if not body.strip():
            return "invalid_no_data", code, "Empty response", latency
        try:
            parsed = json.loads(body.decode("utf-8", "strict"))
        except Exception:
            return "invalid_no_data", code, "Invalid JSON", latency
        if parsed in (None, "", {}, [], False, 0):
            return "invalid_no_data", code, "No data", latency
        return "active", code, "HTTP 200 + data", latency
    except Exception as e:
        return ("unreachable", None, f"{type(e).__name__}: {str(e)[:150]}",
                int((time.monotonic() - started) * 1000))


def verify_devices(url, timeout=VERIFY_TIMEOUT):
    best = -1
    for key in VERIFY_KEYS:
        endpoint = f"{url.rstrip('/')}/clients.json"
        params = {"auth": key} if key else {}
        try:
            r = requests.get(endpoint, params=params,
                headers={"Accept": "application/json",
                         "User-Agent": "FB-Checker/7.0"},
                timeout=timeout)
            if r.status_code in (401, 403, 404): continue
            r.raise_for_status()
            try: data = r.json()
            except ValueError: continue
            if data is None:
                best = max(best, 0); continue
            if isinstance(data, dict):
                best = max(best, len(data))
                if len(data) > 0: return len(data)
        except Exception:
            continue
    return best


# ═══════════════════════════════════════════════════════════════
#  JOB CONTROL
# ═══════════════════════════════════════════════════════════════
def claim_job():
    c = db()
    try:
        c.execute("BEGIN IMMEDIATE")
        row = c.execute("SELECT id FROM jobs WHERE status='pending' "
                        "ORDER BY id LIMIT 1").fetchone()
        if not row: c.execute("ROLLBACK"); return None
        c.execute("UPDATE jobs SET status='processing', "
                  "started_at=COALESCE(started_at,?), updated_at=? "
                  "WHERE id=? AND status='pending'",
                  (now(), now(), row["id"]))
        if c.total_changes != 1:
            c.execute("ROLLBACK"); return None
        c.execute("COMMIT")
        return row["id"]
    finally:
        c.close()


def claim_item(job_id):
    c = db()
    try:
        c.execute("BEGIN IMMEDIATE")
        row = c.execute("SELECT * FROM items WHERE job_id=? AND status='pending' "
                        "ORDER BY id LIMIT 1", (job_id,)).fetchone()
        if not row: c.execute("ROLLBACK"); return None
        c.execute("UPDATE items SET status='checking' WHERE id=? AND status='pending'",
                  (row["id"],))
        if c.total_changes != 1:
            c.execute("ROLLBACK"); return None
        c.execute("COMMIT")
        return row
    finally:
        c.close()


def save_result(item, result):
    status, code, detail, latency = result
    c = db()
    try:
        c.execute("BEGIN")
        c.execute("UPDATE items SET status=?,http_status=?,error=?,latency_ms=?,"
                  "checked_at=? WHERE id=?",
                  (status, code, detail, latency, now(), item["id"]))
        col = {"active": "active", "inactive": "inactive",
               "invalid_no_data": "no_data", "unreachable": "unreachable",
               "response_too_large": "too_large"}.get(status)
        if col:
            c.execute(f"UPDATE jobs SET processed=processed+1,{col}={col}+1,"
                      f"updated_at=? WHERE id=?", (now(), item["job_id"]))
        c.execute("COMMIT")
    except Exception as e:
        log(f"save_result error: {e}")
    finally:
        c.close()

    project = extract_project(item["url"])
    if project: record_seed_attempt(project, status == "active")

    if status == "active":
        is_new_active = persist_active(item["url"], item["job_id"],
                                       code or 200, latency)
        device_count = verify_devices(item["url"])
        if device_count > 0:
            is_new_verified = persist_verified(item["url"], item["job_id"],
                                               device_count, code or 200, latency)
            if is_new_verified:
                log(f"✅ VERIFIED #{item['job_id']} | {item['url']} | devices={device_count}")
                tg_notify_new_verified(item["url"], device_count, item["job_id"])
        if is_new_active:
            log(f"🎯 ACTIVE #{item['job_id']} | {item['url']}")
    else:
        log(f"JOB #{item['job_id']} → {status.upper()} | {item['url']}")


def finish_if_done(job_id):
    c = db()
    try:
        pending = c.execute(
            "SELECT COUNT(*) n FROM items WHERE job_id=? "
            "AND status IN ('pending','checking')", (job_id,)).fetchone()["n"]
        if pending == 0:
            c.execute("UPDATE jobs SET status='completed',completed_at=?,"
                      "updated_at=? WHERE id=? AND status='processing'",
                      (now(), now(), job_id))
            return True
        return False
    finally:
        c.close()


def find_running_job():
    c = db()
    row = c.execute(
        "SELECT id, job_type FROM jobs WHERE status='processing' "
        "ORDER BY id LIMIT 1").fetchone()
    c.close()
    return dict(row) if row else None


def process_job_tick(job_id, job_type):
    item = claim_item(job_id)
    if item:
        save_result(item, probe(item["url"]))
        return "ok"

    if job_type in ("auto", "auto-random"):
        with GEN_LOCK:
            c = db()
            pending = c.execute("SELECT COUNT(*) n FROM items "
                                "WHERE job_id=? AND status='pending'",
                                (job_id,)).fetchone()["n"]
            job = c.execute("SELECT seeds,total,status,job_type FROM jobs WHERE id=?",
                            (job_id,)).fetchone()
            c.close()

            if not job or job["status"] != "processing": return "stopped"
            if pending > 0: return "wait"
            if job["total"] >= AUTO_MAX_URLS:
                c = db()
                c.execute("UPDATE jobs SET status='completed',completed_at=?,"
                          "updated_at=? WHERE id=?", (now(), now(), job_id))
                c.close()
                return "done"
            jt = job["job_type"] or "auto"
            if jt == "auto-random":
                n = generate_random_batch(job_id, AUTO_BATCH)
                return "ok" if n > 0 else "wait"
            try: seeds = json.loads(job["seeds"] or "[]")
            except Exception: seeds = []
            if not seeds:
                c = db()
                c.execute("UPDATE jobs SET status='completed',completed_at=?,"
                          "updated_at=? WHERE id=?", (now(), now(), job_id))
                c.close(); return "done"
            n = generate_auto_batch(job_id, seeds, AUTO_BATCH)
            return "ok" if n > 0 else "wait"

    if finish_if_done(job_id):
        log(f"✔ JOB #{job_id} COMPLETED")
        save_all_files()
        return "done"
    return "wait"


def worker(n):
    log(f"⚡ worker #{n} ready")
    while not STOP.is_set():
        claim_job()
        running = find_running_job()
        if running:
            try:
                process_job_tick(running["id"], running["job_type"])
            except Exception as e:
                log(f"tick error on job #{running['id']}: {e}")
            time.sleep(0.05)
            continue
        time.sleep(0.3)


# ═══════════════════════════════════════════════════════════════
#  DB READS
# ═══════════════════════════════════════════════════════════════
def get_job_by_token(token):
    c = db()
    job = c.execute("SELECT * FROM jobs WHERE token=?", (token,)).fetchone()
    c.close()
    return dict(job) if job else None


def global_stats():
    c = db()
    jobs = c.execute("SELECT COUNT(*) n FROM jobs").fetchone()["n"]
    items = c.execute(
        "SELECT COUNT(*) total, "
        "SUM(CASE WHEN status='active' THEN 1 ELSE 0 END) active, "
        "SUM(CASE WHEN status='inactive' THEN 1 ELSE 0 END) inactive, "
        "SUM(CASE WHEN status='invalid_no_data' THEN 1 ELSE 0 END) no_data, "
        "SUM(CASE WHEN status='unreachable' THEN 1 ELSE 0 END) unreachable "
        "FROM items").fetchone()
    c.close()
    total = items["total"] or 0
    active = items["active"] or 0
    with ACTIVE_LOCK: a_saved = len(ACTIVE_URLS)
    with VERIFIED_LOCK: v_saved = len(VERIFIED_URLS)
    return {
        "jobs": jobs, "urls_checked": total,
        "active_found": active,
        "inactive_found": items["inactive"] or 0,
        "no_data_found": items["no_data"] or 0,
        "unreachable_found": items["unreachable"] or 0,
        "hit_rate_pct": round(active / total * 100, 2) if total else 0,
        "saved_active": a_saved,
        "saved_verified": v_saved,
        "playstore_names": len(PLAY_NAMES),
    }


# ═══════════════════════════════════════════════════════════════
#  TELEGRAM HELPERS
# ═══════════════════════════════════════════════════════════════
def tg(method: str, **params):
    if not TG_API: return {"ok": False, "description": "no token"}
    try:
        r = requests.post(f"{TG_API}/{method}", json=params, timeout=30)
        return r.json()
    except Exception as e:
        log(f"TG {method} error: {type(e).__name__}: {str(e)[:120]}")
        return {"ok": False, "description": str(e)}


def tg_send(chat_id, text, reply_markup=None):
    kw = dict(chat_id=chat_id, text=text, parse_mode="HTML",
              disable_web_page_preview=True)
    if reply_markup: kw["reply_markup"] = reply_markup
    return tg("sendMessage", **kw)


def tg_edit(chat_id, message_id, text, reply_markup=None):
    kw = dict(chat_id=chat_id, message_id=message_id, text=text,
              parse_mode="HTML", disable_web_page_preview=True)
    if reply_markup: kw["reply_markup"] = reply_markup
    return tg("editMessageText", **kw)


def tg_answer_cb(cb_id, text="", show_alert=False):
    return tg("answerCallbackQuery", callback_query_id=cb_id,
              text=text, show_alert=show_alert)


def tg_send_doc(chat_id, path, caption=""):
    try:
        with open(path, "rb") as f:
            r = requests.post(
                f"{TG_API}/sendDocument",
                files={"document": (os.path.basename(path), f, "text/plain")},
                data={"chat_id": chat_id, "caption": caption, "parse_mode": "HTML"},
                timeout=60)
            return r.json()
    except Exception as e:
        log(f"TG sendDocument error: {e}")
        return {"ok": False}


def tg_get_file_bytes(file_id):
    try:
        r = tg("getFile", file_id=file_id)
        if not r.get("ok"): return None
        fp = r["result"]["file_path"]
        url = f"https://api.telegram.org/file/bot{TELEGRAM_BOT_TOKEN}/{fp}"
        return requests.get(url, timeout=60).content
    except Exception as e:
        log(f"tg_get_file_bytes: {e}")
        return None


def is_allowed(chat_id) -> bool:
    if not TELEGRAM_CHAT_ID: return True
    allowed = [c.strip() for c in TELEGRAM_CHAT_ID.split(",") if c.strip()]
    return str(chat_id) in allowed


def rate_ok(chat_id) -> bool:
    with RATE_LOCK:
        ts = [t for t in USER_RATE.get(chat_id, []) if time.time() - t < RATE_WINDOW]
        if len(ts) >= RATE_LIMIT: return False
        ts.append(time.time()); USER_RATE[chat_id] = ts
        return True


def tg_notify_new_verified(url, device_count, job_id):
    if not TELEGRAM_CHAT_ID: return
    targets = [c.strip() for c in TELEGRAM_CHAT_ID.split(",") if c.strip()]
    text = (
        f"🔥 <b>VERIFIED FIREBASE</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"<code>{esc_html(url)}</code>\n\n"
        f"👥 Devices: <b>{device_count}</b>\n"
        f"🆔 Job: <b>#{job_id}</b>\n"
        f'🔗 <a href="{url}/.json?shallow=true">Open JSON</a>'
    )
    for t in targets[:3]:
        try: tg_send(t, text)
        except Exception: pass


# ═══════════════════════════════════════════════════════════════
#  FORMATTING
# ═══════════════════════════════════════════════════════════════
def fmt_status_emoji(status):
    return {"completed":"✅","processing":"🔄","pending":"⏳",
            "stopped":"⏹","failed":"❌"}.get(status, "❓")


def fmt_job_type_emoji(jt):
    return {"auto":"♻️","auto-random":"🎲"}.get(jt or "manual", "📥")


def fmt_progress_bar(pct, width=16):
    filled = int(width * pct / 100)
    return "█" * filled + "░" * (width - filled)


def format_job_progress(j):
    total = j["total"] or 0
    processed = j["processed"] or 0
    pct = (processed / total * 100) if total else 0
    elapsed = elapsed_seconds(j["started_at"], j["completed_at"])
    jt = j.get("job_type") or "manual"
    return (
        f"{fmt_job_type_emoji(jt)} <b>Job #{j['id']}</b> · <code>{esc_html(jt)}</code>\n"
        f"📁 {esc_html((j['filename'] or '—')[:50])}\n\n"
        f"{fmt_status_emoji(j['status'])} <b>{j['status'].upper()}</b>\n"
        f"<code>{fmt_progress_bar(pct)}</code>\n"
        f"{processed:,}/{total:,} · <b>{pct:.1f}%</b>\n\n"
        f"✅ Active: <b>{j['active'] or 0}</b>  "
        f"❌ Inactive: <b>{j['inactive'] or 0}</b>\n"
        f"◌ No Data: <b>{j['no_data'] or 0}</b>  "
        f"✕ Unreach: <b>{j['unreachable'] or 0}</b>\n\n"
        f"⏱ {human_duration(elapsed)}"
    )


def format_job_summary(j):
    total = j["total"] or 0
    processed = j["processed"] or 0
    elapsed = elapsed_seconds(j["started_at"], j["completed_at"])
    jt = j.get("job_type") or "manual"
    hit = ((j["active"] or 0) / total * 100) if total else 0
    return (
        f"{fmt_status_emoji(j['status'])} <b>Job #{j['id']} — {j['status'].upper()}</b>\n"
        f"{fmt_job_type_emoji(jt)} <code>{esc_html(jt)}</code> · "
        f"📁 {esc_html((j['filename'] or '—')[:50])}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"Total: <b>{total:,}</b>  |  Processed: <b>{processed:,}</b>\n\n"
        f"✅ <b>Active:</b> {j['active'] or 0}\n"
        f"❌ Inactive: {j['inactive'] or 0}\n"
        f"◌ No Data: {j['no_data'] or 0}\n"
        f"✕ Unreach: {j['unreachable'] or 0}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"🎯 Hit rate: <b>{hit:.2f}%</b>\n"
        f"⏱ {human_duration(elapsed)}"
    )


# ═══════════════════════════════════════════════════════════════
#  KEYBOARDS
# ═══════════════════════════════════════════════════════════════
def kb_main():
    return {"inline_keyboard": [
        [{"text": "📥 Bulk Check", "callback_data": "menu:bulk"},
         {"text": "♻️ Auto Mutator", "callback_data": "menu:auto"}],
        [{"text": "🎲 Auto Random", "callback_data": "menu:random"}],
        [{"text": "📋 Recent Jobs", "callback_data": "jobs:page:0"}],
        [{"text": "📊 Stats", "callback_data": "menu:stats"},
         {"text": "❓ Help", "callback_data": "menu:help"}],
        [{"text": "💾 Verified URLs", "callback_data": "dl:verified"},
         {"text": "⚡ Active URLs", "callback_data": "dl:active"}],
    ]}


def kb_cancel():
    return {"inline_keyboard": [[{"text": "❌ Cancel", "callback_data": "menu:main"}]]}


def kb_back():
    return {"inline_keyboard": [[{"text": "🏠 Main Menu", "callback_data": "menu:main"}]]}


def kb_job(token, status):
    buttons = []
    if status in ("processing", "pending"):
        buttons.append([{"text": "🛑 Stop Job", "callback_data": f"job:stop:{token}"}])
    buttons.append([{"text": "🔄 Refresh", "callback_data": f"job:view:{token}"}])
    buttons.append([
        {"text": "⬇ Active .txt", "callback_data": f"job:txt:a:{token}"},
        {"text": "⬇ Results .csv", "callback_data": f"job:txt:r:{token}"},
    ])
    buttons.append([{"text": "🏠 Main Menu", "callback_data": "menu:main"}])
    return {"inline_keyboard": buttons}


# ═══════════════════════════════════════════════════════════════
#  COMMANDS
# ═══════════════════════════════════════════════════════════════
HELP_TEXT = (
    "🔥 <b>Firebase Hunter Bot</b>\n\n"
    "<b>Commands:</b>\n"
    "/start — Main menu\n"
    "/bulk — Paste URLs or send .txt file\n"
    "/auto — Seeds → auto mutator\n"
    "/random — Sector-aware random generation\n"
    "/jobs — Recent jobs\n"
    "/stats — Global stats\n"
    "/verified — Download verified.txt\n"
    "/active — Download active.txt\n"
    "/cancel — Cancel current input\n"
    "/help — This message\n\n"
    "<b>How it works:</b>\n"
    "• <b>Bulk</b>: paste URLs (one per line) or send a .txt file\n"
    "• <b>Auto</b>: send seed words, bot mutates and expands\n"
    "• <b>Random</b>: bot generates URLs autonomously\n\n"
    "<b>Classification:</b>\n"
    "200 + data = ✅ Active\n"
    "200 + null = ◌ No Data\n"
    "401/403/404/5xx = ❌ Inactive\n"
    "timeout/DNS = ✕ Unreachable\n\n"
    "Probes are bounded (limitToFirst=1) — no mass reads."
)


def cmd_start(chat_id):
    with VERIFIED_LOCK: v = len(VERIFIED_URLS)
    with ACTIVE_LOCK: a = len(ACTIVE_URLS)
    text = (
        "🔥 <b>Firebase Hunter Bot</b>\n\n"
        f"💾 Verified: <b>{v}</b>  ⚡ Active: <b>{a}</b>\n"
        f"🏪 Play Store names: <b>{len(PLAY_NAMES):,}</b>\n\n"
        "Choose an action:"
    )
    tg_send(chat_id, text, kb_main())


def cmd_bulk(chat_id):
    USER_STATE[chat_id] = {"action": "urls"}
    tg_send(chat_id,
            "📥 <b>Bulk Check</b>\n\n"
            "Paste Firebase URLs (one per line), or send a .txt file.\n\n"
            "Supported hosts:\n"
            "• <code>*.firebaseio.com</code>\n"
            "• <code>*.&lt;region&gt;.firebasedatabase.app</code>\n\n"
            "Max: 100,000 URLs · 10MB",
            kb_cancel())


def cmd_auto(chat_id):
    USER_STATE[chat_id] = {"action": "seeds"}
    tg_send(chat_id,
            "♻️ <b>Auto Mutator</b>\n\n"
            "Send seed words (comma-separated).\n"
            "Example:\n"
            "<code>rto,pmkisan,sbi,aadhaar,panel,admin</code>\n\n"
            "Bot will generate mutants, check them, and expand from active hits.",
            kb_cancel())


def cmd_random(chat_id):
    token = secrets.token_urlsafe(24)
    filename = f"random-{int(time.time())}"
    c = db()
    cur = c.execute(
        "INSERT INTO jobs(token,filename,total,status,job_type,seeds,chat_id) "
        "VALUES(?,?,?,'pending','auto-random',?,?)",
        (token, filename, 0, json.dumps([]), chat_id))
    jid = cur.lastrowid
    c.close()
    text = (
        f"🎲 <b>Auto-Random job #{jid} started</b>\n\n"
        f"Mode: sector-aware random generation\n"
        f"Cap: <b>{AUTO_MAX_URLS:,}</b> URLs\n"
        f"Workers will grind autonomously."
    )
    r = tg_send(chat_id, text, kb_job(token, "pending"))
    if r.get("ok"):
        ACTIVE_MESSAGES[token] = {"chat_id": chat_id,
                                  "message_id": r["result"]["message_id"],
                                  "last_text": text}
    log(f"🎲 Telegram random job #{jid} by chat {chat_id}")


def cmd_jobs(chat_id, page=0):
    c = db()
    total = c.execute("SELECT COUNT(*) n FROM jobs").fetchone()["n"]
    rows = c.execute(
        "SELECT * FROM jobs ORDER BY id DESC LIMIT 5 OFFSET ?",
        (page * 5,)).fetchall()
    c.close()

    if not rows:
        tg_send(chat_id, "📋 <b>No jobs yet</b>", kb_back())
        return

    total_pages = max(1, (total + 4) // 5)
    lines = [f"📋 <b>Recent Jobs</b> (page {page+1}/{total_pages})\n"]
    for j in rows:
        lines.append(
            f"{fmt_status_emoji(j['status'])}{fmt_job_type_emoji(j['job_type'])} "
            f"<b>#{j['id']}</b> — {esc_html((j['filename'] or '—')[:35])}\n"
            f"   {j['processed']}/{j['total']} · "
            f"✅{j['active']} ❌{j['inactive']} ◌{j['no_data']} ✕{j['unreachable']}"
        )
    buttons = []
    for j in rows:
        buttons.append([{
            "text": f"#{j['id']} {(j['filename'] or '')[:28]}",
            "callback_data": f"job:view:{j['token']}"
        }])
    nav = []
    if page > 0:
        nav.append({"text": "◀ Prev", "callback_data": f"jobs:page:{page-1}"})
    if (page + 1) * 5 < total:
        nav.append({"text": "Next ▶", "callback_data": f"jobs:page:{page+1}"})
    if nav: buttons.append(nav)
    buttons.append([{"text": "🏠 Main Menu", "callback_data": "menu:main"}])
    tg_send(chat_id, "\n".join(lines), {"inline_keyboard": buttons})


def cmd_stats(chat_id):
    s = global_stats()
    text = (
        "📊 <b>Global Stats</b>\n"
        "━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"Jobs: <b>{s['jobs']:,}</b>\n"
        f"URLs checked: <b>{s['urls_checked']:,}</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"✅ Active found: <b>{s['active_found']:,}</b>\n"
        f"❌ Inactive: {s['inactive_found']:,}\n"
        f"◌ No Data: {s['no_data_found']:,}\n"
        f"✕ Unreachable: {s['unreachable_found']:,}\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🎯 Hit rate: <b>{s['hit_rate_pct']}%</b>\n"
        f"💾 Saved active: <b>{s['saved_active']:,}</b>\n"
        f"✨ Verified (with devices): <b>{s['saved_verified']:,}</b>\n"
        f"🏪 Play Store names: <b>{s['playstore_names']:,}</b>"
    )
    tg_send(chat_id, text, kb_back())


def cmd_help(chat_id):
    tg_send(chat_id, HELP_TEXT, kb_back())


def cmd_cancel(chat_id):
    USER_STATE.pop(chat_id, None)
    tg_send(chat_id, "❌ Cancelled.", kb_back())


def cmd_download_verified(chat_id):
    with VERIFIED_LOCK:
        if not VERIFIED_URLS:
            tg_send(chat_id, "💾 <b>No verified URLs yet</b>", kb_back()); return
        urls = sorted(VERIFIED_URLS)
    tmp = DATA / f"verified-{chat_id}-{int(time.time())}.txt"
    tmp.write_text("\n".join(urls) + "\n", encoding="utf-8")
    tg_send_doc(chat_id, str(tmp), f"✅ <b>{len(urls)} verified URLs</b>")
    try: tmp.unlink()
    except Exception: pass


def cmd_download_active(chat_id):
    with ACTIVE_LOCK:
        if not ACTIVE_URLS:
            tg_send(chat_id, "⚡ <b>No active URLs yet</b>", kb_back()); return
        urls = sorted(ACTIVE_URLS)
    tmp = DATA / f"active-{chat_id}-{int(time.time())}.txt"
    tmp.write_text("\n".join(urls) + "\n", encoding="utf-8")
    tg_send_doc(chat_id, str(tmp), f"⚡ <b>{len(urls)} active URLs</b>")
    try: tmp.unlink()
    except Exception: pass


def cmd_view_job(chat_id, token):
    j = get_job_by_token(token)
    if not j:
        tg_send(chat_id, "❌ Job not found.", kb_back()); return
    text = format_job_progress(j) if j["status"] in ("processing", "pending") else format_job_summary(j)
    tg_send(chat_id, text, kb_job(token, j["status"]))


def cmd_stop_job(chat_id, token):
    c = db()
    cur = c.execute(
        "UPDATE jobs SET status='stopped',completed_at=?,updated_at=? "
        "WHERE token=? AND status IN ('processing','pending')",
        (now(), now(), token))
    changed = cur.rowcount
    c.close()
    if not changed:
        tg_send(chat_id, "⚠️ Job is not running.", kb_back()); return
    tg_send(chat_id, "⏹ <b>Job stopped.</b>", kb_back())


def cmd_download_job(chat_id, token, kind, cb_id):
    j = get_job_by_token(token)
    if not j:
        tg_answer_cb(cb_id, "Job not found", True); return
    c = db()
    if kind == "a":
        rows = c.execute(
            "SELECT url FROM items WHERE job_id=? AND status='active' ORDER BY id",
            (j["id"],)).fetchall()
        lines = [r["url"] for r in rows]
        fname = f"active-job-{j['id']}.txt"
        caption = f"⬇ <b>Active URLs</b> — job #{j['id']} ({len(lines)})"
    else:
        rows = c.execute(
            "SELECT url,status,http_status,latency_ms,checked_at "
            "FROM items WHERE job_id=? ORDER BY id", (j["id"],)).fetchall()
        header = "url,status,http_status,latency_ms,checked_at\n"
        lines = [header]
        for r in rows:
            lines.append(",".join(
                f'"{v}"' if v is not None else ""
                for v in (r["url"], r["status"], r["http_status"],
                          r["latency_ms"], r["checked_at"])) + "\n")
        fname = f"results-job-{j['id']}.csv"
        caption = f"⬇ <b>All results</b> — job #{j['id']} ({len(rows)})"
    c.close()

    if kind == "a" and not lines:
        tg_answer_cb(cb_id, "No active URLs in this job", True); return

    tg_answer_cb(cb_id, "Preparing file...")
    tmp = DATA / f"dl-{j['id']}-{kind}-{int(time.time())}-{fname}"
    body = "".join(l if l.endswith("\n") else l + "\n" for l in lines)
    tmp.write_text(body, encoding="utf-8")
    tg_send_doc(chat_id, str(tmp), caption)
    try: tmp.unlink()
    except Exception: pass


# ═══════════════════════════════════════════════════════════════
#  INPUT HANDLERS
# ═══════════════════════════════════════════════════════════════
def normalize(line):
    line = line.strip()
    if not line or line.startswith("#"): return None
    candidate = line.split(",", 1)[0].strip().strip('"').strip("'")
    if candidate.lower() in ("url", "firebase_url", "firebase url"): return None
    return canonical_url(candidate)


def parse_urls(content):
    seen, out = set(), []
    for line in content.splitlines():
        u = normalize(line)
        if u and u not in seen:
            seen.add(u); out.append(u)
            if len(out) >= MAX_URLS: break
    return out


def handle_urls_input(chat_id, msg):
    USER_STATE.pop(chat_id, None)
    doc = msg.get("document")
    text = msg.get("text", "")
    content, filename = "", "pasted-urls.txt"

    if doc:
        fname = doc.get("file_name", "urls.txt")
        mime = doc.get("mime_type", "")
        if not (fname.lower().endswith(".txt") or "text" in mime or
                fname.lower().endswith((".csv", ".log"))):
            tg_send(chat_id, "❌ Please send a .txt file.", kb_cancel())
            return
        raw = tg_get_file_bytes(doc["file_id"])
        if raw is None:
            tg_send(chat_id, "❌ Could not download file.", kb_cancel()); return
        content = raw.decode("utf-8", "ignore")
        filename = fname[:150]
    else:
        content = text

    if not content.strip():
        tg_send(chat_id, "❌ No content received.", kb_cancel()); return
    if len(content.encode("utf-8")) > MAX_BYTES:
        tg_send(chat_id, f"❌ File too large (max {MAX_BYTES//1024//1024}MB)", kb_back())
        return

    urls = parse_urls(content)
    if not urls:
        tg_send(chat_id, "❌ No valid Firebase URLs found.", kb_back()); return

    token = secrets.token_urlsafe(24)
    c = db()
    cur = c.execute(
        "INSERT INTO jobs(token,filename,total,status,job_type,chat_id) "
        "VALUES(?,?,?,'pending','manual',?)",
        (token, filename, len(urls), chat_id))
    jid = cur.lastrowid
    c.executemany("INSERT INTO items(job_id,url) VALUES(?,?)",
                  [(jid, u) for u in urls])
    c.close()

    text = (f"📥 <b>Job #{jid} queued</b>\n"
            f"URLs: <b>{len(urls):,}</b>\n"
            f"📁 {esc_html(filename)}")
    r = tg_send(chat_id, text, kb_job(token, "pending"))
    if r.get("ok"):
        ACTIVE_MESSAGES[token] = {"chat_id": chat_id,
                                  "message_id": r["result"]["message_id"],
                                  "last_text": text}
    log(f"📥 Telegram bulk job #{jid} ({len(urls)} URLs) by chat {chat_id}")


def handle_seeds_input(chat_id, text):
    USER_STATE.pop(chat_id, None)
    seeds, seen = [], set()
    for raw in (text or "").split(","):
        s = sanitize_seed(raw)
        if s and s not in seen:
            seen.add(s); seeds.append(s)
        if len(seeds) >= 500: break
    if not seeds:
        tg_send(chat_id, "❌ No valid seeds.", kb_back()); return

    token = secrets.token_urlsafe(24)
    filename = f"auto-{int(time.time())}"
    c = db()
    cur = c.execute(
        "INSERT INTO jobs(token,filename,total,status,job_type,seeds,chat_id) "
        "VALUES(?,?,?,'pending','auto',?,?)",
        (token, filename, 0, json.dumps(seeds), chat_id))
    jid = cur.lastrowid
    c.close()

    text = (f"♻️ <b>Auto job #{jid} started</b>\n\n"
            f"Seeds: <b>{len(seeds)}</b>\n"
            f"Cap: <b>{AUTO_MAX_URLS:,}</b> URLs\n"
            f"Sample: <code>{esc_html(', '.join(seeds[:6]))}</code>")
    r = tg_send(chat_id, text, kb_job(token, "pending"))
    if r.get("ok"):
        ACTIVE_MESSAGES[token] = {"chat_id": chat_id,
                                  "message_id": r["result"]["message_id"],
                                  "last_text": text}
    log(f"♻️ Telegram auto job #{jid} ({len(seeds)} seeds) by chat {chat_id}")


# ═══════════════════════════════════════════════════════════════
#  UPDATE ROUTER
# ═══════════════════════════════════════════════════════════════
def handle_message(msg):
    chat_id = msg.get("chat", {}).get("id")
    if chat_id is None: return
    if not is_allowed(chat_id):
        tg_send(chat_id, "⛔ Unauthorized."); return

    state = USER_STATE.get(chat_id)
    text = msg.get("text", "").strip()
    doc = msg.get("document")

    if state:
        if text in ("/cancel", "/start"):
            if text == "/start":
                USER_STATE.pop(chat_id, None); cmd_start(chat_id)
            else:
                cmd_cancel(chat_id)
            return
        action = state.get("action")
        if action == "urls":
            if not rate_ok(chat_id):
                tg_send(chat_id, "⏳ Rate limit."); return
            handle_urls_input(chat_id, msg); return
        if action == "seeds":
            if not text:
                tg_send(chat_id, "❌ Send seeds as text.", kb_cancel()); return
            if not rate_ok(chat_id):
                tg_send(chat_id, "⏳ Rate limit."); return
            handle_seeds_input(chat_id, text); return

    if text.startswith("/"):
        cmd = text.split()[0][1:].split("@")[0].lower()
        if cmd == "start": cmd_start(chat_id)
        elif cmd == "bulk": cmd_bulk(chat_id)
        elif cmd == "auto": cmd_auto(chat_id)
        elif cmd == "random":
            if not rate_ok(chat_id):
                tg_send(chat_id, "⏳ Rate limit."); return
            cmd_random(chat_id)
        elif cmd in ("jobs", "list"): cmd_jobs(chat_id, 0)
        elif cmd == "stats": cmd_stats(chat_id)
        elif cmd == "verified": cmd_download_verified(chat_id)
        elif cmd == "active": cmd_download_active(chat_id)
        elif cmd == "cancel": cmd_cancel(chat_id)
        elif cmd == "help": cmd_help(chat_id)
        else: tg_send(chat_id, "Unknown command. Try /help.", kb_back())
        return

    if doc:
        tg_send(chat_id,
                "📎 To upload URLs, use /bulk first, then send the file.",
                kb_back())
        return

    if text:
        tg_send(chat_id, "Use /start to open the menu.", kb_back())


def handle_callback(cq):
    chat_id = cq.get("message", {}).get("chat", {}).get("id")
    if chat_id is None: return
    if not is_allowed(chat_id):
        tg_answer_cb(cq["id"], "Unauthorized"); return

    data = cq.get("data", "")
    parts = data.split(":")
    action = parts[0] if parts else ""

    try:
        if action == "menu":
            sub = parts[1] if len(parts) > 1 else "main"
            tg_answer_cb(cq["id"])
            if sub == "main": cmd_start(chat_id)
            elif sub == "bulk": cmd_bulk(chat_id)
            elif sub == "auto": cmd_auto(chat_id)
            elif sub == "random":
                if not rate_ok(chat_id):
                    tg_send(chat_id, "⏳ Rate limit."); return
                cmd_random(chat_id)
            elif sub == "stats": cmd_stats(chat_id)
            elif sub == "help": cmd_help(chat_id)

        elif action == "jobs":
            page = int(parts[2]) if len(parts) > 2 else 0
            tg_answer_cb(cq["id"])
            cmd_jobs(chat_id, page)

        elif action == "job":
            if len(parts) < 3: return
            sub = parts[1]; token = parts[2]
            if sub == "view":
                tg_answer_cb(cq["id"]); cmd_view_job(chat_id, token)
            elif sub == "stop":
                tg_answer_cb(cq["id"], "Stopping..."); cmd_stop_job(chat_id, token)
            elif sub == "txt" and len(parts) >= 4:
                cmd_download_job(chat_id, token, parts[3], cq["id"])

        elif action == "dl":
            sub = parts[1] if len(parts) > 1 else ""
            tg_answer_cb(cq["id"])
            if sub == "verified": cmd_download_verified(chat_id)
            elif sub == "active": cmd_download_active(chat_id)
    except Exception as e:
        log(f"callback error: {e}")
        try: tg_answer_cb(cq["id"], "Error", True)
        except Exception: pass


# ═══════════════════════════════════════════════════════════════
#  POLLING
# ═══════════════════════════════════════════════════════════════
def poll_updates_forever():
    global UPDATES_OFFSET
    log("📡 Bot polling started")
    while not STOP.is_set():
        try:
            r = requests.get(
                f"{TG_API}/getUpdates",
                params={"offset": UPDATES_OFFSET + 1, "timeout": 25,
                        "allowed_updates": json.dumps(["message", "callback_query"])},
                timeout=35)
            data = r.json()
            if not data.get("ok"):
                log(f"getUpdates not ok: {data.get('description')}")
                time.sleep(3); continue
            for upd in data.get("result", []):
                try:
                    UPDATES_OFFSET = max(UPDATES_OFFSET, upd["update_id"])
                    if "message" in upd:
                        handle_message(upd["message"])
                    elif "callback_query" in upd:
                        handle_callback(upd["callback_query"])
                except Exception as e:
                    log(f"update handler error: {e}")
        except requests.exceptions.ReadTimeout:
            continue
        except Exception as e:
            log(f"poll error: {type(e).__name__}: {str(e)[:100]}")
            time.sleep(3)


def progress_updater():
    log("📈 Progress updater started")
    while not STOP.is_set():
        time.sleep(3)
        for token, info in list(ACTIVE_MESSAGES.items()):
            try:
                j = get_job_by_token(token)
                if not j:
                    ACTIVE_MESSAGES.pop(token, None); continue
                if j["status"] in ("processing", "pending"):
                    text = format_job_progress(j)
                    if text != info.get("last_text"):
                        tg_edit(info["chat_id"], info["message_id"], text,
                                kb_job(token, j["status"]))
                        info["last_text"] = text
                else:
                    text = format_job_summary(j)
                    tg_edit(info["chat_id"], info["message_id"], text,
                            kb_job(token, j["status"]))
                    ACTIVE_MESSAGES.pop(token, None)
            except Exception as e:
                log(f"progress update error: {e}")


def periodic_file_sender():
    if not TELEGRAM_CHAT_ID: return
    log(f"📤 Periodic file sender every {FILE_INTERVAL // 60} min")
    targets = [c.strip() for c in TELEGRAM_CHAT_ID.split(",") if c.strip()]
    next_send = time.time() + FILE_INTERVAL
    while not STOP.is_set():
        wait = next_send - time.time()
        if wait > 0:
            if STOP.wait(min(wait, 5)): return
            continue
        try:
            save_all_files()
            with VERIFIED_LOCK: v = len(VERIFIED_URLS)
            if v > 0 and VERIFIED_FILE.exists():
                for t in targets[:3]:
                    tg_send_doc(t, str(VERIFIED_FILE),
                                f"✅ <b>Verified URLs</b>\nTotal: <b>{v}</b>\n{now()}")
        except Exception as e:
            log(f"periodic_file_sender error: {e}")
        next_send = time.time() + FILE_INTERVAL


# ═══════════════════════════════════════════════════════════════
#  HEALTH SERVER (for Railway web service health checks)
# ═══════════════════════════════════════════════════════════════
class HealthHandler(BaseHTTPRequestHandler):
    def log_message(self, *args): pass
    def do_GET(self):
        body = json.dumps({
            "ok": True, "service": "firebase-hunter-bot",
            "verified": len(VERIFIED_URLS), "active": len(ACTIVE_URLS),
        }).encode()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)
    def do_HEAD(self):
        self.send_response(200); self.end_headers()


def start_health_server():
    port = int(os.getenv("PORT", "8080"))
    try:
        srv = ThreadingHTTPServer(("0.0.0.0", port), HealthHandler)
        threading.Thread(target=srv.serve_forever, daemon=True).start()
        log(f"🏥 Health server on :{port}")
    except Exception as e:
        log(f"health server error: {e}")


# ═══════════════════════════════════════════════════════════════
#  CLI: harvest / verify (unchanged from v6.1, kept for offline use)
# ═══════════════════════════════════════════════════════════════
PS_UA_POOL = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/123.0.0.0 Safari/537.36",
    "Mozilla/5.0 (X11; Linux x86_64; rv:124.0) Gecko/20100101 Firefox/124.0",
]
PS_CATEGORIES = ["APPLICATION", "GAME", "TOOLS", "COMMUNICATION", "SOCIAL",
                 "SHOPPING", "FINANCE", "PRODUCTIVITY", "ENTERTAINMENT",
                 "EDUCATION", "HEALTH_AND_FITNESS", "TRAVEL_AND_LOCAL",
                 "FOOD_AND_DRINK", "PHOTOGRAPHY", "MUSIC_AND_AUDIO",
                 "BUSINESS", "MEDICAL"]
PS_KEYWORDS = ["admin", "panel", "dashboard", "portal", "kisan", "rto",
               "upi", "aadhaar", "sbi", "hdfc", "paytm", "hospital",
               "police", "school", "app", "shop", "chat", "game"]
PS_PKG_RE = re.compile(rb"([a-z][a-z0-9_]{2,30}(?:\.[a-z][a-z0-9_]{2,30}){1,4})")


def ps_fetch(url, timeout=25, retries=2):
    for i in range(retries):
        try:
            req = Request(url, headers={
                "User-Agent": random.choice(PS_UA_POOL),
                "Accept-Language": "en-US,en;q=0.9",
                "Accept-Encoding": "identity",
            })
            with urlopen(req, timeout=timeout) as r:
                return r.read()
        except Exception:
            if i == retries - 1: return None
            time.sleep(1.5)
    return None


def ps_extract(html: bytes) -> set:
    if not html: return set()
    out = set()
    for m in PS_PKG_RE.finditer(html):
        try: pkg = m.group(1).decode("ascii", "ignore").lower()
        except Exception: continue
        parts = pkg.split(".")
        if 2 <= len(parts) <= 5 and all(
                re.fullmatch(r"[a-z][a-z0-9_]*", p) for p in parts):
            if 8 <= len(pkg) <= 60: out.add(pkg)
    return out


def ps_pkg_to_base(pkg):
    parts = [p for p in pkg.split(".") if p]
    junk = {"com", "org", "net", "app", "games", "studio", "labs", "team",
            "android", "free", "pro", "official", "app", "apps", "mobile",
            "inc", "llc", "ltd", "co", "game", "hd", "new", "the", "best"}
    while parts and parts[0] in junk: parts.pop(0)
    while parts and parts[-1] in junk: parts.pop()
    if not parts: return None
    base = max(parts, key=len).lower()
    base = re.sub(r"[^a-z0-9]", "", base)
    if 3 <= len(base) <= 28: return base
    return None


def run_harvest(argv):
    ap = argparse.ArgumentParser(prog="run.py harvest")
    ap.add_argument("--countries", default="IN,US,GB")
    ap.add_argument("--categories", default="")
    ap.add_argument("--search", default="")
    ap.add_argument("--fresh", action="store_true")
    args = ap.parse_args(argv)

    countries = [c.strip().upper() for c in args.countries.split(",") if c.strip()]
    categories = ([c.strip().upper() for c in args.categories.split(",") if c.strip()]
                  or PS_CATEGORIES[:5])
    keywords = ([k.strip() for k in args.search.split(",") if k.strip()]
                or PS_KEYWORDS[:15])

    print(f"Harvesting {len(countries)} countries, {len(categories)} cats, "
          f"{len(keywords)} keywords")
    packages = set()
    for c in countries:
        for cat in categories:
            print(f"  → top {c} {cat}")
            packages |= ps_extract(ps_fetch(
                f"https://play.google.com/store/apps/category/{cat}?hl=en&gl={c}") or b"")
            time.sleep(0.6)
        for kw in keywords:
            print(f"  → search {c} '{kw}'")
            packages |= ps_extract(ps_fetch(
                f"https://play.google.com/store/search?q={quote_plus(kw)}&c=apps&hl=en&gl={c}") or b"")
            time.sleep(0.6)

    base_counts = {}
    for pkg in packages:
        base = ps_pkg_to_base(pkg)
        if base: base_counts[base] = base_counts.get(base, 0) + 1

    final = base_counts if args.fresh else {
        **({} if args.fresh else (json.loads(PLAY_JSON.read_text(encoding="utf-8"))
           if PLAY_JSON.exists() else {})),
        **{k: base_counts.get(k, 0) + ({} if args.fresh else
           (json.loads(PLAY_JSON.read_text(encoding="utf-8")).get(k, 0)
            if PLAY_JSON.exists() else 0))
           for k in base_counts}
    }
    PLAY_JSON.write_text(json.dumps(final, indent=2, sort_keys=True), encoding="utf-8")
    PLAY_TXT.write_text("\n".join(sorted(final)) + "\n", encoding="utf-8")
    print(f"[✓] {len(final):,} base names → {PLAY_JSON}")


def run_verify(argv):
    ap = argparse.ArgumentParser(prog="run.py verify")
    ap.add_argument("n", nargs="?", type=int, default=300)
    ap.add_argument("--workers", type=int, default=48)
    args = ap.parse_args(argv)
    print(f"Verify: N={args.n} workers={args.workers}")
    print("(not implemented in bot-only build — use the bot)")


# ═══════════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════════
def run_bot():
    if not TELEGRAM_BOT_TOKEN:
        print("❌ TELEGRAM_BOT_TOKEN not set")
        sys.exit(1)
    if not TELEGRAM_CHAT_ID:
        print("⚠️  TELEGRAM_CHAT_ID not set — bot is PUBLIC (anyone can use).")
        print("   Set it in Railway env vars to restrict access.")

    init_db()
    load_all_persistent()

    # Startup banner
    with VERIFIED_LOCK: v = len(VERIFIED_URLS)
    with ACTIVE_LOCK: a = len(ACTIVE_URLS)
    log("━" * 60)
    log("🔥 FIREBASE HUNTER BOT v7.0")
    log("━" * 60)
    log(f"⚡ Workers:     {WORKERS}")
    log(f"⏱ Timeout:     {TIMEOUT}s")
    log(f"♻ Auto cap:    {AUTO_MAX_URLS:,}")
    log(f"🏪 Play names:  {len(PLAY_NAMES):,}")
    log(f"💾 Active:      {a:,}")
    log(f"✅ Verified:    {v:,}")
    log(f"🔐 Allowlist:   {'YES' if TELEGRAM_CHAT_ID else 'PUBLIC'}")
    log("━" * 60)

    # Start threads
    start_health_server()
    for i in range(WORKERS):
        threading.Thread(target=worker, args=(i + 1,), daemon=True).start()
    threading.Thread(target=progress_updater, daemon=True).start()
    if TELEGRAM_CHAT_ID:
        threading.Thread(target=periodic_file_sender, daemon=True).start()

    # Notify owner
    if TELEGRAM_CHAT_ID:
        targets = [c.strip() for c in TELEGRAM_CHAT_ID.split(",") if c.strip()]
        for t in targets[:3]:
            try:
                tg_send(t, f"🚀 <b>Bot online</b>\n"
                           f"Workers: {WORKERS} · Verified: {v} · Active: {a}")
            except Exception: pass

    try:
        poll_updates_forever()
    except KeyboardInterrupt:
        log("Shutting down...")
    finally:
        STOP.set()
        save_all_files()
        log("State saved. Bye.")


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "bot"
    if mode in ("harvest", "playstore", "play"):
        run_harvest(sys.argv[2:]); return
    if mode in ("verify", "verify-playstore"):
        run_verify(sys.argv[2:]); return
    run_bot()


if __name__ == "__main__":
    main()
