#!/usr/bin/env python3
"""AniList binge tracker.

Pulls your public AniList list + activity history and finds, per show, the
burst where you actually watched most of it. Catches the "watch ep 1 when it
airs, wait, binge the rest" pattern that start/finish dates can't see, and
flags back-to-back sequel runs that held pace vs. burned out.

Usage:
    python anilist_binge.py USERNAME
    python anilist_binge.py USERNAME --offline      # reuse the cached pull
    python anilist_binge.py USERNAME --romaji       # romaji titles

Stdlib only. Writes binge_<user>.html and caches raw data in
anilist_cache_<user>.json so reruns don't re-hit the API.
"""
import argparse, json, math, re, statistics, sys, time, html, webbrowser
import urllib.request, urllib.error
from collections import defaultdict
from datetime import datetime, timedelta
from pathlib import Path

API = "https://graphql.anilist.co"
REQUEST_PAUSE = 2.1          # AniList sometimes runs at 30 req/min; stay under it
DAY = 86400

# Tunables (plain variables on purpose)
GAP_DAYS = 3                 # a pause longer than this ends a burst
WAIT_DAYS = 14               # an earlier episode this far before the burst = waited for the season
BINGE_COVERAGE = 0.6         # burst must hold this share of the episodes you watched
BINGE_RATE = 2.0             # and run at least this many episodes per day
CHAIN_LINK_DAYS = 3          # next season started within this many days = back to back
STALE_DAYS = 30              # "watching" with no activity this long counts as stalled
TAIL_LINK_DAYS = 30          # a paused/dropped sequel started within this many days still ends the run
MIN_EPISODES = 6             # ignore shorter things for binge ranking

Q_USER = "query($name:String){User(name:$name){id name}}"
Q_LIST = """query($userId:Int){MediaListCollection(userId:$userId,type:ANIME){lists{entries{
  mediaId status progress repeat startedAt{year month day}
  media{id episodes format title{romaji english}}}}}}"""
Q_REL = """query($ids:[Int],$page:Int){Page(page:$page,perPage:50){pageInfo{hasNextPage}
  media(id_in:$ids){id relations{edges{relationType node{id type}}}}}}"""
Q_ACT = """query($userId:Int,$page:Int){Page(page:$page,perPage:50){pageInfo{hasNextPage}
  activities(userId:$userId,type:ANIME_LIST,sort:ID_DESC){
    ... on ListActivity{id status progress createdAt media{id}}}}}"""


# ---------------------------------------------------------------- fetching
def gql(query, variables, tries=6):
    body = json.dumps({"query": query, "variables": variables}).encode()
    for attempt in range(tries):
        req = urllib.request.Request(API, data=body, headers={
            "Content-Type": "application/json", "Accept": "application/json",
            # Cloudflare in front of AniList rejects the stock "Python-urllib" agent with a 403
            "User-Agent": "anilist-binge-tracker/1.1 (personal script; Python urllib)"})
        try:
            with urllib.request.urlopen(req, timeout=30) as r:
                data = json.load(r)
            time.sleep(REQUEST_PAUSE)
            if data.get("errors"):
                raise RuntimeError(data["errors"][0].get("message", data["errors"]))
            return data["data"]
        except urllib.error.HTTPError as e:
            if e.code == 429:
                wait = int(e.headers.get("Retry-After", "60")) + 1
                print(f"  rate limited, waiting {wait}s")
                time.sleep(wait)
                continue
            if e.code == 403:
                detail = e.read().decode("utf-8", "replace")[:400]
                raise SystemExit(f"AniList returned 403 Forbidden. Response body:\n{detail}")
            if e.code == 404:
                raise SystemExit("AniList says that user doesn't exist (or the list is private).")
            if attempt == tries - 1:
                raise
            time.sleep(5 * (attempt + 1))
    raise RuntimeError("AniList kept refusing the request")


def fetch(username):
    user = gql(Q_USER, {"name": username})["User"]
    uid = user["id"]
    print(f"Found {user['name']} (id {uid}). Pulling list...")
    lists = gql(Q_LIST, {"userId": uid})["MediaListCollection"]["lists"]
    entries = {e["mediaId"]: e for l in lists for e in l["entries"]}

    print(f"{len(entries)} list entries. Pulling sequel links...")
    ids = list(entries)
    relations = {}
    for i in range(0, len(ids), 50):
        chunk, page = ids[i:i + 50], 1
        while True:
            p = gql(Q_REL, {"ids": chunk, "page": page})["Page"]
            for m in p["media"]:
                relations[m["id"]] = [e["node"]["id"] for e in m["relations"]["edges"]
                                      if e["relationType"] == "SEQUEL" and e["node"]["type"] == "ANIME"]
            if not p["pageInfo"]["hasNextPage"]:
                break
            page += 1

    print("Pulling activity history (this is the slow part)...")
    acts, page = [], 1
    while True:
        p = gql(Q_ACT, {"userId": uid, "page": page})["Page"]
        acts += [a for a in p["activities"] if a and a.get("media")]
        if page % 10 == 0:
            print(f"  {len(acts)} activities so far")
        if not p["pageInfo"]["hasNextPage"]:
            break
        page += 1
    print(f"{len(acts)} activities total.")
    return {"user": user, "entries": list(entries.values()),
            "relations": {str(k): v for k, v in relations.items()}, "activities": acts,
            "fetched_at": int(time.time())}


# ---------------------------------------------------------------- analysis
PROG = re.compile(r"(\d+)\s*-\s*(\d+)|(\d+)")


def ep_range(progress):
    if not progress:
        return None
    m = PROG.search(progress)
    if not m:
        return None
    if m.group(1):
        return int(m.group(1)), int(m.group(2))
    n = int(m.group(3))
    return n, n


def cal_days(t0, t1):
    return (datetime.fromtimestamp(t1).date() - datetime.fromtimestamp(t0).date()).days + 1


def analyse_show(entry, acts):
    """acts: this show's activities, oldest first."""
    total = entry["media"].get("episodes")
    first_seen = {}                  # episode -> timestamp of first (non-rewatch) log
    per_activity = defaultdict(int)  # activity id -> episodes it contributed
    end_state, end_time = None, None
    for a in acts:
        st = (a.get("status") or "").lower()
        if st.startswith("rewatch"):
            continue
        if st == "watched episode":
            r = ep_range(a.get("progress"))
            if r:
                for ep in range(r[0], r[1] + 1):
                    if ep not in first_seen:
                        first_seen[ep] = a["createdAt"]
                        per_activity[a["id"]] += 1
        elif st == "completed":
            top = total or (max(first_seen) if first_seen else 0)
            for ep in range(1, top + 1):
                if ep not in first_seen:
                    first_seen[ep] = a["createdAt"]
                    per_activity[a["id"]] += 1
            end_state, end_time = "completed", a["createdAt"]
        elif st in ("paused watching", "dropped"):
            end_state, end_time = st, a["createdAt"]

    times = sorted(first_seen.values())
    res = {"title": None, "total": total, "watched": len(times), "times": times,
           "status": entry["status"], "repeat": entry.get("repeat") or 0,
           "format": entry["media"].get("format"),
           "pattern": "no episode history", "burst": None, "first": None, "last": None}
    started = entry.get("startedAt") or {}
    started_ts = None
    if started.get("year"):
        started_ts = int(datetime(started["year"], started.get("month") or 1,
                                  started.get("day") or 1, 12).timestamp())
    # when you got into it: first logged episode, else the list start date, else the pause/drop
    res["anchor"] = times[0] if times else (started_ts or end_time)
    if not times:
        return res
    res["first"], res["last"] = times[0], times[-1]

    bursts, cur = [], [times[0]]
    for t in times[1:]:
        if t - cur[-1] > GAP_DAYS * DAY:
            bursts.append(cur)
            cur = [t]
        else:
            cur.append(t)
    bursts.append(cur)
    main = max(bursts, key=len)
    days = cal_days(main[0], main[-1])
    res["burst"] = {"eps": len(main), "start": main[0], "end": main[-1],
                    "days": days, "rate": len(main) / days}
    res["pace"] = len(times) / cal_days(times[0], times[-1])

    watched = len(times)
    biggest_single = max(per_activity.values()) if per_activity else 0
    if watched < MIN_EPISODES:
        res["pattern"] = "short"
    elif biggest_single >= 0.8 * watched:
        res["pattern"] = "logged in one go"      # bulk update: could be a binge, could be catch-up logging
    elif len(main) >= BINGE_COVERAGE * watched and res["burst"]["rate"] >= BINGE_RATE:
        waited = times[0] <= main[0] - WAIT_DAYS * DAY
        res["pattern"] = "waited, then binged" if waited else "binged"
    else:
        gaps = [(b - a) / DAY for a, b in zip(times, times[1:]) if b - a > DAY / 2]
        med = statistics.median(gaps) if gaps else 0
        res["pattern"] = "weekly" if 5 <= med <= 9 else "spread out"
    return res


def title_of(entry, romaji):
    t = entry["media"]["title"]
    return (t["romaji"] if romaji else (t.get("english") or t["romaji"])) or "?"


def analyse(data, romaji=False):
    by_media = defaultdict(list)
    for a in data["activities"]:
        by_media[a["media"]["id"]].append(a)
    for v in by_media.values():
        v.sort(key=lambda a: (a["createdAt"], a["id"]))

    shows = {}
    for e in data["entries"]:
        s = analyse_show(e, by_media.get(e["mediaId"], []))
        s["title"] = title_of(e, romaji)
        s["id"] = e["mediaId"]
        shows[e["mediaId"]] = s

    # back-to-back sequel chains (movies and specials count: they're sequels too)
    rel = {int(k): v for k, v in data["relations"].items()}
    nxt, has_prev = {}, set()

    def link(window_days, ok, start_of):
        for a, sequels in rel.items():
            sa = shows.get(a)
            if not sa or not sa["last"] or a in nxt:
                continue
            best = None
            for b in sequels:
                sb = shows.get(b)
                if not sb or b in has_prev or not ok(sb) or not start_of(sb):
                    continue
                gap = start_of(sb) - sa["last"]
                if -DAY <= gap <= window_days * DAY and (best is None or gap < best[1]):
                    best = (b, gap)
            if best:
                nxt[a] = best[0]
                has_prev.add(best[0])

    # pass 1: you started the next entry right after finishing this one
    link(CHAIN_LINK_DAYS, lambda sb: True, lambda sb: sb["first"])
    # pass 2: a paused/dropped sequel ends the run even if you took a few weeks to start it
    link(TAIL_LINK_DAYS, lambda sb: sb["status"] in ("PAUSED", "DROPPED"), lambda sb: sb["anchor"])

    def single(s):
        return (s["total"] or s["watched"]) <= 1

    now = data.get("fetched_at", time.time())
    chains = []
    for start in nxt:
        if start in has_prev:
            continue
        chain, cur = [start], start
        while cur in nxt and nxt[cur] not in chain:
            cur = nxt[cur]
            chain.append(cur)
        seasons = [shows[m] for m in chain]
        if len(seasons) < 3 and sum(x["watched"] for x in seasons) < 3:
            continue  # two one-off OVAs on the same day isn't a run
        last = seasons[-1]
        multi = [x for x in seasons if not single(x) and x["burst"]]
        done = [x for x in multi if x["status"] in ("COMPLETED", "REPEATING")]
        if last["status"] in ("PAUSED", "DROPPED") or (
                last["status"] == "CURRENT" and now - (last["last"] or last["anchor"] or 0) > STALE_DAYS * DAY):
            verdict = "burned out"
        elif last["status"] == "CURRENT":
            verdict = "in progress"
        elif len(done) >= 2:
            # compare each season's main burst, so an episode 1 logged years early doesn't skew it
            ratio = done[-1]["burst"]["rate"] / done[0]["burst"]["rate"]
            verdict = "sped up" if ratio >= 1.15 else "held pace" if ratio >= 0.75 else "slowed down"
        elif not multi:
            # film series: judge by the gaps between entries
            starts = [x["anchor"] for x in seasons if x["anchor"]]
            gaps = [(b - a) / DAY for a, b in zip(starts, starts[1:])]
            earlier = statistics.median(gaps[:-1]) if len(gaps) > 1 else None
            verdict = "slowed down" if earlier is not None and gaps[-1] > 2 * max(earlier, 1) else "held pace"
        else:
            verdict = "finished the run"
        begin = seasons[0]["burst"]["start"] if seasons[0]["burst"] else seasons[0]["anchor"]
        end = max((x["last"] or x["anchor"] or begin) for x in seasons)
        chains.append({"seasons": seasons, "verdict": verdict,
                       "eps": sum(x["watched"] for x in seasons), "days": cal_days(begin, end)})
    chains.sort(key=lambda c: -c["eps"])

    acts_times = [a["createdAt"] for a in data["activities"]]
    coverage = {"since": min(acts_times) if acts_times else None,
                "with_history": sum(1 for s in shows.values() if s["times"]),
                "entries": len(shows)}
    return shows, chains, coverage


# ---------------------------------------------------------------- report
def d(t):
    return datetime.fromtimestamp(t).strftime("%b %-d, %Y") if sys.platform != "win32" \
        else datetime.fromtimestamp(t).strftime("%b %#d, %Y")


def strip(s, width=220, h=22):
    """Episode timeline: one tick per episode, burst highlighted."""
    t = s["times"]
    if not t:
        return ""
    t0, t1 = t[0], t[-1]
    span = max(t1 - t0, 1)
    b = s["burst"]
    parts = [f'<svg class="strip" viewBox="0 0 {width} {h}" width="{width}" height="{h}" role="img" '
             f'aria-label="{len(t)} episodes from {d(t0)} to {d(t1)}">',
             f'<line x1="4" x2="{width-4}" y1="{h/2}" y2="{h/2}" class="axis"/>']
    if b and t1 > t0:
        x0 = 4 + (b["start"] - t0) / span * (width - 8)
        x1 = 4 + (b["end"] - t0) / span * (width - 8)
        parts.append(f'<rect x="{x0-3:.1f}" y="2" width="{max(x1-x0, 0)+6:.1f}" height="{h-4}" rx="4" class="burstbg"/>')
    for x in t:
        cx = 4 + (x - t0) / span * (width - 8) if t1 > t0 else width / 2
        inb = b and b["start"] <= x <= b["end"]
        parts.append(f'<line x1="{cx:.1f}" x2="{cx:.1f}" y1="5" y2="{h-5}" class="{"tick in" if inb else "tick"}"/>')
    parts.append("</svg>")
    return "".join(parts)


CSS = """
:root{--bg:#EDEFF5;--panel:#F8F9FC;--ink:#1B1F3B;--muted:#5E637D;--line:#D5D8E4;
--binge:#2F5BEA;--binge-soft:#2F5BEA22;--burn:#B4236B;--hold:#1F7A5C;--slow:#8A6A12;
color-scheme:light;box-sizing:border-box;padding-top:env(safe-area-inset-top,0px)}
@media (prefers-color-scheme:dark){:root{--bg:#12142A;--panel:#1A1D38;--ink:#E6E8F2;--muted:#9EA3C0;
--line:#2E3254;--binge:#7C9BFF;--binge-soft:#7C9BFF2B;--burn:#F06AAE;--hold:#4FD1A1;--slow:#E5B94E;color-scheme:dark}}
*{box-sizing:inherit}
body{margin:0;background:var(--bg);color:var(--ink);font:16px/1.5 "Avenir Next","Segoe UI Variable","Segoe UI",system-ui,sans-serif}
main{max-width:980px;margin:0 auto;padding:40px 20px 80px}
h1{font-size:2.4rem;line-height:1.1;margin:0 0 .4rem;font-weight:700;letter-spacing:-.02em}
h2{font-size:1.35rem;margin:3rem 0 .3rem}
p.lede,p.note{color:var(--muted);max-width:68ch;margin:.2rem 0 1rem}
.wrap{overflow-x:auto;background:var(--panel);border:1px solid var(--line);border-radius:12px}
table{border-collapse:collapse;width:100%;font-size:.94rem}
th,td{padding:.55rem .8rem;text-align:left;border-bottom:1px solid var(--line);vertical-align:middle;white-space:nowrap}
td.t{white-space:normal;min-width:200px}
tr:last-child td{border-bottom:0}
th{font-weight:600;color:var(--muted);cursor:pointer;user-select:none}
th:focus-visible{outline:2px solid var(--binge);outline-offset:-2px}
td.n{font-variant-numeric:tabular-nums;text-align:right}
.strip .axis{stroke:var(--line);stroke-width:1}
.strip .tick{stroke:var(--muted);stroke-width:1.5;opacity:.55}
.strip .tick.in{stroke:var(--binge);opacity:1}
.strip .burstbg{fill:var(--binge-soft)}
.tag{font-weight:600}
.tag.binged,.tag.waited{color:var(--binge)}
.tag.burned{color:var(--burn)}.tag.held,.tag.sped,.tag.finished{color:var(--hold)}.tag.slowed{color:var(--slow)}
.chain{background:var(--panel);border:1px solid var(--line);border-radius:12px;padding:1rem 1.1rem;margin:.8rem 0}
.chain h3{margin:0 0 .4rem;font-size:1.05rem}
.chain ol{margin:.3rem 0 0;padding-left:1.3rem;color:var(--muted)}
.chain li span{color:var(--ink)}
"""

JS = """
document.querySelectorAll('table').forEach(t=>{t.querySelectorAll('th').forEach((th,i)=>{
th.tabIndex=0;const go=()=>{const tb=t.tBodies[0],rows=[...tb.rows],asc=th.dataset.asc!=='1';
th.dataset.asc=asc?'1':'0';rows.sort((a,b)=>{const x=a.cells[i].dataset.v??a.cells[i].textContent,
y=b.cells[i].dataset.v??b.cells[i].textContent,nx=parseFloat(x),ny=parseFloat(y);
const c=(!isNaN(nx)&&!isNaN(ny))?nx-ny:x.localeCompare(y);return asc?c:-c});rows.forEach(r=>tb.appendChild(r))};
th.onclick=go;th.onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();go()}}})});
"""


def report(user, shows, chains, cov):
    e = html.escape
    ranked = [s for s in shows.values() if s["pattern"] in ("binged", "waited, then binged")]
    ranked.sort(key=lambda s: (-s["burst"]["eps"] * math.sqrt(s["burst"]["rate"])))
    bulk = [s for s in shows.values() if s["pattern"] == "logged in one go"]
    rewatched = sorted([s for s in shows.values() if s["repeat"] > 0 or s["status"] == "REPEATING"],
                       key=lambda s: -s["repeat"])

    def row(s):
        b = s["burst"]
        cls = "waited" if s["pattern"].startswith("waited") else "binged"
        return (f'<tr><td class="t">{e(s["title"])}</td><td>{strip(s)}</td>'
                f'<td class="n" data-v="{b["eps"]}">{b["eps"]}/{s["total"] or "?"}</td>'
                f'<td class="n" data-v="{b["days"]}">{b["days"]}</td>'
                f'<td class="n" data-v="{b["rate"]:.3f}">{b["rate"]:.1f}</td>'
                f'<td data-v="{b["start"]}">{d(b["start"])}</td>'
                f'<td><span class="tag {cls}">{e(s["pattern"])}</span></td></tr>')

    out = [f'<!doctype html><html lang="en"><head><meta charset="utf-8">'
           f'<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">'
           f'<title>Binge report for {e(user)}</title><style>{CSS}</style></head><body><main>',
           f'<h1>What {e(user)} actually binged</h1>',
           f'<p class="lede">Each show is judged by its biggest burst of episodes, not its start and finish dates, '
           f'so a show you started on air and finished in one weekend still counts. Slow watches never count against a show.</p>']
    if cov["since"]:
        out.append(f'<p class="note">Activity history goes back to {d(cov["since"])} and covers '
                   f'{cov["with_history"]} of {cov["entries"]} list entries. Imports into AniList don\'t create activity, '
                   f'so anything added that way has no episode timing here.</p>')

    out.append('<h2>Binges</h2><p class="note">The shaded part of each strip is the burst; each tick is an episode. '
               'Click a column to sort.</p><div class="wrap"><table><thead><tr><th>Show</th><th>Timeline</th>'
               '<th>Burst eps</th><th>Days</th><th>Eps/day</th><th>Burst began</th><th>Pattern</th></tr></thead><tbody>')
    out += [row(s) for s in ranked] or ['<tr><td colspan="7">No binges found yet.</td></tr>']
    out.append('</tbody></table></div>')

    out.append('<h2>Back-to-back runs</h2><p class="note">Seasons where you started the next one within '
               f'{CHAIN_LINK_DAYS} days of finishing the last. How the run ends matters more than how long it is.</p>')
    if not chains:
        out.append('<p class="note">None found.</p>')
    for c in chains:
        v = c["verdict"]
        out.append(f'<div class="chain"><h3>{e(c["seasons"][0]["title"])}: {c["eps"]} episodes over {c["days"]} days, '
                   f'<span class="tag {v.split()[0]}">{e(v)}</span></h3><ol>')
        for s in c["seasons"]:
            st = e(s["status"].lower())
            b = s["burst"]
            if not s["times"]:
                detail = f"no episode history, {st}"
            elif (s["total"] or s["watched"]) <= 1:
                detail = f"watched {d(s['last'])}"
            elif b["eps"] == s["watched"]:
                detail = f"{s['watched']} eps in {b['days']} days ({b['rate']:.1f}/day), {st}"
            else:
                detail = (f"{s['watched']} eps, main burst {b['eps']} in {b['days']} days "
                          f"({b['rate']:.1f}/day), {st}")
            out.append(f'<li><span>{e(s["title"])}</span>: {detail}</li>')
        out.append('</ol></div>')

    if rewatched:
        out.append('<h2>Rewatched</h2><div class="wrap"><table><thead><tr><th>Show</th><th>Rewatches</th></tr></thead><tbody>')
        out += [f'<tr><td class="t">{e(s["title"])}</td><td class="n" data-v="{s["repeat"]}">'
                f'{s["repeat"] or "in progress"}</td></tr>' for s in rewatched]
        out.append('</tbody></table></div>')

    if bulk:
        out.append('<h2>Logged in one update</h2><p class="note">Most of these episodes were logged at once, '
                   'so there\'s no way to tell a real binge from catching up on your list.</p>'
                   '<div class="wrap"><table><thead><tr><th>Show</th><th>Episodes</th><th>Logged</th></tr></thead><tbody>')
        out += [f'<tr><td class="t">{e(s["title"])}</td><td class="n">{s["watched"]}</td>'
                f'<td data-v="{s["last"]}">{d(s["last"])}</td></tr>' for s in bulk]
        out.append('</tbody></table></div>')

    out.append(f'<script>{JS}</script></main></body></html>')
    return "".join(out)


# ---------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("username")
    ap.add_argument("--offline", action="store_true", help="use the cached pull instead of the API")
    ap.add_argument("--romaji", action="store_true", help="romaji titles instead of English")
    ap.add_argument("--out", help="output HTML path")
    ap.add_argument("--no-open", action="store_true", help="don't open the report in a browser")
    a = ap.parse_args()

    cache = Path(f"anilist_cache_{a.username}.json")
    if a.offline:
        if not cache.exists():
            raise SystemExit(f"No cache at {cache}. Run once without --offline first.")
        data = json.loads(cache.read_text(encoding="utf-8"))
    else:
        data = fetch(a.username)
        cache.write_text(json.dumps(data), encoding="utf-8")

    shows, chains, cov = analyse(data, a.romaji)
    out = Path(a.out or f"binge_{a.username}.html")
    out.write_text(report(data["user"]["name"], shows, chains, cov), encoding="utf-8")
    print(f"Wrote {out.resolve()}")
    if not a.no_open:
        webbrowser.open(out.resolve().as_uri())


if __name__ == "__main__":
    main()
