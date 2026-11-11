"""Hämtar data från fisdetektorn, sparar ett arkiv och bygger en webbsida med grafer.

Användning:
    python tools/fisrapport.py              # hämta en gång, bygg sidan och öppna den
    python tools/fisrapport.py --watch      # i bilen: ligg kvar, uppdatera och ladda upp
    python tools/fisrapport.py --offline    # bygg sidan från arkivet, utan kortet
    python tools/fisrapport.py --port COM5  # annars hittas kortet automatiskt
    python tools/fisrapport.py --watch --serve 8080      # + webbsidan på hemnätverket
    python tools/fisrapport.py --watch --auto-update     # + ny firmware när git har ny kod

--serve visar rapport/index.html på http://<datorns-ip>:8080 för alla på
samma nätverk. --auto-update kollar var 10:e minut om git-repot har nya
commits; i så fall hämtas de och tools/bygg.py --upload körs (med
säkerhetskopia av statistiken före och återställning efter).
"Ladda upp nu" i detektorns inställningar laddar upp direkt och svarar på
skärmen.

Allt hamnar i mappen rapport/ bredvid tools/:
    arkiv.json    alla fisar som någonsin hämtats (kortet minns bara de 100 senaste),
                  med varje fis gaskurva
    fisar.csv     samma sak som tabell
    luft.json     luftloggen: luften en gång i timmen (kortet minns 60 dygn; äldre
                  firmware var 5:e minut)
    luft.csv      samma sak som tabell
    index.html    webbsidan, med datan inbakad (fungerar även utan server)

Ingenting tas bort ur arkivet eller luftloggen: nya data läggs till, och en
kurva byts bara mot en med minst lika hög upplösning.

Fisdatabasen (valfri): fisar som skannats in med mobilen (QR-koder på
detektorns skärm, "Skanna detektorn" på webbsidan) eller hämtats över USB
direkt i webbläsaren ("Hämta från enhet", med kurvor) sparas i en Firebase
Realtime Database. Adressen står i tools/fisdatabas.json (i git), eller i
rapport/fisdatabas.json som går före:
    {"url": "https://fisdata-1234-default-rtdb.europe-west1.firebasedatabase.app"}
Skriptet hämtar därifrån fisar som saknas i arkivet, och webbsidan får
adressen så att den kan läsa och skriva. Se README för reglerna.

Uppladdning (valfritt) styrs av rapport/uppladdning.json. Firebase Hosting:
    {"firebase": {"site": "fisdata-1234", "keyfile": "firebase-nyckel.json"}}
där keyfile är servicekontots nyckel (sökväg relativt rapport/). Sidan finns
sedan på https://fisdata-1234.web.app. Kräver pip install google-auth requests.
Eller GitHub Pages via git över SSH (deploy key, se README):
    {"gitpages": {"remote": "git@github-fisdata:användare/fisdata.git", "branch": "main"}}
Eller GitHub via API-token:
    {"github": {"repo": "användare/fisdata", "branch": "main", "token": "github_pat_..."}}
index.html och arkiv.json laddas upp efter varje uppdatering. Utan internet
köas uppladdningen tills nätet är tillbaka.

Vid anslutning ställer skriptet kortets klocka från datorn, så att fisarna får
rätt tid även utan RTC-modul.

Kräver pyserial (pip install pyserial).
"""

import argparse
import base64
import csv
import gzip
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request
import webbrowser
from datetime import datetime, timedelta
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TEMPLATE = Path(__file__).resolve().parent / "fisrapport_mall.html"
DEVICE_EPOCH = datetime(2000, 1, 1)   # kortets tid: sekunder sedan dess, lokal tid
TYPE_NAMES = ["Smygaren", "Tyst men dödlig", "Knallaren", "Kemvapnet"]

FETCH_EVERY = 10 * 60      # s, hämta även utan nya fisar
RETRY_UPLOAD_EVERY = 60    # s, nytt uppladdningsförsök när nätet saknas
TRIGGERS = ("🏁", "ångrad", "👤", "nollställd", "SYSTEM REDO", "📣")
UPDATE_EVERY = 10 * 60     # s, kolla git efter ny firmware (--auto-update)
CLOCK_EVERY = 60 * 60      # s, synka kortets klocka mot datorns (som går efter internet)


def log(msg):
    print(f"{datetime.now():%H:%M:%S} {msg}", flush=True)


# ---------- KORTET ----------
SEEED_VID = 0x2886   # Seeed Studio (XIAO)


def find_port(name):
    """Porten från --port, annars den första med Seeeds USB-id."""
    if name != "auto":
        return name
    from serial.tools import list_ports
    for p in list_ports.comports():
        if p.vid == SEEED_VID:
            return p.device
    raise OSError("hittar inget XIAO-kort på USB")


def open_port(name):
    import serial
    port = serial.Serial(find_port(name), 115200, timeout=0.5)
    port.dtr = True
    time.sleep(0.5)
    return port


def readline(port):
    return port.readline().decode("utf-8", errors="replace").strip()


def set_clock(port):
    port.write(f"D{datetime.now():%Y-%m-%d %H:%M:%S}\n".encode())


def request_json(port, timeout=6):
    """Skickar J och väntar på FISDATA-raden. None om kortet inte svarar
    (t.ex. under uppvärmningen, då lyssnar det inte på kommandon)."""
    port.reset_input_buffer()
    port.write(b"J\n")
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        line = readline(port)
        if line.startswith("FISDATA:"):
            return json.loads(line[len("FISDATA:"):])
    return None


def request_lines(port, command, item, end, timeout=15):
    """Skickar ett kommando och samlar raderna som börjar med item tills
    raden som börjar med end. None om kortet inte svarar klart i tid."""
    port.reset_input_buffer()
    port.write(command.encode() + b"\n")
    items = []
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        line = readline(port)
        if line.startswith(end):
            return items
        if line.startswith(item):
            try:
                items.append(json.loads(line[len(item):]))
            except ValueError:
                return None      # avhuggen rad: försök igen nästa gång
    return None


def request_curves(port):
    """Kurvorna i kortets flash (K), äldst först."""
    return request_lines(port, "K", "FISKURVA:", "FISKURVOR:")


def request_air(port, air_id, after):
    """Luftloggen (B) efter mätpunkt after. Returnerar (huvud, rader) eller None.
    Stämmer inte id:t (ny logg efter uppladdning) skickar kortet allt."""
    port.reset_input_buffer()
    port.write(f"B{air_id} {after}\n".encode())
    head, rows = None, []
    deadline = time.monotonic() + 30
    while time.monotonic() < deadline:
        line = readline(port)
        if line.startswith("FISLUFT.:"):
            return (head, rows) if head else None
        try:
            if line.startswith("FISLUFT:"):
                head = json.loads(line[len("FISLUFT:"):])
            elif line.startswith("FISLUFT+:"):
                rows.extend(json.loads(line[len("FISLUFT+:"):]))
        except ValueError:
            return None
    return None


def fetch_history(port, folder, archive, device):
    """Hämtar kurvor och luftlogg om firmwaren har dem (J har "history").
    Sparar luftloggen direkt; kurvorna läggs i archive. False om något inte
    gick att läsa (då försöker --watch igen nästa gång)."""
    if not device.get("history"):
        return True
    ok = True
    curves = request_curves(port)
    if curves is None:
        log("Kurvorna kunde inte läsas, försöker igen nästa gång")
        ok = False
    else:
        merge_curves(archive, curves)
    air = load_air(folder)
    got = request_air(port, air.get("id", 0), air.get("last", -1))
    if got is None:
        log("Luftloggen kunde inte läsas, försöker igen nästa gång")
        return False
    if merge_air(air, *got):
        save_air(air, folder)
    return ok


# ---------- ARKIVET ----------
def load_archive(folder):
    path = folder / "arkiv.json"
    if path.exists():
        return json.loads(path.read_text(encoding="utf-8"))
    return {"farts": {}, "device": {}, "updated": None}


def merge(archive, device, seen_now=None):
    """Lägger in kortets logg i arkivet. Nyckeln är (epoch, löpnummer):
    epoch byts när statistiken nollställs, så gamla fisar finns kvar."""
    epoch = device["epoch"]
    names = {p["slot"]: p["name"] for p in device.get("players", [])}
    farts = archive["farts"]
    added = 0

    # Ångrade fisar: löpnummer över kortets total finns inte längre
    for key in [k for k, f in farts.items() if f["epoch"] == epoch and f["seq"] > device["total"]]:
        del farts[key]

    for entry in device.get("log", []):
        key = f"{epoch}-{entry['seq']}"
        old = farts.get(key)
        if entry["t"]:
            when = (DEVICE_EPOCH + timedelta(seconds=entry["t"])).isoformat()
        elif old and old.get("time"):
            when = old["time"]            # tid gissad när fisen först sågs
        else:
            when = seen_now.isoformat() if seen_now else None
        fart = {
            "epoch": epoch,
            "seq": entry["seq"],
            "time": when,
            "timeGuessed": not entry["t"] and when is not None,
            "player": names.get(entry["player"]) if entry["player"] >= 0 else None,
            **{k: entry[k] for k in ("score", "points", "peak", "dur", "slope", "type", "richter", "combo", "flags")},
        }
        # Spelarens namn när fisen lades ska stå kvar även om någon byter namn
        if old and old.get("player") and fart["player"]:
            fart["player"] = old["player"]
        if old and old.get("curve"):
            fart["curve"] = old["curve"]
        if old != fart:
            added += old is None
            farts[key] = fart

    # Kurvorna i J: senaste och rekordet (32 punkter), och i äldre firmware de
    # 10 senaste. Spara dem på fisarna i arkivet, så att varje fis behåller sin
    # kurva för alltid. Firmware med "history" har dessutom 100 punkter per
    # kurva i flash, som hämtas med K (fetch_history).
    curves = device.get("curves") or {}
    merge_curves(archive, [dict(c, epoch=epoch) for c in
                           [curves.get("record"), *(curves.get("recent") or []), curves.get("last")] if c])

    archive["device"] = {k: v for k, v in device.items() if k != "log"}
    archive["updated"] = datetime.now().isoformat(timespec="seconds")
    return added


def merge_curves(archive, curves):
    """Lägger kurvor på fisarna. Senaste sist vinner (om en ångrad fis fått
    nytt löpnummer), men en kurva byts aldrig mot en med lägre upplösning."""
    farts = archive["farts"]
    for c in curves:
        fart = farts.get(f"{c.get('epoch')}-{c.get('seq')}")
        pts = c.get("pts") or []
        if not fart or not any(pts):
            continue
        old = fart.get("curve")
        if old and len(old.get("pts") or []) > len(pts):
            continue
        fart["curve"] = {k: c[k] for k in ("dur", "peak", "pts")}


# ---------- LUFTLOGGEN ----------
AIR_COLUMNS = ["id", "idx", "t", "base", "mean", "lo", "hi", "thr", "farts", "flags"]
AIR_BOOT, AIR_NODATA, AIR_FAULT, AIR_SMELL = 1, 2, 4, 8


def load_air(folder):
    path = folder / "luft.json"
    if path.exists():
        return json.loads(path.read_text(encoding="utf-8"))
    return {"columns": AIR_COLUMNS, "every": 300, "id": 0, "last": -1, "rows": []}


def merge_air(air, head, rows):
    """Lägger till nya mätpunkter (kortets rader: idx, t, base, mean, lo, hi,
    thr, fisar, flaggor; värdena i tiondels ADC-steg). Tar aldrig bort något.
    True om något ändrats."""
    air_id = head["id"]
    every = air.setdefault("everyById", {})
    if air.get("id") and str(air["id"]) not in every:
        every[str(air["id"])] = air.get("every", 300)   # äldre logg: dess intervall
    every[str(air_id)] = head.get("every", 300)
    changed = air.get("id") != air_id
    if changed:
        air["id"] = air_id
        air["last"] = -1
    air["every"] = head.get("every", 300)
    # Kortets egna rader går före timmar som kommit via QR (de saknar lägsta och tröskel)
    have = {r[1]: i for i, r in enumerate(air["rows"]) if r[0] == air_id}
    for r in rows:
        i = have.get(r[0])
        if i is None:
            air["rows"].append([air_id, *r])
            changed = True
        elif air["rows"][i][5] is None:
            air["rows"][i] = [air_id, *r]
            changed = True
    if rows:
        air["last"] = max(air["last"], max(r[0] for r in rows))
    return changed


def air_times(air):
    """Tid (kortets sekunder sedan 2000) för varje mätpunkt. Punkter utan tid
    (innan datorn ställde klockan) räknas bakåt från en senare punkt i samma
    start, eftersom de kommer med jämna mellanrum. None = okänd."""
    every_by = air.get("everyById", {})
    rows = air["rows"]
    times = [r[2] or None for r in rows]
    anchor = None                     # (idx, t) för en senare punkt med tid i samma start
    for i in range(len(rows) - 1, -1, -1):
        r = rows[i]
        if i + 1 < len(rows):
            nxt = rows[i + 1]
            if nxt[0] != r[0] or nxt[1] != r[1] + 1 or nxt[9] & AIR_BOOT:
                anchor = None         # ny start eller lucka
        if times[i]:
            anchor = (r[1], times[i])
        elif anchor:
            times[i] = anchor[1] - (anchor[0] - r[1]) * every_by.get(str(r[0]), air.get("every", 300))
    return times


def save_air(air, folder):
    folder.mkdir(parents=True, exist_ok=True)
    # Ordning: äldre loggar (andra id) först i den ordning de kom, sedan den nuvarande
    order = {}
    for r in air["rows"]:
        order.setdefault(r[0], len(order))
    order[air.get("id")] = len(order)
    air["rows"].sort(key=lambda r: (order[r[0]], r[1]))
    (folder / "luft.json").write_text(json.dumps(air, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
    with open(folder / "luft.csv", "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow(["tid", "baslinje", "medel", "lägsta", "högsta", "tröskel", "fisar", "tid gissad", "anmärkning"])
        for r, t in zip(air["rows"], air_times(air)):
            notes = [n for bit, n in ((AIR_BOOT, "start"), (AIR_NODATA, "ingen mätning"),
                                      (AIR_FAULT, "sensorfel"), (AIR_SMELL, "lukt")) if r[9] & bit]
            when = (DEVICE_EPOCH + timedelta(seconds=t)).isoformat() if t else ""
            w.writerow([when, *("" if v is None else str(v / 10).replace(".", ",") for v in r[3:8]), r[8],
                        "ja" if t and not r[2] else "", ", ".join(notes)])


def air_for_page(air, days=7):
    """Senaste veckan i full upplösning och ett dygnsvärde för all tid."""
    known = [(t, r) for t, r in zip(air_times(air), air["rows"]) if t and not r[9] & AIR_NODATA]
    known.sort(key=lambda x: x[0])
    if not known:
        return None

    def to_ms(t):
        return int((DEVICE_EPOCH + timedelta(seconds=t)).timestamp() * 1000)

    start = known[-1][0] - days * 86400
    recent = [[to_ms(t), *r[3:10], r[0], r[1]] for t, r in known if t >= start]
    daily = {}
    for t, r in known:
        d = (DEVICE_EPOCH + timedelta(seconds=t)).date().isoformat()
        x = daily.setdefault(d, [0, 0, 0, 0, 0])   # summa baslinje, antal, högsta, luktperioder, fisar
        x[0] += r[3]
        x[1] += 1
        x[2] = max(x[2], r[6])
        x[3] += bool(r[9] & AIR_SMELL)
        x[4] += r[8]
    return {"every": max(air.get("everyById", {}).values() or [air.get("every", 300)]), "recent": recent,
            "daily": [[d, round(x[0] / x[1]), x[2], x[3], x[4], x[1]] for d, x in sorted(daily.items())]}


# ---------- FISDATABASEN (Firebase, fisar från QR-skanning och webbsidans USB) ----------
def db_url(folder):
    """Fisdatabasens adress: rapport/fisdatabas.json om den finns, annars
    tools/fisdatabas.json (följer med i git, så att alla datorer har den)."""
    path = folder / "fisdatabas.json"
    if not path.exists():
        path = Path(__file__).resolve().parent / "fisdatabas.json"
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8")).get("url", "").rstrip("/") or None
    except ValueError:
        log("rapport/fisdatabas.json går inte att läsa")
        return None


DB_FIELDS = ("epoch", "seq", "time", "timeGuessed", "player", "score", "points", "peak", "dur", "slope",
             "type", "richter", "combo", "flags")


def merge_db(archive, folder):
    """Lägger till fisar från databasen som saknas i arkivet. Skriver aldrig
    över: kortets egen logg är mer komplett (kurvor m.m.) och går före."""
    url = db_url(folder)
    if not url:
        return 0
    try:
        with urllib.request.urlopen(f"{url}/fis/farts.json", timeout=10) as r:
            farts = json.load(r) or {}
        with urllib.request.urlopen(f"{url}/fis/status.json", timeout=10) as r:
            status = json.load(r) or {}
    except (urllib.error.URLError, TimeoutError, OSError, ValueError) as e:
        log(f"Fisdatabasen svarar inte ({e}), försöker igen senare")
        return 0
    dev = archive.get("device") or {}
    # Kortets antal fisar: från kortet, eller från en senare skanning
    total = max([dev.get("total", 0)] + [s.get("total", 0) for s in status.values()
                                         if isinstance(s, dict) and s.get("epoch") == dev.get("epoch")])
    added = 0
    for key, f in farts.items():
        if not isinstance(f, dict) or key in archive["farts"]:
            continue
        try:
            fart = {k: f[k] for k in DB_FIELDS if k in f}
            fart["epoch"], fart["seq"] = int(fart["epoch"]), int(fart["seq"])
        except (KeyError, TypeError, ValueError):
            continue
        if f"{fart['epoch']}-{fart['seq']}" != key:
            continue
        # Firebase sparar inte tomma värden: en okänd fis (player null) eller en fis
        # utan klocka (time null) kommer tillbaka utan fältet
        for k in ("player", "time"):
            fart.setdefault(k, None)
        if any(k not in fart for k in ("type", "richter", "points", "score", "peak", "dur", "slope", "combo", "flags")):
            continue
        # Ångrad på kortet efter skanningen
        if fart["epoch"] == dev.get("epoch") and fart["seq"] > total:
            continue
        fart["via"] = f.get("via") if f.get("via") in ("qr", "usb") else "qr"
        # Kurvan följer med när fisen hämtats över USB på webbsidan
        c = f.get("curve")
        if isinstance(c, dict) and isinstance(c.get("pts"), list) and any(c["pts"]):
            fart["curve"] = {k: c[k] for k in ("dur", "peak", "pts") if k in c}
        archive["farts"][key] = fart
        added += 1
    if added:
        log(f"{added} fisar från fisdatabasen (QR/USB)")
    merge_db_air(url, folder)
    return added


def merge_db_air(url, folder):
    """Timmar ur luftloggen från fisdatabasen läggs i luft.json, om de saknas
    där. Från QR saknas lägsta och tröskel (då ersätter kortets egna rader via
    USB dem senare); från webbsidans USB-hämtning finns allt."""
    try:
        with urllib.request.urlopen(f"{url}/fis/luft.json", timeout=10) as r:
            luft = json.load(r) or {}
    except (urllib.error.URLError, TimeoutError, OSError, ValueError):
        return
    air = load_air(folder)
    have = {(r[0], r[1]) for r in air["rows"]}
    added = 0
    for a in luft.values():
        try:
            key = (int(a["id"]), int(a["idx"]))
            t = int((datetime.fromisoformat(a["time"]) - DEVICE_EPOCH).total_seconds())
            lo, thr = a.get("lo"), a.get("thr")
            row = [*key, t, int(a["base"]), int(a["mean"]), None if lo is None else int(lo), int(a["hi"]),
                   None if thr is None else int(thr),
                   int(a.get("farts", 0)), int(a.get("flags", 0))]
        except (KeyError, TypeError, ValueError):
            continue
        if key in have:
            continue
        air["rows"].append(row)
        air.setdefault("everyById", {}).setdefault(str(key[0]), 3600)
        added += 1
    if added:
        save_air(air, folder)
        log(f"{added} timmar luft från fisdatabasen (QR/USB)")


def sorted_farts(archive):
    return sorted(archive["farts"].values(), key=lambda f: (f["time"] or "", f["epoch"], f["seq"]))


def save_all(archive, folder):
    folder.mkdir(parents=True, exist_ok=True)
    (folder / "arkiv.json").write_text(json.dumps(archive, ensure_ascii=False, indent=1), encoding="utf-8")

    with open(folder / "fisar.csv", "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow(["tid", "spelare", "typ", "richter", "poäng", "death score", "topp %",
                    "längd s", "lutning %/s", "combo", "happy hour", "test"])
        for x in sorted_farts(archive):
            w.writerow([x.get("time") or "", x.get("player") or "Okänd", TYPE_NAMES[x["type"]], x["richter"],
                        x["points"], x["score"], x["peak"], x["dur"], x["slope"], x["combo"],
                        "ja" if x["flags"] & 1 else "", "ja" if x["flags"] & 2 else ""])

    if (folder / "luft.json").exists():
        (folder / "luftsida.json").write_text(json.dumps(page_air(folder), separators=(",", ":")), encoding="utf-8")
    page = build_page(archive, folder=folder)
    (folder / "index.html").write_text(page, encoding="utf-8")
    return folder / "index.html"


def firmware_lists():
    """Nivåer och bossar läses ur firmwaren, så att wikin alltid stämmer.
    Utan firmwaren (sidbyggaren i fisdata-repot) från nivaer.json bredvid skriptet."""
    try:
        src = (ROOT / "mq_detector_xiao" / "fis_game.cpp").read_text(encoding="utf-8")
    except OSError:
        try:
            saved = json.loads((Path(__file__).resolve().parent / "nivaer.json").read_text(encoding="utf-8"))
            return saved.get("levels", []), saved.get("bosses", [])
        except (OSError, ValueError):
            return [], []

    def strings(name):
        m = re.search(name + r"\[[A-Z_]+\]\s*=\s*\{(.*?)\};", src, re.S)
        return re.findall(r'"([^"]*)"', m.group(1)) if m else []

    titles = strings("LEVEL_TITLES")
    levels = [{"title": t, "at": 0 if i == 0 else round(25 * i ** 2.2)} for i, t in enumerate(titles)]
    return levels, strings("BOSS_NAMES")


def page_air(folder):
    """Luftloggen till sidan: från luft.json, eller (där bara sidan finns, t.ex.
    i fisdata-repot) från luftsida.json som publiceras bredvid sidan."""
    if not folder:
        return None
    if (folder / "luft.json").exists():
        return air_for_page(load_air(folder))
    try:
        return json.loads((folder / "luftsida.json").read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None


def build_page(archive, fragment=False, folder=None):
    levels, bosses = firmware_lists()
    air = page_air(folder)
    data = {"updated": archive["updated"], "device": archive["device"], "farts": sorted_farts(archive),
            "levels": levels, "bosses": bosses, "air": air, "db": db_url(folder) if folder else None}
    blob = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")
    body = TEMPLATE.read_text(encoding="utf-8").replace("/*FISDATA*/null", blob)
    if fragment:
        return body
    return ('<!doctype html>\n<html lang="sv">\n<head>\n<meta charset="utf-8">\n'
            '<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">\n'
            '<style>body{margin:0}</style>\n</head>\n<body>\n' + body + "\n</body>\n</html>\n")


# ---------- UPPLADDNING ----------
UPLOAD_FILES = ("index.html", "arkiv.json", "luftsida.json")   # luftsida.json bara om den finns


def upload_names(folder):
    return [n for n in UPLOAD_FILES if (folder / n).exists()]


def upload_configured(folder):
    return (folder / "uppladdning.json").exists()


def upload(folder):
    """Laddar upp enligt rapport/uppladdning.json, om den finns.
    True = klart (eller inget att göra), False = försök igen senare."""
    cfg_path = folder / "uppladdning.json"
    if not cfg_path.exists():
        return True
    cfg = json.loads(cfg_path.read_text(encoding="utf-8"))
    if "firebase" in cfg:
        return upload_firebase(folder, cfg["firebase"])
    if "gitpages" in cfg:
        return upload_gitpages(folder, cfg["gitpages"])
    if "github" in cfg:
        return upload_github(folder, cfg["github"])
    log("uppladdning.json saknar \"firebase\" eller \"github\"")
    return True


def upload_firebase(folder, cfg):
    """Firebase Hosting via REST: ny version, ladda upp gzippade filer som
    saknas, slutför och publicera. Servicekontot behöver rollen
    Firebase Hosting Admin (Firebase-projektets eget adminsdk-konto har den)."""
    try:
        import google.auth.exceptions
        from google.oauth2 import service_account
        from google.auth.transport.requests import AuthorizedSession
        import requests
    except ImportError:
        log("Firebase kräver: pip install google-auth requests")
        return True

    site = cfg["site"]
    keyfile = Path(cfg.get("keyfile", "firebase-nyckel.json"))
    if not keyfile.is_absolute():
        keyfile = folder / keyfile
    api = "https://firebasehosting.googleapis.com/v1beta1"
    try:
        creds = service_account.Credentials.from_service_account_file(
            str(keyfile), scopes=["https://www.googleapis.com/auth/firebase.hosting"])
        http = AuthorizedSession(creds)

        def call(method, url, **kw):
            r = http.request(method, url, timeout=30, **kw)
            if r.status_code >= 400:
                raise PermissionError(f"{r.status_code}: {r.text[:300]}")
            return r.json() if r.content else {}

        # Ingen cache: sidan ska visa senaste datan direkt
        version = call("POST", f"{api}/sites/{site}/versions", json={"config": {
            "headers": [{"glob": "**", "headers": {"Cache-Control": "no-cache"}}]}})["name"]

        blobs = {}
        for name in upload_names(folder):
            data = gzip.compress((folder / name).read_bytes(), mtime=0)
            blobs[hashlib.sha256(data).hexdigest()] = (f"/{name}", data)
        res = call("POST", f"{api}/{version}:populateFiles",
                   json={"files": {path: h for h, (path, _) in blobs.items()}})
        for h in res.get("uploadRequiredHashes", []):
            r = http.post(f"{res['uploadUrl']}/{h}", data=blobs[h][1], timeout=60,
                          headers={"Content-Type": "application/octet-stream"})
            if r.status_code >= 400:
                raise PermissionError(f"{r.status_code}: {r.text[:300]}")

        call("PATCH", f"{api}/{version}?update_mask=status", json={"status": "FINALIZED"})
        call("POST", f"{api}/sites/{site}/releases?versionName={version}", json={})
        log(f"Uppladdat till https://{site}.web.app")
        return True
    except FileNotFoundError:
        log(f"Hittar inte nyckelfilen {keyfile}")
        return True
    except google.auth.exceptions.TransportError as e:
        log(f"Inget internet ({e}), försöker igen senare")
        return False
    except google.auth.exceptions.RefreshError as e:
        log(f"Nyckelfilen godtogs inte ({e}). Ladda ner en ny från Firebase.")
        return True
    except PermissionError as e:
        log(f"Firebase nekade uppladdningen ({e}). Kolla site-namnet och servicekontots roll.")
        return True
    except (requests.exceptions.RequestException, OSError) as e:
        log(f"Inget internet ({e}), försöker igen senare")
        return False
    except Exception as e:   # t.ex. trasig nyckelfil eller tokenfel utan nät
        log(f"Firebase-fel ({e}), försöker igen senare")
        return False


def upload_gitpages(folder, cfg):
    """GitHub Pages: håller en klon i rapport/.pages och pushar sidan dit.
    Klonen följer först med det som finns på GitHub (där bygger GitHub
    Actions också sidan, se tools/publicera_bygg.py). En datacommit överst
    ersätts (amend), så att repot inte växer med en kopia av sidan var tionde
    minut; annat i repot rörs aldrig."""
    clone = folder / ".pages"
    branch = cfg.get("branch", "main")

    def git(*a, check=True):
        r = subprocess.run(["git", "-C", str(clone), *a], capture_output=True, text=True)
        if check and r.returncode != 0:
            raise OSError((r.stderr or r.stdout).strip().splitlines()[-1] if (r.stderr or r.stdout) else "git-fel")
        return r

    try:
        if not (clone / ".git").exists():
            r = subprocess.run(["git", "clone", "--quiet", cfg["remote"], str(clone)], capture_output=True, text=True)
            if r.returncode != 0:
                raise OSError(r.stderr.strip() or "git clone misslyckades")
            git("config", "user.name", "Fisdetektorn")
            git("config", "user.email", "fisdetektorn@localhost")
        git("fetch", "--quiet", "origin")
        if git("rev-parse", "--verify", f"origin/{branch}", check=False).returncode == 0:
            git("reset", "--quiet", "--hard", f"origin/{branch}")
        for name in upload_names(folder):
            (clone / name).write_bytes((folder / name).read_bytes())
        (clone / ".nojekyll").write_text("", encoding="utf-8")
        git("add", "--", *upload_names(folder), ".nojekyll")
        if git("diff", "--cached", "--quiet", check=False).returncode == 0:
            return True
        has_head = git("rev-parse", "--verify", "HEAD", check=False).returncode == 0
        top = git("log", "-1", "--format=%s", check=False).stdout.strip() if has_head else ""
        message = f"Fisdata {datetime.now():%Y-%m-%d %H:%M}"
        if top.startswith("Fisdata "):
            git("commit", "--quiet", "--amend", "-m", message)
            git("push", "--quiet", f"--force-with-lease={branch}:origin/{branch}", "origin", f"HEAD:{branch}")
        else:
            git("commit", "--quiet", "-m", message)
            git("push", "--quiet", "origin", f"HEAD:{branch}")
        log(f"Uppladdat till GitHub Pages ({cfg['remote']})")
        return True
    except OSError as e:
        log(f"GitHub Pages: {e}. Försöker igen senare")
        return False


def upload_github(folder, cfg):
    branch = cfg.get("branch", "main")
    headers = {"Authorization": f"Bearer {cfg['token']}", "Accept": "application/vnd.github+json",
               "User-Agent": "fisrapport"}
    try:
        for name in upload_names(folder):
            url = f"https://api.github.com/repos/{cfg['repo']}/contents/{name}"
            sha = None
            try:
                req = urllib.request.Request(f"{url}?ref={branch}", headers=headers)
                with urllib.request.urlopen(req, timeout=20) as r:
                    sha = json.load(r)["sha"]
            except urllib.error.HTTPError as e:
                if e.code != 404:
                    raise
            body = {"message": f"Fisdata {datetime.now():%Y-%m-%d %H:%M}", "branch": branch,
                    "content": base64.b64encode((folder / name).read_bytes()).decode()}
            if sha:
                body["sha"] = sha
            req = urllib.request.Request(url, data=json.dumps(body).encode(), headers=headers, method="PUT")
            urllib.request.urlopen(req, timeout=30).close()
        log(f"Uppladdat till {cfg['repo']}")
        return True
    except urllib.error.HTTPError as e:
        log(f"Uppladdningen nekades ({e.code}): kolla repo och token i uppladdning.json")
        return e.code < 500   # fel token/repo: vänta på nästa uppdatering, serverfel: försök igen
    except (urllib.error.URLError, TimeoutError, OSError) as e:
        log(f"Inget internet ({e}), försöker igen senare")
        return False


# ---------- LÄGEN ----------
def update(port, folder, live):
    device = request_json(port)
    if device is None:
        return None
    archive = load_archive(folder)
    added = merge(archive, device, seen_now=datetime.now() if live else None)
    fetch_history(port, folder, archive, device)
    merge_db(archive, folder)
    page = save_all(archive, folder)
    log(f"{len(archive['farts'])} fisar i arkivet ({added} nya)")
    return page


def run_once(args, folder):
    port = open_port(args.port)
    try:
        set_clock(port)
        time.sleep(0.3)
        page = None
        for _ in range(3):
            page = update(port, folder, live=False)
            if page:
                break
            log("Kortet svarar inte än (värmer det upp?), väntar 10 s...")
            time.sleep(10)
        if not page:
            sys.exit("Fick ingen data från kortet")
    finally:
        port.close()
    upload(folder)
    if not args.no_browser:
        webbrowser.open(page.as_uri())
    print(page)


def tell(port, text):
    """Visar ett kort meddelande på detektorns skärm."""
    try:
        port.write(f"O{text[:40]}\n".encode())
    except Exception:
        pass


def serve(folder, port_no):
    """Webbsidan på hemnätverket, i en egen tråd."""
    import functools
    import socket
    import threading
    from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer

    # Bara sidan och dess data: aldrig backup/, uppladdning.json eller nycklar
    PUBLIC = {"/": "index.html", "/index.html": "index.html",
              "/arkiv.json": "arkiv.json", "/fisar.csv": "fisar.csv", "/luft.csv": "luft.csv"}

    class Quiet(SimpleHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def send_head(self):
            path = self.path.split("?", 1)[0].split("#", 1)[0]
            if path not in PUBLIC:
                self.send_error(404)
                return None
            self.path = "/" + PUBLIC[path]
            return super().send_head()

        def list_directory(self, path):
            self.send_error(404)
            return None

    folder.mkdir(parents=True, exist_ok=True)
    handler = functools.partial(Quiet, directory=str(folder))
    httpd = ThreadingHTTPServer(("0.0.0.0", port_no), handler)
    threading.Thread(target=httpd.serve_forever, daemon=True).start()
    try:
        ip = socket.gethostbyname(socket.gethostname())
    except OSError:
        ip = "datorns-ip"
    log(f"Webbsidan finns på http://{ip}:{port_no}/ (hemnätverket)")


def git_out(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True).stdout.strip()


def pull_updates():
    """Hämtar nya commits uppströms. Returnerar (hämtade, firmwaren ändrad)."""
    if subprocess.run(["git", "fetch", "--quiet"], cwd=ROOT).returncode != 0:
        return False, False
    if git_out("rev-list", "--count", "HEAD..@{u}") in ("", "0"):
        return False, False
    old = git_out("rev-parse", "HEAD")
    if subprocess.run(["git", "pull", "--ff-only", "--quiet"], cwd=ROOT).returncode != 0:
        return False, False
    changed = git_out("diff", "--name-only", old, "HEAD", "--", "mq_detector_xiao")
    return True, bool(changed)


def restart_self():
    """Startar om skriptet med den nya koden (samma argument)."""
    log("Startar om med den nya koden")
    os.execv(sys.executable, [sys.executable] + sys.argv)


def run_watch(args, folder):
    upload_pending = False
    last_upload_try = 0.0
    next_update_check = time.monotonic() + 60
    if args.serve:
        serve(folder, args.serve)
    while True:
        try:
            port = open_port(args.port)
        except Exception as e:
            log(f"Hittar inte kortet på {args.port} ({e}), försöker igen om 10 s")
            time.sleep(10)
            continue
        log(f"Ansluten till {port.port}")
        need_clock = True
        last_clock = 0.0
        next_fetch = time.monotonic()
        try:
            while True:
                line = readline(port)
                if line:
                    if "SYSTEM REDO" in line:
                        need_clock = True
                    if any(t in line for t in TRIGGERS):
                        next_fetch = min(next_fetch, time.monotonic() + 2)
                    if "FISREQ:UPLOAD" in line:
                        # "Ladda upp nu" från menyn: direkt, och svara på skärmen
                        if update(port, folder, live=True):
                            if not upload_configured(folder):
                                tell(port, "Sidan uppdaterad (ingen webb inställd)")
                            elif upload(folder):
                                tell(port, "Uppladdat!")
                                upload_pending = False
                            else:
                                tell(port, "Inget internet: laddas upp senare")
                                upload_pending = True
                        else:
                            tell(port, "Kunde inte läsa data")
                now = time.monotonic()
                if args.auto_update and now >= next_update_check:
                    next_update_check = now + UPDATE_EVERY
                    pulled, firmware = pull_updates()
                    if pulled:
                        if firmware:
                            # Kurvorna och luftloggen i flash raderas av uppladdningen:
                            # hämta allt först (tools/bygg.py gör det också)
                            update(port, folder, live=True)
                            log("Ny firmware i git: laddar upp")
                            tell(port, "Ny firmware: uppdaterar...")
                            time.sleep(1)
                            port.close()
                            r = subprocess.run([sys.executable, str(ROOT / "tools" / "bygg.py"), "--upload"], cwd=ROOT)
                            log("Firmware uppdaterad" if r.returncode == 0 else "Firmwareuppdateringen misslyckades")
                        else:
                            port.close()
                        restart_self()
                if not need_clock and now - last_clock >= CLOCK_EVERY:
                    set_clock(port)
                    last_clock = now
                    log("Klockan synkad")
                if now >= next_fetch:
                    if need_clock:
                        set_clock(port)
                        last_clock = now
                        time.sleep(0.3)
                    if update(port, folder, live=True):
                        need_clock = False
                        upload_pending = True
                        next_fetch = now + FETCH_EVERY
                    else:
                        next_fetch = now + 15        # värmer upp: försök snart igen
                if upload_pending and now - last_upload_try >= RETRY_UPLOAD_EVERY:
                    last_upload_try = now
                    upload_pending = not upload(folder)
        except Exception as e:   # kortet urkopplat, datorn i viloläge m.m.
            log(f"Tappade kortet ({e}), ansluter igen")
            try:
                port.close()
            except Exception:
                pass
            time.sleep(5)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--port", default="auto", help="t.ex. COM10, annars automatiskt")
    ap.add_argument("--watch", action="store_true", help="ligg kvar och uppdatera vid nya fisar")
    ap.add_argument("--offline", action="store_true", help="bygg sidan från arkivet utan kortet")
    ap.add_argument("--no-browser", action="store_true", help="öppna inte sidan efteråt")
    ap.add_argument("--serve", type=int, nargs="?", const=8080, help="visa sidan på hemnätverket (port, standard 8080)")
    ap.add_argument("--auto-update", action="store_true", help="ladda upp ny firmware när git har nya commits")
    ap.add_argument("--out", type=Path, default=ROOT / "rapport", help="mapp för arkiv och sida")
    ap.add_argument("--import-json", type=Path, help=argparse.SUPPRESS)   # FISDATA-dump, för test
    ap.add_argument("--fragment", type=Path, help=argparse.SUPPRESS)      # sidan utan html-skal
    ap.add_argument("--upload", action="store_true", help="ladda bara upp befintlig sida och arkiv")
    args = ap.parse_args()
    folder = args.out

    if args.upload:
        sys.exit(0 if upload(folder) else 1)

    if args.import_json:
        text = args.import_json.read_text(encoding="utf-8").strip()
        archive = load_archive(folder)
        merge(archive, json.loads(text.split("FISDATA:", 1)[-1]))
        print(save_all(archive, folder))
    elif args.offline:
        archive = load_archive(folder)
        merge_db(archive, folder)
        if not archive["farts"]:
            sys.exit(f"Arkivet i {folder} är tomt")
        archive["updated"] = archive["updated"] or datetime.now().isoformat(timespec="seconds")
        page = save_all(archive, folder)
        if not args.no_browser:
            webbrowser.open(page.as_uri())
        print(page)
    elif args.watch:
        run_watch(args, folder)
    else:
        run_once(args, folder)

    if args.fragment:
        args.fragment.write_text(build_page(load_archive(folder), fragment=True, folder=folder), encoding="utf-8")


if __name__ == "__main__":
    main()
