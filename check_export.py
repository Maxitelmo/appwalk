#!/usr/bin/env python3
"""check-export: compares a WhatsApp walk with the chat's own Export chat, added to the export with `attach`.

On a phone without root, WhatsApp's Export chat is the only second source for what a WhatsApp walk read:
ALEAPP cannot read msgstore.db without root. This reads the chat's text from the attached zip and finds
each of its lines in the walk's transcript, in order, and the other way round: what the transcript has
that the export does not (a voice note written twice, abrignoni/appwalk#39).

For each line of the export:
- a text: is it the text of a message line in the transcript, with the direction its sender gives;
- a voice note (PTT-....opus): is there a voice note line;
- a picture or a video: is there one, and its caption, when it has one; in an album with more files than its
  grid shows, the files the grid does not show are behind its last tile, not missing;
- a deleted message: is there a deleted-message line;
- a link sent on its own: found by its text, or as its preview card when that is all the walk shows of it
  (section 14 of the manual);
- a call, answered or missed, which the export writes as an empty message from the one who called: is there
  a call line;
- system lines (group created, the encryption notice) are listed, not counted.

The export holds the whole chat and a walk may not (--stop-at, or an end not confirmed). The log says
which end of the list the walk did not confirm; export lines past the first or last one found at that
end are "not walked", not "missing".

The check reads the transcript as transcript.build() makes it now, with this AppWalk and this profile,
because transcript.csv has no hash. It compares that with transcript.csv as text: if the file differs,
the same counts are run on the file too. When they agree, that says nothing about what the walk first
wrote: attach writes transcript.csv again with the AppWalk that runs it.

Times are not compared: the export gives "03:28" and a phone in 12 hours shows "3:28 a. m.", and a time
is not needed to find a message. Read from Spanish (es-US) exports from Android only, the ones tried; any
other format or language stops the check and says so. The result is kept out of the hash chain and the
report, in export_check.csv and export_check.txt in the export's main folder (a file in attachments/
would make verify fail).
"""
import csv
import difflib
import hashlib
import io
import json
import os
import re
import sys
import unicodedata
import urllib.parse
import zipfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import transcript  # noqa: E402

WHATSAPP = "com.whatsapp"
CSV_NAME, TXT_NAME, FILE_CSV_NAME = "export_check.csv", "export_check.txt", "export_check_of_transcript_csv.csv"
COLUMNS = ["export_line", "kind", "author", "direction_by_export", "text", "result", "walk_line", "walk_direction",
           "direction_agrees", "screenshot", "note"]

FOUND, MISSING, NOT_WALKED, ONLY_WALK = "found", "missing", "not walked", "only in the walk"
SYSTEM = "system line (not counted)"
LINK_CARD = "found as its preview card: WhatsApp showed the card, not the typed link"
DESCRIBED_ONLY = "only in the walk: a description (a sticker, a GIF) the check does not compare (not counted)"
CARD_LINE = "only in the walk, where the export has a link sent alone: a line of its preview card (not counted)"
OTHER_FILE = "attachment of another kind (not compared)"
ALBUM = "album: the photos and videos after it are its own lines (not counted)"
BEHIND_TILE = "behind the album's last tile: the walk shows the album's first files only (not counted as missing)"
TILE = "the album's last tile, standing for the files it does not show (not counted)"
# The walk shows an album's photos as "Ver foto, 1 de 6" and the export lists their files in an order of its own
# (IMG-…-WA0003, WA0008, WA0004 for photos 1 to 3 of an album of 6, 22 November 2026), so a found or hidden photo
# of an album is one of the album's files, counted, not that file.
ALBUM_NOTE = "matched as one of the album's photos; the walk does not say which file"
NOT_WALKED_NOTE = "past the end of the list the walk did not confirm reaching"
# A photo of an album, and the last tile of an album with more files than its grid shows, as WhatsApp 2.26.45.99
# describes them (es-US).
ALBUM_PHOTO = re.compile(r"Ver foto, (\d+) de (\d+)")
ALBUM_TILE = re.compile(r"Ver los (\d+) archivos multimedia")
# The kinds that are counted, in the order the summary gives them.
KINDS = ["text", "caption", "link", "voice note", "picture", "video", "deleted", "call"]
PLURAL = {"text": "texts", "caption": "captions", "link": "links sent alone", "voice note": "voice notes",
          "picture": "pictures", "video": "videos", "deleted": "deleted messages", "call": "calls"}

# The line that starts a message in an Android export, once odd spaces are plain ones: "14/11/2026, 03:22 - "
# (24 hours, Samsung SM-G990E, es-US) or "14/11/26, 3:22 a. m. - " (12 hours). What follows is "Name: text"
# or, for a line nobody wrote (group created, the encryption notice), the text alone.
START = re.compile(r"^(\d{1,2})/(\d{1,2})/(\d{2,4}),? (\d{1,2}):(\d{2})(?: ?([ap])\.? ?m\.?)? - (.*)$", re.I)
# iOS writes "[14/11/26, 3:22:05 a. m.] Name: text"; not tried, so it is recognised only to say so.
IOS_START = re.compile(r"^\[\d{1,2}/\d{1,2}/\d{2,4},? \d{1,2}:\d{2}:\d{2}")
ATTACHED = re.compile(r"^(\S+\.\w+) \(archivo adjunto\)$")
# A link alone, with or without its scheme ("www.github.com/x"), the scheme in any case (#62, found by testing
# made-up chats).
LINK_ALONE = re.compile(r"^(?:https?://|www\.)\S+$", re.I)
# A deleted message, as the export writes it for the exporting phone's own and for the others', and as a walk
# reads it on either side (moto g47 and Samsung SM-G990E, WhatsApp 2.26.44.90, es-US, 14 November 2026).
DELETED_OWN, DELETED_OTHERS = "Eliminaste este mensaje.", "Se eliminó este mensaje."
SPANISH = ("(archivo adjunto)", DELETED_OWN, DELETED_OTHERS, "<Multimedia omitido>",
           "Los mensajes y las llamadas están cifrados de extremo a extremo", "Creaste este grupo", "te añadió")
ENGLISH = ("(file attached)", "<Media omitted>", "Messages and calls are end-to-end encrypted", "You deleted this message",
           "This message was deleted", "You created group")
# The view ids of WhatsApp's own items in a transcript line (profiles/com.whatsapp.json), whatever the language.
WALK_IDS = {"audio_seekbar": "voice note", "image": "picture", "video_container": "video", "caption": "caption"}


class CheckStopped(Exception):
    """The check cannot be made: the reason is said, and nothing is written."""


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def plain(text):
    """Text as compared: NFC, without the direction marks and joiners WhatsApp puts in, odd spaces made plain
    and runs of space made one. The export starts an attachment line with U+200E; the walk starts the
    encryption notice with U+200C; a moto g47 in 12 hours writes "a. m." with U+202F."""
    t = unicodedata.normalize("NFC", text or "")
    t = re.sub("[\u200b\u200c\u200d\u200e\u200f\u2066-\u2069\ufeff]", "", t)
    t = re.sub(r"[\s\u00a0\u202f\u2007]+", " ", t)
    return t.strip()


# ---- The export ----


def parse_export(text):
    """The lines of an Android Export chat, in order: dicts with n (its line in the .txt), author ("" for a
    system line), kind, text, and file for an attachment. A picture or a video with a caption gives two
    lines, the item and its caption, with the same n. Stops when the format or the language is not one
    that was tried."""
    raw = text.splitlines()
    first = next((x for x in raw if x.strip()), "")
    if IOS_START.match(plain(first)):
        raise CheckStopped("this looks like an export made on an iPhone ([date, time] Name: text); only Android "
                           "exports were tried, so it was not read")
    if not START.match(plain(first)):
        raise CheckStopped(f"the first line of the chat's text is not in a format this check reads: {first[:80]!r}")
    if not any(m in text for m in SPANISH):
        if any(m in text for m in ENGLISH):
            raise CheckStopped("the export is in English; only Spanish (es-US) exports were tried, so it was not read")
        raise CheckStopped("could not tell the export's language: none of the Spanish lines this check knows is in it")
    if "<Multimedia omitido>" in text:
        raise CheckStopped("the export was made without media (<Multimedia omitido>); that kind of export was not "
                           "tried, so it was not read")
    messages = []
    for n, line in enumerate(raw, 1):
        m = START.match(plain(line))
        if m:
            rest = m.group(7)
            author, sep, body = rest.partition(": ")
            if not sep and rest.endswith(":"):
                # A message with nothing after the name: how the export writes a call, answered or missed, from
                # the one who called (Samsung SM-G990E and Xiaomi 22101316G, WhatsApp 2.26.45.99, 21 November
                # 2026: "21/11/2026, 19:28 - Maxi: "). The space after the colon was stripped with the line's end.
                author, sep, body = rest[:-1], ":", ""
            messages.append({"n": n, "author": author.strip() if sep else "", "body": body if sep else rest,
                             "stamp": m.groups()[:6]})
        elif messages:
            messages[-1]["body"] += "\n" + line
    def tidy(msg):
        return "\n".join(x.strip() for x in msg["body"].replace("\u200e", "").split("\n")).strip()

    def is_photo_or_video(msg):
        att = ATTACHED.match(plain(tidy(msg).partition("\n")[0]))
        return bool(att) and att.group(1).upper().startswith(("IMG-", "VID-"))

    def album_files(i):
        """How many photos and videos follow message i from the same sender at the same minute."""
        k = i + 1
        while (k < len(messages) and messages[k]["author"] == messages[i]["author"]
               and messages[k]["stamp"] == messages[i]["stamp"] and is_photo_or_video(messages[k])):
            k += 1
        return k - i - 1

    out = []
    album = None   # [the album's line, its size, how many of its files are still to come]
    for i, msg in enumerate(messages):
        n, author = msg["n"], msg["author"]
        body = tidy(msg)
        if album and album[2] == 0:
            album = None
        if not author:
            out.append({"n": n, "author": "", "kind": "system", "text": plain(body), "file": ""})
            continue
        if not plain(body):
            # An empty message is also how the export starts an album: the photos and videos follow it from the same
            # sender at the same minute (Samsung SM-G990E and Xiaomi 22101316G, 22 November 2026: an album of 3 and
            # one of 6). With none after it, it is a call.
            files = album_files(i)
            if files >= 2:
                out.append({"n": n, "author": author, "kind": "album", "text": f"{files} files", "file": "",
                            "album_size": files})
                album = [n, files, files]
            else:
                out.append({"n": n, "author": author, "kind": "call", "text": "", "file": ""})
            continue
        first_line, _, more = body.partition("\n")
        att = ATTACHED.match(plain(first_line))
        if att:
            name = att.group(1)
            kind = ("voice note" if name.upper().startswith("PTT-") else "picture" if name.upper().startswith("IMG-")
                    else "video" if name.upper().startswith("VID-") else "attachment")
            out.append({"n": n, "author": author, "kind": kind, "text": name, "file": name})
            if album and kind in ("picture", "video"):
                out[-1].update(album=album[0], album_size=album[1])
                album[2] -= 1
            if plain(more):
                out.append({"n": n, "author": author, "kind": "caption", "text": plain(more), "file": ""})
            continue
        if plain(body) in (DELETED_OWN, DELETED_OTHERS):
            out.append({"n": n, "author": author, "kind": "deleted", "text": plain(body), "file": ""})
        elif LINK_ALONE.match(plain(body)):
            out.append({"n": n, "author": author, "kind": "link", "text": plain(body), "file": ""})
        else:
            out.append({"n": n, "author": author, "kind": "text", "text": plain(body), "file": ""})
    return out


# ---- The walk ----


def walk_kind(row):
    """What a transcript line is, for this check: a kind and its direction, or None for a line that is not a
    message (a time, an author's name, a quoted message, a date)."""
    rid = (row.get("resource_id") or "").split(":id/")[-1]
    role, text = row.get("role"), plain(row.get("text"))
    direction = row.get("direction") or ""
    if rid in ("title", "snippet", "url") and role == "other":
        # A link's preview card: its title, snippet and address, which the profile leaves as other text. It counts
        # only as the card of a link the walk has no line for (#62: a real card was never seen).
        return "card", {"right": "sent", "left": "received"}.get(row.get("side") or "", "")
    if rid == "call_log_title":
        # A call is a line of its own in the chat ("Llamada", "Videollamada perdida"), which the profile leaves as
        # other text. Who called is the side it sits on, as for a message.
        return "call", direction or {"right": "sent", "left": "received"}.get(row.get("side") or "", "")
    if role not in ("message", "described"):
        return None
    if text in (DELETED_OWN, DELETED_OTHERS):
        # The walk's own words say whose it was, as on the screen: "Eliminaste" on the phone that deleted it.
        return "deleted", direction or ("sent" if text == DELETED_OWN else "received")
    if rid == "thumb" and role == "described":
        # WhatsApp 2.26.45.99 draws a video and each photo of an album as a view "thumb" (abrignoni/appwalk#61):
        # "Video, HD, duration 5 segundos", "Ver foto, 1 de 3", and for an album with more than the grid shows, a
        # last tile "Ver los 6 archivos multimedia" over the ones it does not show.
        if ALBUM_TILE.fullmatch(text):
            return "album tile", direction
        return ("video" if text.startswith("Video,") else "picture"), direction
    if rid in WALK_IDS and (role == "described" or rid == "caption"):
        return WALK_IDS[rid], direction
    if role == "message":
        return "text", direction
    # A message of one emoji is drawn large and described, not written (the 👍 of the known-data chat). It is a text,
    # counted as one: a large emoji written twice in a walk passed while a text written twice failed (#62). Other
    # descriptions (a sticker, a GIF) stay apart and are not counted. An emoji is known by having no letter: a keycap
    # such as 3️⃣ holds a digit and was taken for a description (#62, found by testing made-up chats).
    if text and not any(unicodedata.category(ch).startswith("L") for ch in text):
        return "text", direction
    return "described", direction


def key(kind, text):
    """What two lines must share to be the same message: the text for text, a caption, a link and a large
    emoji; the kind alone for a voice note, a picture, a video, a deleted message or a call."""
    if kind in ("text", "caption", "link", "described"):
        return ("text", plain(text))
    return (kind,)


def walked_ends(export, item):
    """(oldest_unsure, newest_unsure): which end of the list the walks of this item did not confirm reaching.
    A walk with reveal "above" goes up to the oldest message, after a rewind to the newest; "below" the other
    way. A stop at --stop-at, a cap, or an end not confirmed leaves its end unsure, as does --no-rewind."""
    oldest = newest = False
    seen = False
    start = None
    with open(os.path.join(export, "actions.jsonl"), encoding="utf-8") as f:
        for raw in f:
            r = json.loads(raw)
            if r["action"] not in ("walk_start", "walk_stop"):
                continue
            d = json.loads(r["detail"]) if r.get("detail") else {}
            if (d.get("item") or "") != item:
                continue
            if r["action"] == "walk_start":
                start = d
                continue
            seen = True
            start = start or {}
            walked_to_end = d.get("end_confirmed") is True
            rewound = bool(start.get("rewind", True)) and d.get("rewind_end_confirmed") is True
            if start.get("reveal", "above") == "above":
                oldest, newest = oldest or not walked_to_end, newest or not rewound
            else:
                oldest, newest = oldest or not rewound, newest or not walked_to_end
            start = None
    if not seen:
        return True, True
    return oldest, newest


def line_up(a, b, from_end=False):
    """{index in a: index in b} for the lines two lists share, in order (difflib, without its junk rule: five voice
    notes look alike and must all count). With from_end, lined up from the lists' ends."""
    if from_end:
        back = line_up(a[::-1], b[::-1])
        return {len(a) - 1 - i: len(b) - 1 - j for i, j in back.items()}
    pairs = {}
    for block in difflib.SequenceMatcher(None, a, b, autojunk=False).get_matching_blocks():
        for i in range(block.size):
            pairs[block.a + i] = block.b + i
    return pairs


def line_up_by_direction(a, b, a_dir, b_dir, from_end=False):
    """{index in a: index in b}: the most lines the two lists share in order and, of the ways to line up that many,
    the one with the most lines whose direction agrees (a direction the walk does not give agrees with none). With
    from_end, of the ways that tie, the one nearest the lists' ends.

    Lined up blind to direction, an "ok" of the owner's that the walk lacks took the other side's "ok"; lined up by
    direction first, a line with no direction or the wrong one in the walk left a line the walk has as missing; and
    difflib, which takes the longest run first, let a sticker among repeated texts strand an "ok" at each end (#62,
    found by testing made-up chats). This line-up counts the lines first and the directions only to break ties.

    Lines found once on each side are lined up first, as fixed points (as git's patience diff does), and the
    weighted line-up runs only in the stretches between them: run over a whole chat of 2,000 messages it took
    minutes."""
    if from_end:
        back = line_up_by_direction(a[::-1], b[::-1], a_dir[::-1], b_dir[::-1])
        return {len(a) - 1 - i: len(b) - 1 - j for i, j in back.items()}
    if not a or not b:
        return {}
    count_a, count_b = {}, {}
    for k in a:
        count_a[k] = count_a.get(k, 0) + 1
    for k in b:
        count_b[k] = count_b.get(k, 0) + 1
    where = {k: i for i, k in enumerate(a) if count_a[k] == 1 and count_b.get(k) == 1}
    marks = [(where[k], j) for j, k in enumerate(b) if k in where]
    fixed = longest_rising(marks)
    if not fixed:
        return weighted_line_up(a, b, a_dir, b_dir)
    pairs, (i0, j0) = {}, (-1, -1)
    for i, j in fixed + [(len(a), len(b))]:
        inner = line_up_by_direction(a[i0 + 1:i], b[j0 + 1:j], a_dir[i0 + 1:i], b_dir[j0 + 1:j])
        pairs.update({i0 + 1 + x: j0 + 1 + y for x, y in inner.items()})
        if i < len(a):
            pairs[i] = j
        i0, j0 = i, j
    return pairs


def longest_rising(marks):
    """The longest run of (i, j) pairs, taken in order of j, whose i also rises."""
    import bisect
    tails, prev, at = [], [None] * len(marks), []
    for n, (i, _) in enumerate(marks):
        k = bisect.bisect_left(tails, i)
        if k == len(at):
            at.append(n)
            tails.append(i)
        else:
            at[k] = n
            tails[k] = i
        prev[n] = at[k - 1] if k else None
    out, n = [], at[-1] if at else None
    while n is not None:
        out.append(marks[n])
        n = prev[n]
    return out[::-1]


def weighted_line_up(a, b, a_dir, b_dir):
    """The weighted line-up of line_up_by_direction, line by line, over the stretch of a around the lines difflib
    finds in b, with a margin of b's length on each side."""
    rough = line_up(a, b)
    if not rough or not b:
        return {}
    lo = max(0, min(rough) - len(b))
    hi = min(len(a), max(rough) + len(b) + 1)
    ids = {}
    A = [ids.setdefault(k, len(ids)) for k in a[lo:hi]]
    B = [ids.setdefault(k, len(ids)) for k in b]
    agree = [[bool(d) and d == e for e in b_dir] for d in a_dir[lo:hi]]
    n, m = len(A), len(B)
    big = n + m + 1
    prev = [0] * (m + 1)
    trace = []
    for i in range(1, n + 1):
        cur = [0] * (m + 1)
        steps = bytearray(m + 1)
        ai, agi = A[i - 1], agree[i - 1]
        for j in range(1, m + 1):
            best, step = prev[j], 1                       # this export line not lined up
            if cur[j - 1] > best:
                best, step = cur[j - 1], 2                # this walk line not lined up
            if ai == B[j - 1]:
                take = prev[j - 1] + big + agi[j - 1]
                if take > best:                           # ties keep the lines earlier, the way difflib did
                    best, step = take, 3
            cur[j] = best
            steps[j] = step
        trace.append(steps)
        prev = cur
    pairs, i, j = {}, n, m
    while i and j:
        step = trace[i - 1][j]
        if step == 3:
            pairs[lo + i - 1] = j - 1
            i, j = i - 1, j - 1
        elif step == 2:
            j -= 1
        else:
            i -= 1
    return pairs


def walk_units(wk, walk_rows):
    """The walk's message lines as units to line up: one per line, except that the photos of an album ("Ver foto, 1
    de 6") and its last tile ("Ver los 6 archivos multimedia") make one unit, the album as its grid shows it. A photo
    the grid already showed is kept apart as a line written twice; a photo after the album's tile starts another
    album."""
    position = {id(r): p for p, r in enumerate(walk_rows)}
    units, album = [], None
    for r, kind, direction in wk:
        text = plain(r.get("text"))
        photo = ALBUM_PHOTO.fullmatch(text) if kind == "picture" else None
        tile = ALBUM_TILE.fullmatch(text) if kind == "album tile" else None
        if not (photo or tile):
            units.append({"kind": kind, "row": r, "direction": direction, "text": text})
            album = None
            continue
        size = int(photo.group(2)) if photo else int(tile.group(1))
        k = int(photo.group(1)) if photo else None
        # An album is done when its grid is: a tile and the three photos beside it, or all of its four or fewer
        # photos. A tile read before photo 3 did not end it (photo 3 then started an album of its own); an album of
        # the other sender, or a grid starting again at photo 1, starts another (two albums of 3 in a row, the first
        # missing a photo, became one; #62, found by testing made-up chats).
        done = album is not None and len(album["photos"]) >= (3 if album["size"] > 4 else album["size"]) and (
            album["size"] <= 4 or album["tile"] is not None)
        other = album is not None and direction and album["dirs"] and direction not in album["dirs"]
        again = album is not None and k == 1 and 1 in album["photos"]
        if album is None or album["size"] != size or done or other or again or (tile and album["tile"] is not None):
            album = {"kind": "album", "size": size, "photos": {}, "extra": [], "tile": None, "hidden": 0, "dirs": [],
                     "row": r, "text": text}
            units.append(album)
        album["dirs"].append(direction)
        if photo:
            if k in album["photos"]:
                album["extra"].append((r, direction))
            else:
                album["photos"][k] = (r, direction)
        else:
            album["tile"] = r
            # The tile stands for the number on it, read from the "+ 3" line beside it; with none, for all but the
            # three photos a grid of four shows (an album of 6 with only photo 1 and the tile in a walk was called
            # whole, with 5 behind a tile for 3: #62).
            album["hidden"] = size - 3
            for near in walk_rows[position[id(r)] + 1:position[id(r)] + 3]:
                m = re.fullmatch(r"\+\s*(\d+)", plain(near.get("text")))
                if (near.get("resource_id") or "").endswith(":id/more") and m:
                    album["hidden"] = int(m.group(1))
                    break
    for u in units:
        if u["kind"] == "album":
            known = [d for d in u["dirs"] if d]
            u["direction"] = max(set(known), key=known.count) if known else ""
    return units


def export_units(export_lines):
    """The export's lines as units to line up: one per line, except that an album (its empty first line and its photos
    and videos) makes one unit. The captions of an album's files follow the album, as they show under its grid."""
    units, albums = [], {}
    for x in export_lines:
        if x["kind"] in ("system", "attachment"):
            continue
        if x["kind"] == "album":
            albums[x["n"]] = {"kind": "album", "line": x, "files": [], "size": x.get("album_size"), "author": x["author"]}
            units.append(albums[x["n"]])
        elif x.get("album") in albums:
            albums[x["album"]]["files"].append(x)
        else:
            units.append({"kind": x["kind"], "line": x, "author": x["author"], "text": x["text"]})
    return units


def unit_key(u):
    if u["kind"] == "card":
        return ("card", id(u))   # a card's line lines up with no export line
    if u["kind"] == "album":
        return ("album", u["size"])
    return key(u["kind"], u.get("text"))


def compare(export_lines, walk_rows, me, ends=(False, False)):
    """Rows for export_check.csv and counts per kind. The export's lines and the walk's are lined up in order, an
    album as one unit on each side."""
    oldest_unsure, newest_unsure = ends
    # The owner's name as given is made plain like the export's names: a name with an emoji joined by U+200D, a
    # direction mark or two spaces never matched otherwise (#62, found by testing made-up chats).
    me = plain(me)
    wk = []
    for r in walk_rows:
        k = walk_kind(r)
        if k:
            wk.append((r, k[0], k[1]))
    E, W = export_units(export_lines), walk_units(wk, walk_rows)

    def sent_by(author):
        return ("sent" if author == me else "received") if author else ""

    # An album lines up with an album of the same size: photos look alike, so lined up one by one two albums of the
    # same size side by side mixed their photos, and a grid the walk wrote twice took the photos behind the tile in
    # its place (#62, found by testing made-up chats).
    # A walk that did not reach the oldest end (--stop-at) covers the newest part, so the line-up starts from the
    # newest end: from the oldest, a line said often ("ok") was found in its oldest copies and the newest ones the
    # walk shows came out missing (#62, found by testing made-up chats).
    def line_up_units(eu, wu):
        return line_up_by_direction([unit_key(u) for u in eu], [unit_key(u) for u in wu],
                                    [sent_by(u["author"]) for u in eu], [u["direction"] for u in wu],
                                    from_end=oldest_unsure)

    pairs = line_up_units(E, W)

    # The export writes an album's first line and a call alike, as an empty message, and lists a photo sent on its
    # own right after an album, at the same minute, as one more file of it. So an album can also be read as a call
    # with photos of their own, or as a smaller album the walk shows with the rest as photos of their own. Each album
    # is tried each other way over the whole chat, and a reading is kept when it lines up more lines in order (or as
    # many, with more directions that agree); this is done again until no reading lines up more. (A call followed by
    # two photos sent apart read as an album, and both came out as differences: #62. Settled by whatever call or
    # photo was free near it, or by the stretch a first line-up left it, a photo sent later took the place of one of
    # the album's, a call or photos out of order still passed, and an album of 5 and a photo before an album of 6
    # took the wrong album: #62, found by testing made-up chats.)
    def readings(u):
        files = [{"kind": f["kind"], "line": f, "author": f["author"], "text": f["text"]} for f in u["files"]]
        call = {"kind": "call", "line": u["line"], "author": u["author"], "text": "", "from_album": True}
        out = [[call] + files]
        for size in sorted({w["size"] for w in W if w["kind"] == "album" and 2 <= w["size"] < len(u["files"])}):
            out.append([{**u, "files": u["files"][:size], "size": size}] + files[size:])
        return out

    def score(eu, got):
        return len(got), sum(1 for i, j in got.items() if W[j]["direction"] and W[j]["direction"] == sent_by(eu[i]["author"]))

    # Each round tries every reading of every album and keeps the one that lines up the most: taking the first
    # that helped read a real album of 2 as a call, where the call and its photos were the next one (#62).
    best = score(E, pairs)
    while True:
        # Only an album the line-up left out, or one of a size the export has more of than the line-up found, can
        # be read better; trying every album each round took minutes on a chat of 2,000 messages.
        lone = {E[i]["size"] for i, u in enumerate(E) if u["kind"] == "album" and i not in pairs}
        tried = [(E[:i] + reading + E[i + 1:]) for i, u in enumerate(E)
                 if u["kind"] == "album" and (i not in pairs or u["size"] in lone) for reading in readings(u)]
        tried = [(score(trial, got), trial, got) for trial in tried for got in [line_up_units(trial, W)]]
        top = max(tried, key=lambda t: t[0], default=None)
        if not top or top[0] <= best:
            break
        best, E, pairs = top
    used = set(pairs.values())
    first = min(pairs) if pairs else None
    last = max(pairs) if pairs else None

    def not_walked(i):
        """Past the first or last line found, at an end of the list the walk did not confirm reaching. With no line
        found at all there is no such end: a walk that found nothing passed when one end was unsure, every line of
        the export called not walked (#62, found by testing made-up chats)."""
        if first is None:
            return False
        return (i < first and oldest_unsure) or (i > last and newest_unsure)

    # A link sent on its own can be shown as its preview card alone (title, snippet, address: section 14 of the
    # manual), with no line holding the typed link. The card is up to three text lines no export line took, between
    # the messages found just before and just after the link, one of which holds the link's address ("github.com").
    # Without that address any line there was taken as the card: a voice note written twice, a photo, another link
    # (#62, found by testing made-up chats). A link in the part that was not walked has no card in the walk either
    # (a walk with --stop-at on a Samsung SM-G990E, 21 November 2026, called such a link's result a preview card).
    # A card is a run of the walk's card lines (title, snippet, address) ending in the line that holds the link's own
    # address, as a whole name ("x.com" is not in "netflix.com", "github.com" not in "github.com.evil.org"). Only
    # card lines make a card: messages the walk wrote around a link were taken as its card and passed (#62). A card
    # right above a link the walk found by its text is that link's, and no other link takes it. Links that share a
    # stretch take their cards in order; a card the walk shows at an end it did not confirm reaching was walked, so it
    # is looked for there too. A card no link takes is a link the export does not have (a card written twice passed).
    runs, j = [], 0
    while j < len(W):
        if W[j]["kind"] == "card":
            k = j
            # A card ends at its address line, so two cards in a row are two runs.
            while k + 1 < len(W) and W[k + 1]["kind"] == "card" and not (W[k]["row"].get("resource_id") or "").endswith(":id/url"):
                k += 1
            after = W[k + 1] if k + 1 < len(W) else None
            owned = after is not None and (k + 1) in used and LINK_ALONE.match(after.get("text") or "")
            if not owned:
                runs.append(list(range(j, k + 1)))
            j = k + 1
        else:
            j += 1

    def host_of(link):
        try:
            text = link if "://" in link else "http://" + link
            return (urllib.parse.urlsplit(text).hostname or "").removeprefix("www.")
        except ValueError:   # an address urlsplit cannot read ("http://[x"): no card can be told to be its
            return ""

    card, by_card = set(), {}
    for i, u in enumerate(E):
        if u["kind"] != "link" or i in pairs:
            continue
        before = max((pairs[p] for p in pairs if p < i), default=-1)
        after = min((pairs[q] for q in pairs if q > i), default=len(W))
        host = host_of(u["text"])
        at = re.compile(r"(?<![\w.-])(?:[\w-]+\.)*" + re.escape(host) + r"(?![\w.-])") if host else None
        for run in runs:
            if at and run[0] > before and run[-1] < after and not card & set(run) \
                    and at.search(W[run[-1]]["text"].lower()):
                card |= set(run)
                by_card[i] = run[-1]
                break
    stray = [j for run in runs if not card & set(run) for j in run[-1:]]

    counts = {k: {"export": 0, "found": 0, "direction_right": 0, "no_direction": 0, "not_walked": 0, "missing": 0,
                  "behind_tile": 0, "walk": 0, "only_walk": 0} for k in KINDS}
    results = {}   # id(export line) -> the fields of its row

    def mark(x, result, wrow=None, direction="", note="", kind=None):
        c = counts.get(kind or x["kind"])
        f = {"result": result, "note": note}
        if c is not None:
            c["export"] += 1
        if wrow is not None:
            by_export = sent_by(x["author"])
            agrees = ("yes" if direction == by_export else "NO") if direction else "no direction in the walk"
            f.update(walk_line=wrow.get("line", ""), walk_direction=direction, direction_agrees=agrees,
                     screenshot=wrow.get("screenshot", ""))
            if c is not None:
                c["found"] += 1
                c["direction_right"] += direction == by_export
                c["no_direction"] += not direction
        elif c is not None:
            c[{MISSING: "missing", NOT_WALKED: "not_walked", BEHIND_TILE: "behind_tile"}[result]] += 1
        results[id(x)] = f

    only = []   # (walk row, kind, direction, result) for lines the export does not have

    def album_found(files, w, edge=None):
        """An album lined up with the walk's: the files its grid shows are found while the walk has photos for them,
        and missing after; as many as its last tile stands for are behind it; any more are missing. At an end of the
        list the walk did not confirm reaching, the grid's photos the walk lacks past the ones it read (lower numbers
        at the oldest end, higher at the newest) may be past where it stopped, so they are not walked, not missing
        (a walk that stopped half way up an album's grid: #62); one it skipped between photos it read is missing
        (#62, both found by testing made-up chats). The walk's photos past those, and any photo written twice, are
        lines the export does not have."""
        hidden = w["hidden"] if w["tile"] is not None else 0
        shown = max(0, w["size"] - hidden)
        photos = [w["photos"][k] for k in sorted(w["photos"])]
        n = min(len(photos), shown, len(files))
        read = [k for k in w["photos"] if k <= shown]
        unread = [k for k in range(1, shown + 1) if k not in w["photos"]]
        past = len([k for k in unread if not read or (edge == "oldest" and k < min(read)) or (edge == "newest" and k > max(read))]) if edge else 0
        lacking = [idx for idx in range(n, min(shown, len(files)))]
        for idx, f in enumerate(files):
            if idx < n:
                mark(f, FOUND, photos[idx][0], photos[idx][1], ALBUM_NOTE)
            elif idx >= shown and idx < shown + hidden:
                mark(f, BEHIND_TILE, note=ALBUM_NOTE)
            elif idx in lacking[:past]:
                mark(f, NOT_WALKED, note=NOT_WALKED_NOTE)
            else:
                mark(f, MISSING, note=ALBUM_NOTE)
        for r, d in photos[n:] + w["extra"]:
            only.append((r, "picture", d, ONLY_WALK))
        if w["tile"] is not None:
            only.append((w["tile"], "album tile", w["direction"], TILE))

    for i, u in enumerate(E):
        x = u["line"]
        if u["kind"] == "album":
            if i in pairs:
                results[id(x)] = {"result": ALBUM, "note": ""}
                album_found(u["files"], W[pairs[i]], edge="oldest" if i == first and oldest_unsure else "newest" if i == last and newest_unsure else None)
            else:
                walked = not not_walked(i)
                results[id(x)] = {"result": ALBUM, "note": "" if walked else NOT_WALKED_NOTE}
                for f in u["files"]:
                    if walked:
                        mark(f, MISSING, note=ALBUM_NOTE)
                    else:
                        mark(f, NOT_WALKED, note=NOT_WALKED_NOTE)
        elif u.get("from_album"):
            # An album's first line read as a call.
            note = "the export writes a call and an album's first line alike; read here as a call"
            if i in pairs:
                mark(x, FOUND, W[pairs[i]]["row"], W[pairs[i]]["direction"], note, kind="call")
            elif not_walked(i):
                mark(x, NOT_WALKED, note=NOT_WALKED_NOTE, kind="call")
            else:
                mark(x, MISSING, note=note, kind="call")
            results[id(x)]["kind"] = "call"
        elif i in pairs:
            mark(x, FOUND, W[pairs[i]]["row"], W[pairs[i]]["direction"])
        elif i in by_card:
            w = W[by_card[i]]
            mark(x, FOUND, w["row"], w["direction"])
            results[id(x)]["result"] = LINK_CARD
        elif not_walked(i):
            mark(x, NOT_WALKED, note=NOT_WALKED_NOTE)
        else:
            mark(x, MISSING)

    for j, w in enumerate(W):
        if w["kind"] == "album":
            if j in used:
                continue
            for r, d in [w["photos"][k] for k in sorted(w["photos"])] + w["extra"]:
                only.append((r, "picture", d, ONLY_WALK))
            if w["tile"] is not None:
                only.append((w["tile"], "album tile", w["direction"], ONLY_WALK))
        elif j in card:
            only.append((w["row"], w["kind"], w["direction"], CARD_LINE))
        elif j in stray:
            only.append((w["row"], "link", w["direction"], ONLY_WALK))
        elif j not in used and w["kind"] != "card":
            only.append((w["row"], w["kind"], w["direction"], ONLY_WALK))

    rows = []
    for x in export_lines:
        row = {"export_line": x["n"], "kind": x["kind"], "author": x["author"], "direction_by_export": sent_by(x["author"]),
               "text": x["text"], "result": "", "walk_line": "", "walk_direction": "", "direction_agrees": "",
               "screenshot": "", "note": ""}
        if x["kind"] == "system":
            row["result"] = SYSTEM
        elif x["kind"] == "attachment":
            row["result"] = OTHER_FILE
        else:
            row.update(results.get(id(x), {"result": MISSING}))
        rows.append(row)
    for r, kind, direction, result in only:
        # An album's tile the export has no album for, or a tile written twice, stands for photos: it counts as
        # photos the export lacks (it passed uncounted: #62, found by testing made-up chats).
        c = counts.get("picture" if kind == "album tile" else kind)
        if c is not None and result == ONLY_WALK:
            c["only_walk"] += 1
        if kind == "described" and result == ONLY_WALK:
            result = DESCRIBED_ONLY
        rows.append({"export_line": "", "kind": kind, "author": "", "direction_by_export": "", "text": plain(r.get("text")),
                     "result": result, "walk_line": r.get("line", ""), "walk_direction": direction, "direction_agrees": "",
                     "screenshot": r.get("screenshot", ""), "note": ""})
    # A walk line found for an export line counts as the export's kind (a large emoji is described, not
    # written, and is still a text); one found for none counts as its own kind.
    for c in counts.values():
        c["walk"] = c["found"] + c["only_walk"]
    return rows, counts


def passed(counts):
    return all(c["missing"] == 0 and c["only_walk"] == 0 and c["direction_right"] + c["no_direction"] == c["found"]
               for c in counts.values())


def count_lines(counts):
    """One line per kind in the export or the walk, as verify prints them: (ok, text)."""
    out = []
    for kind in KINDS:
        c = counts[kind]
        if not (c["export"] or c["walk"]):
            continue
        text = f"{PLURAL[kind]}: {c['export']} in the export, {c['found']} found"
        if c["found"]:
            text += f" ({c['direction_right']} with the direction the export gives"
            text += f", {c['no_direction']} with none in the walk)" if c["no_direction"] else ")"
        if c["not_walked"]:
            text += f", {c['not_walked']} not walked"
        if c["behind_tile"]:
            text += f", {c['behind_tile']} behind an album's last tile"
        if c["missing"]:
            text += f", {c['missing']} MISSING"
        text += f"; {c['walk']} in the walk" + (f", {c['only_walk']} of them NOT in the export" if c["only_walk"] else "")
        ok = c["missing"] == 0 and c["only_walk"] == 0 and c["direction_right"] + c["no_direction"] == c["found"]
        out.append((ok, text))
    return out


# ---- The export folder ----


def chain_rows(export):
    with open(os.path.join(export, "actions.jsonl"), encoding="utf-8") as f:
        return [json.loads(x) for x in f if x.strip()]


def attached_zip(export, rows, name=None):
    """The attached zip to read and its chained row, checked against the SHA-256 in that row."""
    import appwalk
    ok, msg, _ = appwalk.verify_chain(rows)
    if not ok:
        raise CheckStopped(f"the hash chain is not intact ({msg}); run verify")
    attached = [(r, json.loads(r["detail"])) for r in rows if r["action"] == "file_attached"]
    zips = [(r, d) for r, d in attached if d.get("zip_members") is not None]
    if name:
        zips = [(r, d) for r, d in zips if d["file"] == name]
        if not zips:
            raise CheckStopped(f"no zip named {name!r} was attached to this export")
    if not zips:
        raise CheckStopped("no zip was attached to this export; add WhatsApp's Export chat with attach first")
    if len(zips) > 1:
        raise CheckStopped("more than one zip is attached; say which with --zip: " + ", ".join(d["file"] for _, d in zips))
    row, d = zips[0]
    path = os.path.join(export, "attachments", d["file"])
    if not os.path.exists(path):
        raise CheckStopped(f"attachments/{d['file']} is missing")
    got = sha256_file(path)
    if got != d["sha256"]:
        raise CheckStopped(f"attachments/{d['file']} does not match the SHA-256 in its chained row (seq {row['seq']}); "
                           "it was not read")
    return path, row, d


def chat_text(zip_path, chat=None):
    with zipfile.ZipFile(zip_path) as z:
        texts = [n for n in z.namelist() if n.lower().endswith(".txt")]
        if chat:
            texts = [n for n in texts if n == chat]
            if not texts:
                raise CheckStopped(f"the zip holds no {chat!r}")
        if not texts:
            raise CheckStopped("the zip holds no chat text (.txt)")
        if len(texts) > 1:
            raise CheckStopped("the zip holds more than one chat text; say which with --chat: " + ", ".join(texts))
        return texts[0], z.read(texts[0]).decode("utf-8-sig")


def transcript_source():
    """The transcript.py this check ran with, its SHA-256, and where it is. A ready-made build carries a copy of
    the file beside its code (devtools/build_binaries.py), the one it was built from."""
    path = os.path.join(os.path.dirname(os.path.abspath(transcript.__file__)), "transcript.py")
    where = "the copy bundled with this build" if getattr(sys, "frozen", False) else path
    if not os.path.exists(path):
        return None, "not found in this build"
    return sha256_text(path), where


def sha256_text(path):
    """The SHA-256 of a text file with its line endings made LF, as the repository holds it. Git on Windows checks
    files out with CRLF, on this computer and on the Windows runners that make the builds, so the same
    transcript.py gave one hash there and another on macOS and Linux (21 November 2026); with LF, every copy of
    the same file gives the hash of the file as GitHub shows it."""
    with open(path, "rb") as f:
        return hashlib.sha256(f.read().replace(b"\r\n", b"\n")).hexdigest()


def csv_text(rows, columns):
    out = io.StringIO(newline="")
    w = csv.DictWriter(out, fieldnames=columns)
    w.writeheader()
    w.writerows(rows)
    return out.getvalue()


def write_rows(path, rows):
    with open(path, "w", newline="", encoding="utf-8") as f:
        f.write(csv_text(rows, COLUMNS))


def check(export, me, *, owner_wrote_nothing=False, zip_name=None, chat=None, item=None, profile_folder=None):
    """Runs the check and writes its files. Returns (ok, lines): the summary, as it is printed."""
    import appwalk
    me = plain(me)   # as the export's names are read, so the same name matches however it was typed
    if not os.path.exists(os.path.join(export, "manifest.json")):
        raise CheckStopped(f"{export} is not a finished AppWalk export: it has no manifest.json")
    with open(os.path.join(export, "manifest.json"), encoding="utf-8") as f:
        manifest = json.load(f)
    package = manifest["apps_under_test"][0]["package"]
    if package != WHATSAPP:
        raise CheckStopped(f"this export walked {package}; the check reads WhatsApp exports only")
    rows = chain_rows(export)
    zip_path, zip_row, zip_detail = attached_zip(export, rows, zip_name)
    chat_name, text = chat_text(zip_path, chat)
    lines = parse_export(text)
    senders = []
    for x in lines:
        if x["author"] and x["author"] not in senders:
            senders.append(x["author"])
    if me not in senders and not owner_wrote_nothing:
        raise CheckStopped(f"no sender in the export is named {me!r}; the senders are: " + ", ".join(senders)
                           + ". Give --me as the export spells the walked phone's owner, or --owner-wrote-nothing "
                             "if the owner wrote nothing in this chat")
    built, _notes, _ = transcript.build(export, profile_folder)
    # The walked items are the log's, not the transcript's: a walk that read no line has none in the transcript, and
    # its item was taken as "", whose ends the log does not have, so both ends counted as unsure (#62).
    items = []
    for r in rows:
        if r["action"] == "walk_start":
            name = json.loads(r["detail"]).get("item") or ""
            if name not in items:
                items.append(name)
    if item is None:
        if len(items) > 1:
            raise CheckStopped("the export has more than one walked item; say which with --item: "
                               + ", ".join(repr(i) for i in items))
        item = items[0] if items else ""
    elif item not in items:
        raise CheckStopped(f"the export has no walked item {item!r}; it has: " + ", ".join(repr(i) for i in items))
    ends = walked_ends(export, item)
    as_text = [{k: "" if v is None else str(v) for k, v in r.items()} for r in built]
    result, counts = compare(lines, [r for r in as_text if r["item"] == item], me, ends)
    ok = passed(counts)
    write_rows(os.path.join(export, CSV_NAME), result)

    profile = transcript.load_profile(package, profile_folder)
    t_hash, t_where = transcript_source()
    out = [f"AppWalk {appwalk.VERSION}; transcript.py sha256 {t_hash or '-'} with LF line endings ({t_where})"]
    if profile:
        out.append(f"profile {os.path.basename(profile['_path'])}, {profile.get('_from')}, sha256 "
                   f"{sha256_text(profile['_path'])} with LF line endings")
    else:
        out.append(f"no profile for {package}: the transcript gives no message lines, so nothing can be found")
    out.append(f"export chat attachments/{zip_detail['file']}, sha256 {zip_detail['sha256']}, matches its chained row "
               f"(seq {zip_row['seq']}); chat text {chat_name}")
    out.append(f"latest row hash {rows[-1]['row_hash']}")
    out.append(f"walked phone's owner as the export spells it: {me}" + ("" if me in senders else
               " (not a sender: the examiner says the owner wrote nothing in this chat)"))
    out.append(f"item: {item!r}" if item else "item: the screen walked")
    unsure = [w for w, u in zip(("oldest", "newest"), ends) if u]
    if unsure:
        out.append("the walk did not confirm reaching the " + " and the ".join(unsure) + " end of the list: export "
                   "lines past the first or last one found there are counted as not walked")
    system = sum(1 for x in lines if x["kind"] == "system")
    other = sum(1 for x in lines if x["kind"] == "attachment")
    links = sum(1 for x in lines if x["kind"] == "link")
    # An album's first line read as a call is a call, not an album (#62, found by testing made-up chats).
    albums = sum(1 for r in result if r["export_line"] and r["result"] == ALBUM)
    calls_read = sum(1 for r in result if r["export_line"] and r["kind"] == "call" and r["direction_by_export"]
                     and any(x["n"] == r["export_line"] and x["kind"] == "album" for x in lines))
    out.append(f"{len({x['n'] for x in lines if x['kind'] != 'system'}) - albums} messages in the export, "
               f"{system} system line(s)" + (f", {albums} album(s)" if albums else "")
               + (f", {calls_read} call(s) written like an album's first line" if calls_read else "")
               + (f", {links} link(s) sent alone" if links else "") + (f", {other} other attachment(s) not compared" if other else ""))
    out += [("ok      " if good else "WARNING ") + t for good, t in count_lines(counts)]

    path = os.path.join(export, "transcript.csv")
    if not os.path.exists(path):
        out.append("transcript.csv: not in the export")
    else:
        with open(path, encoding="utf-8", newline="") as f:
            on_disk = f.read()
        if on_disk == csv_text(built, transcript.COLUMNS):
            out.append("transcript.csv: the same text as the transcript this AppWalk builds now. That says nothing "
                       "about what the walk first wrote: attach writes transcript.csv again")
        else:
            file_rows = [r for r in csv.DictReader(io.StringIO(on_disk)) if r.get("item", "") == item]
            f_result, f_counts = compare(lines, file_rows, me, ends)
            write_rows(os.path.join(export, FILE_CSV_NAME), f_result)
            out.append(f"transcript.csv DIFFERS from the transcript this AppWalk builds now; the same counts on the "
                       f"file ({FILE_CSV_NAME}):")
            out += [("  ok      " if good else "  WARNING ") + t for good, t in count_lines(f_counts)]
            ok = ok and passed(f_counts)
    out.append(f"export check: {'PASS' if ok else 'DIFFERENCES'}; each line in {CSV_NAME}")
    with open(os.path.join(export, TXT_NAME), "w", encoding="utf-8") as f:
        f.write("\n".join(out) + "\n")
    return ok, out
