#!/usr/bin/env python3
"""check-export: compares a WhatsApp walk with the chat's own Export chat, added to the export with `attach`.

On a phone without root, WhatsApp's Export chat is the only second source for what a WhatsApp walk read:
ALEAPP cannot read msgstore.db without root. This reads the chat's text from the attached zip and finds
each of its lines in the walk's transcript, in order, and the other way round: what the transcript has
that the export does not (a voice note written twice, abrignoni/appwalk#39).

For each line of the export:
- a text: is it the text of a message line in the transcript, with the direction its sender gives;
- a voice note (PTT-....opus): is there a voice note line;
- a picture or a video: is there one, and its caption, when it has one;
- a deleted message: is there a deleted-message line;
- a link sent on its own: found, or said to be shown as a preview card (section 14 of the manual);
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
import difflib
import json
import os
import re
import unicodedata

FOUND, MISSING, NOT_WALKED, ONLY_WALK = "found", "missing", "not walked", "only in the walk"
SYSTEM = "system line (not counted)"
LINK_CARD = "link sent alone: WhatsApp shows a preview card, not the typed link (not counted)"
CARD_LINE = "only in the walk, where the export has a link sent alone: taken as its preview card (not counted)"
OTHER_FILE = "attachment of another kind (not compared)"
# The kinds that are counted, in the order the summary gives them.
KINDS = ["text", "caption", "voice note", "picture", "video", "deleted"]
PLURAL = {"text": "texts", "caption": "captions", "voice note": "voice notes", "picture": "pictures", "video": "videos",
          "deleted": "deleted messages"}

# The line that starts a message in an Android export, once odd spaces are plain ones: "14/11/2026, 03:22 - "
# (24 hours, Samsung SM-G990E, es-US) or "14/11/26, 3:22 a. m. - " (12 hours). What follows is "Name: text"
# or, for a line nobody wrote (group created, the encryption notice), the text alone.
START = re.compile(r"^(\d{1,2})/(\d{1,2})/(\d{2,4}),? (\d{1,2}):(\d{2})(?: ?([ap])\.? ?m\.?)? - (.*)$", re.I)
# iOS writes "[14/11/26, 3:22:05 a. m.] Name: text"; not tried, so it is recognised only to say so.
IOS_START = re.compile(r"^\[\d{1,2}/\d{1,2}/\d{2,4},? \d{1,2}:\d{2}:\d{2}")
ATTACHED = re.compile(r"^(\S+\.\w+) \(archivo adjunto\)$")
LINK_ALONE = re.compile(r"^https?://\S+$")
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
            messages.append({"n": n, "author": author.strip() if sep else "", "body": body if sep else rest})
        elif messages:
            messages[-1]["body"] += "\n" + line
    out = []
    for msg in messages:
        n, author = msg["n"], msg["author"]
        body = "\n".join(x.strip() for x in msg["body"].replace("\u200e", "").split("\n")).strip()
        if not author:
            out.append({"n": n, "author": "", "kind": "system", "text": plain(body), "file": ""})
            continue
        first_line, _, more = body.partition("\n")
        att = ATTACHED.match(plain(first_line))
        if att:
            name = att.group(1)
            kind = ("voice note" if name.upper().startswith("PTT-") else "picture" if name.upper().startswith("IMG-")
                    else "video" if name.upper().startswith("VID-") else "attachment")
            out.append({"n": n, "author": author, "kind": kind, "text": name, "file": name})
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
    if role not in ("message", "described"):
        return None
    if text in (DELETED_OWN, DELETED_OTHERS):
        # The walk's own words say whose it was, as on the screen: "Eliminaste" on the phone that deleted it.
        return "deleted", direction or ("sent" if text == DELETED_OWN else "received")
    if rid in WALK_IDS and (role == "described" or rid == "caption"):
        return WALK_IDS[rid], direction
    if role == "message":
        return "text", direction
    # A message of one emoji is drawn large and described, not written (the 👍 of the known-data chat).
    return "described", direction


def key(kind, text):
    """What two lines must share to be the same message: the text for text, a caption, a link and a large
    emoji; the kind alone for a voice note, a picture, a video or a deleted message."""
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


def compare(export_lines, walk_rows, me, ends=(False, False)):
    """Rows for export_check.csv and counts per kind. The export's lines and the transcript's are lined up in
    order (difflib, without its junk rule: five voice notes look alike and must all count)."""
    oldest_unsure, newest_unsure = ends
    ex = [x for x in export_lines if x["kind"] not in ("system", "attachment")]
    wk = []
    for r in walk_rows:
        k = walk_kind(r)
        if k:
            wk.append((r, k[0], k[1]))
    a = [key(x["kind"], x["text"]) for x in ex]
    b = [key(kind, r.get("text")) for r, kind, _ in wk]
    pairs = {}
    for block in difflib.SequenceMatcher(None, a, b, autojunk=False).get_matching_blocks():
        for i in range(block.size):
            pairs[block.a + i] = block.b + i
    first = min(pairs) if pairs else None
    last = max(pairs) if pairs else None
    used = set(pairs.values())
    # A link sent on its own is shown as its preview card (title, snippet, address: section 14 of the manual),
    # so the walk has the card's lines where the export has the link. The walk's lines that no export line
    # took, between the messages found just before and just after such a link, are taken as that card.
    card = set()
    for i, x in enumerate(ex):
        if x["kind"] != "link" or i in pairs:
            continue
        before = max((pairs[p] for p in pairs if p < i), default=-1)
        after = min((pairs[q] for q in pairs if q > i), default=len(wk))
        card |= {j for j in range(before + 1, after) if j not in used}
    found_at = {id(x): i for i, x in enumerate(ex)}
    rows, counts = [], {k: {"export": 0, "found": 0, "direction_right": 0, "no_direction": 0, "not_walked": 0,
                            "missing": 0, "walk": 0, "only_walk": 0} for k in KINDS}
    for x in export_lines:
        by_export = ("sent" if x["author"] == me else "received") if x["author"] else ""
        row = {"export_line": x["n"], "kind": x["kind"], "author": x["author"], "direction_by_export": by_export,
               "text": x["text"], "result": "", "walk_line": "", "walk_direction": "", "direction_agrees": "",
               "screenshot": "", "note": ""}
        if x["kind"] == "system":
            row["result"] = SYSTEM
        elif x["kind"] == "attachment":
            row["result"] = OTHER_FILE
        else:
            i = found_at[id(x)]
            c = counts.get(x["kind"])
            if c is not None:
                c["export"] += 1
            if i in pairs:
                r, _, direction = wk[pairs[i]]
                row.update(result=FOUND, walk_line=r.get("line", ""), walk_direction=direction,
                           screenshot=r.get("screenshot", ""))
                if not direction:
                    row["direction_agrees"] = "no direction in the walk"
                else:
                    row["direction_agrees"] = "yes" if direction == by_export else "NO"
                if c is not None:
                    c["found"] += 1
                    c["direction_right"] += direction == by_export
                    c["no_direction"] += not direction
            elif x["kind"] == "link":
                row["result"] = LINK_CARD
            elif (first is None and (oldest_unsure or newest_unsure)) or (first is not None and (
                    (i < first and oldest_unsure) or (i > last and newest_unsure))):
                row["result"] = NOT_WALKED
                row["note"] = "past the end of the list the walk did not confirm reaching"
                if c is not None:
                    c["not_walked"] += 1
            else:
                row["result"] = MISSING
                if c is not None:
                    c["missing"] += 1
        rows.append(row)
    for j, (r, kind, direction) in enumerate(wk):
        if j in used:
            continue
        c = counts.get(kind)
        if c is not None and j not in card:
            c["only_walk"] += 1
        rows.append({"export_line": "", "kind": kind, "author": "", "direction_by_export": "", "text": plain(r.get("text")),
                     "result": CARD_LINE if j in card else ONLY_WALK, "walk_line": r.get("line", ""),
                     "walk_direction": direction, "direction_agrees": "", "screenshot": r.get("screenshot", ""), "note": ""})
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
        if c["missing"]:
            text += f", {c['missing']} MISSING"
        text += f"; {c['walk']} in the walk" + (f", {c['only_walk']} of them NOT in the export" if c["only_walk"] else "")
        ok = c["missing"] == 0 and c["only_walk"] == 0 and c["direction_right"] + c["no_direction"] == c["found"]
        out.append((ok, text))
    return out
