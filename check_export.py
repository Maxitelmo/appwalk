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
import re
import unicodedata

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
