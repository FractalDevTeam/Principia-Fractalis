#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""Coq-side hygiene gate -- the cross-prover mirror of semantic_hygiene_gate.py.

The Coq layer is the corpus's independent confirmation surface: 765 .v files
under PF_Coq_Code, built against a _CoqProject that maps -Q PF PrincipiaTractalis.
It needs the same two checks the Lean side has:

  ESCAPE HATCHES (Coq analogue of sorry / native_decide / axiom)
    Admitted.      a theorem signature with no proof
    Abort.         an abandoned proof
    admit.         an admitted goal inside a proof
    Axiom          a declared axiom
    Parameter      an assumed constant
    Hypothesis     an assumed hypothesis
    Conjecture     an explicit conjecture

  SEMANTIC HYGIENE (Coq analogue of criterion (f))
    TRUE_BODY          Definition _ : Prop := True
    FALSE_BODY         Definition _ : Prop := False
    UNIT_CARRIER       quantifies over unit
    ALL_BINDERS_DEAD   every binder underscore-prefixed
    EXTERNAL_NAME_TRIV named after published mathematics, trivial body
    REFLEXIVE          body is x = x

As on the Lean side this is DIAGNOSTIC: every finding locates formalization work
and never refutes the intended mathematics. Nothing is modified.

COMMENT HANDLING MATTERS AS MUCH AS IT DID IN LEAN. Coq comments are (* ... *),
nestable, and there are no line comments. A raw grep for "Admitted" over this
tree returns 21 files, of which most are docstring prose -- including four files
whose headers say "ZERO Admitted". Stripping first is the difference between a
real count and an artifact.

Read-only.

Author: Pablo Cohen + Claude Opus 5. 2026-10-06.
"""
import argparse
import io
import os
import re
import sys
from collections import Counter, defaultdict

ROOT = "/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Coq_Code"
NL = chr(10)

ESCAPES = {
    "Admitted": re.compile(r"(?<![A-Za-z_])Admitted\s*\."),
    "Abort": re.compile(r"(?<![A-Za-z_])Abort\s*\."),
    "admit": re.compile(r"(?<![A-Za-z_])admit\s*\."),
    "Axiom": re.compile(r"^\s*Axiom\s+", re.MULTILINE),
    "Parameter": re.compile(r"^\s*Parameter\s+", re.MULTILINE),
    "Hypothesis": re.compile(r"^\s*Hypothesis\s+", re.MULTILINE),
    "Conjecture": re.compile(r"^\s*Conjecture\s+", re.MULTILINE),
}

EXTERNAL = ("Wiles", "Glimm", "Jaffe", "Wightman", "Osterwalder", "Schrader",
            "Coates", "Kolyvagin", "Hardy", "Odlyzko", "Perelman", "Fefferman",
            "Mayer", "Connes", "BerryKeating", "BostConnes", "Voisin",
            "Deligne", "Elliott", "Brun", "Selberg", "Mertens", "Chebyshev",
            "Leray", "Hopf", "Titchmarsh", "Bombieri", "Riemann", "Dirichlet")

REPAIR = {
    "Admitted": "a signature with no proof. Either complete it or move it to an "
                "explicitly-marked scaffold file so no capstone cites it.",
    "Abort": "an abandoned proof. Remove or mark as a recorded attempt.",
    "admit": "an admitted goal inside an otherwise complete proof -- the most "
             "easily missed escape hatch. Close the goal or lift it to a stated "
             "hypothesis.",
    "Axiom": "a declared axiom is a project-level assumption. State it as a "
             "hypothesis of the theorems that use it so it appears in their types.",
    "Parameter": "an assumed constant. If it is meant to be constructed, that "
                 "construction is the formalization work this locates.",
    "Hypothesis": "a section-level assumption silently enters every theorem in "
                  "the section. Prefer explicit binders.",
    "Conjecture": "explicit and honest; ensure no capstone treats it as proved.",
    "TRUE_BODY": "locate the intended predicate; the name records an intent the "
                 "body does not.",
    "FALSE_BODY": "a False body makes every theorem over it vacuous.",
    "UNIT_CARRIER": "unit is a placeholder domain; replace with the intended carrier.",
    "ALL_BINDERS_DEAD": "not parametric in anything it binds.",
    "EXTERNAL_NAME_TRIV": "named after published mathematics with a trivial body; "
                          "either formalize the cited statement or rename.",
    "REFLEXIVE": "an x = x conclusion carries no information.",
}

HARD = set(ESCAPES) | {"TRUE_BODY", "FALSE_BODY", "UNIT_CARRIER",
                       "ALL_BINDERS_DEAD", "EXTERNAL_NAME_TRIV", "REFLEXIVE"}


def strip_comments(s):
    """Remove nestable Coq (* ... *) comments, preserving newlines."""
    out, i, depth, n = [], 0, 0, len(s)
    while i < n:
        if s.startswith("(*", i):
            depth += 1
            i += 2
            continue
        if s.startswith("*)", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth > 0:
            if s[i] == NL:
                out.append(NL)
            i += 1
            continue
        out.append(s[i])
        i += 1
    return "".join(out), depth


DEF = re.compile(
    r"^\s*(?:Definition|Notation|Local\s+Definition)\s+"
    r"([A-Za-z_][A-Za-z0-9_" + chr(39) + r"]*)\s*(.*?):\s*Prop\s*:=\s*(.*?)\.",
    re.MULTILINE | re.DOTALL)

BINDER_NAME = re.compile(r"[({]\s*([A-Za-z_][A-Za-z0-9_" + chr(39) + r"]*)"
                         r"(?:\s+[A-Za-z_][A-Za-z0-9_" + chr(39) + r"]*)*\s*:")
REFL = re.compile(r"([A-Za-z_][A-Za-z0-9_" + chr(39) + r".]*)\s*=\s*\1$")


def norm(s):
    return " ".join(s.split()).strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ledger", action="store_true")
    a = ap.parse_args()

    files = []
    for dp, _dn, fns in os.walk(ROOT):
        for f in fns:
            if f.endswith(".v"):
                files.append(os.path.join(dp, f))
    files.sort()

    records = []
    raw_hits = Counter()
    real_hits = Counter()
    unbalanced = []
    ndef = 0
    vo_present = 0

    for full in files:
        rel = os.path.relpath(full, ROOT)
        try:
            raw = io.open(full, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        if os.path.exists(full[:-2] + ".vo"):
            vo_present += 1
        code, depth = strip_comments(raw)
        if depth != 0:
            unbalanced.append((rel, depth))

        for k, rx in ESCAPES.items():
            nraw = len(rx.findall(raw))
            nreal = len(rx.findall(code))
            raw_hits[k] += nraw
            real_hits[k] += nreal
            if nreal:
                for m in rx.finditer(code):
                    records.append((rel, code[:m.start()].count(NL) + 1,
                                    "<proof script>", k,
                                    norm(code[max(0, m.start() - 60):m.start() + 20])))

        for m in DEF.finditer(code):
            ndef += 1
            name, binders, body = m.group(1), m.group(2) or "", m.group(3) or ""
            b = norm(body)
            line = code[:m.start()].count(NL) + 1
            hits = []
            if b == "True":
                hits.append(("TRUE_BODY", "body := True"))
            if b == "False":
                hits.append(("FALSE_BODY", "body := False"))
            if re.search(r":\s*unit\b", b) or re.search(r"forall[^,]*:\s*unit\b", b):
                hits.append(("UNIT_CARRIER", b[:110]))
            if REFL.search(b):
                hits.append(("REFLEXIVE", b[:110]))
            bn = BINDER_NAME.findall(binders)
            if bn and all(x.startswith("_") for x in bn):
                hits.append(("ALL_BINDERS_DEAD", "binders: " + ",".join(bn)))
            if any(e in name for e in EXTERNAL) and b in ("True", "False"):
                hits.append(("EXTERNAL_NAME_TRIV", name + " := " + b))
            for k, d in hits:
                records.append((rel, line, name, k, d))

    if a.ledger:
        tab = chr(9)
        print(tab.join(["severity", "class", "file", "line", "declaration",
                        "detail"]))
        for rel, line, nm, k, d in sorted(records, key=lambda r: (r[0], r[1])):
            print(tab.join(["HARD" if k in HARD else "soft", k, rel, str(line),
                            nm, d[:200]]))
        return 0

    bar = "=" * 78
    print(bar)
    print("COQ HYGIENE GATE -- cross-prover confirmation surface")
    print(bar)
    print("  .v files scanned             %6d" % len(files))
    print("  .vo compiled artifacts       %6d  (%.1f%% of files)"
          % (vo_present, 100.0 * vo_present / max(1, len(files))))
    print("  Prop definitions inspected   %6d" % ndef)
    print("  findings                     %6d" % len(records))
    if unbalanced:
        print("  files with unbalanced (* *)  %6d  %s"
              % (len(unbalanced), unbalanced[:3]))
    print("")
    print("ESCAPE HATCHES -- raw grep vs comment-stripped")
    print("  %-12s %>8s %>8s" % ("class", "raw", "real") if False else
          "  %-12s %8s %8s" % ("class", "raw", "real"))
    for k in ESCAPES:
        print("  %-12s %8d %8d%s" % (k, raw_hits[k], real_hits[k],
                                     "   <-- ARTIFACT ONLY" if raw_hits[k]
                                     and not real_hits[k] else ""))
    print("")
    sem = Counter(k for _r, _l, _n, k, _d in records if k not in ESCAPES)
    if sem:
        print("SEMANTIC FINDINGS")
        for k, n in sem.most_common():
            print("  %-20s %5d" % (k, n))
        print("")
    print("DETAIL, grouped by class")
    bycls = defaultdict(list)
    for rel, line, nm, k, d in records:
        bycls[k].append((rel, line, nm, d))
    for k in sorted(bycls, key=lambda x: -len(bycls[x])):
        print("  --- %s (%d)" % (k, len(bycls[k])))
        print("      REPAIR: " + REPAIR.get(k, ""))
        for rel, line, nm, d in bycls[k][:6]:
            print("        %-58s %s:%d" % (nm[:58], rel, line))
        if len(bycls[k]) > 6:
            print("        ... %d more" % (len(bycls[k]) - 6))
    return 0


sys.exit(main())
