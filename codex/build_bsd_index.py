#!/usr/bin/env python3
"""BSD lane evidence index: theorem -> commit -> where its axiom output lives.

Companion to codex/build_evidence_index.py (Riemann lane), for Rio's P8.

Scope rule: a declaration is listed only if the file carries a `#print axioms`
line naming it. That is the corpus's own marker for "this is a load-bearing
claim whose axiom set was checked", so the index inherits the corpus's own
judgement rather than mine about what counts.

As with the Riemann index, the axiom OUTPUT is not in the tree -- it prints at
build time. Each row therefore says where the output is recorded, if anywhere:
the status board, a commit message, or nowhere (in which case it needs a
rebuild, and that is stated).
"""
import re
import subprocess

REPO = "/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE"
BSD_HINTS = ("Duplication", "NaiveHeight", "MordellWeil", "RankOne",
             "NonTorsion", "Parallelogram", "CanonicalHeight", "Secant",
             "RankPipeline", "Canheight", "BiAdditive", "E91a1", "E43a1",
             "E37a1", "E389a1", "E5077a1", "QuasiParallelogram")


def git(a):
    return subprocess.run(["git"] + a, cwd=REPO, capture_output=True,
                          text=True, encoding="utf-8", errors="replace").stdout


files = [f for f in git(["ls-files", "PF_Lean4_Code/PF/"]).split("\n")
         if f.endswith(".lean") and any(h in f for h in BSD_HINTS)]

board = git(["show", "HEAD:codex/status/legion.md"])

rows = []
for path in files:
    body = git(["show", "HEAD:%s" % path])
    decls = re.findall(r"#print axioms\s+([A-Za-z0-9_.']+)", body)
    if not decls:
        continue
    log = git(["log", "--format=%h", "-1", "--", path]).strip()
    msg = git(["log", "--format=%B", "-1", "--", path])
    short = [d.split(".")[-1] for d in decls]
    # where is the axiom output recorded?
    where = []
    if any(("%s " % s) in board or ("`%s`" % s) in board or
           ("%s  " % s) in board for s in short):
        where.append("status board")
    if "propext" in msg:
        where.append("commit message")
    rows.append((path.split("/")[-1], len(decls), log,
                 ", ".join(where) if where else "NOWHERE (needs rebuild)",
                 short))

rows.sort(key=lambda r: r[0])
print("# BSD lane — evidence index (theorem → commit → axiom output location)")
print("")
print("%d files carry `#print axioms` on %d declarations."
      % (len(rows), sum(r[1] for r in rows)))
print("")
print("| file | axiom-checked decls | commit | axiom output recorded |")
print("|---|---|---|---|")
for fn, n, sha, where, _ in rows:
    print("| `%s` | %d | `%s` | %s | " % (fn, n, sha, where))
print("")
nowhere = [r for r in rows if r[3].startswith("NOWHERE")]
print("Axiom output recorded somewhere: **%d of %d files**."
      % (len(rows) - len(nowhere), len(rows)))
if nowhere:
    print("")
    print("Needs a rebuild to produce its axiom output (%d):" % len(nowhere))
    for fn, n, sha, _w, _d in nowhere:
        print("- `%s` (%d decls, `%s`)" % (fn, n, sha))
