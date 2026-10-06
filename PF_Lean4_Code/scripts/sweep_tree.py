#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""Whole-tree control-byte and lost-backslash sweep, NOT just chapters/.

Why this exists: the 36-chapter sweep passed clean, and then appending to
codex/CHAPTER_AUDIT_LEDGER_2026-10-05.md revealed a 0x08 backspace at line 100
--- inside that ledger's own record of a heredoc defect, where \begin{equation}
had been written as BS + "egin{equation}". The guard's SCOPE was the gap: the
ledger is not a chapter, so no sweep had ever looked at it.

So: everything text-like in the tree, reported, nothing modified. Read-only.
"""
import io
import os
import re
import sys

ROOT = "/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE"

EXTS = (".tex", ".md", ".py", ".lean", ".sh", ".txt", ".bib", ".yml", ".yaml",
        ".json", ".toml", ".cls", ".sty")

SKIP_DIRS = (".git", ".lake", "build", "node_modules", "__pycache__",
             ".elan", "lake-packages")

# A severed command tail standing alone. See chapter_integrity_sweep.py for why
# the newline-initial ones are the only informative patterns and the rest are
# redundancy against the control-byte check.
LOST = {
    "abla": "backslash-nabla",
    "ewline": "backslash-newline",
    "ewcommand": "backslash-newcommand",
    "oindent": "backslash-noindent",
    "onumber": "backslash-nonumber",
    "otin": "backslash-notin",
    "extbf": "backslash-textbf",
    "extit": "backslash-textit",
    "exttt": "backslash-texttt",
    "extsc": "backslash-textsc",
    "extrm": "backslash-textrm",
    "mph{": "backslash-emph-brace",
    "egin{": "backslash-begin-brace",
    "rac{": "backslash-frac-brace",
}

# Files whose job is to CONTAIN these patterns as data, so hits are expected.
SELF_REFERENTIAL = ("chapter_integrity_sweep.py", "sweep_tree.py",
                    "sweep36.py")


def main():
    ctrl_findings = []
    lost_findings = []
    scanned = 0
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for fn in filenames:
            if not fn.endswith(EXTS):
                continue
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, ROOT)
            try:
                s = io.open(full, encoding="utf-8").read()
            except (UnicodeDecodeError, OSError):
                continue
            scanned += 1

            is_tab_ok = fn.endswith((".py", ".sh", ".yml", ".yaml", ".json",
                                     ".toml", ".lean"))
            for m in re.finditer(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", s):
                if m.group() == "\t" and is_tab_ok:
                    continue
                line = s[:m.start()].count("\n") + 1
                ctx = repr(s[max(0, m.start() - 45):m.start() + 30])
                ctrl_findings.append((rel, line, hex(ord(m.group())), ctx))

            if fn in SELF_REFERENTIAL:
                continue
            for tail in sorted(LOST):
                for m in re.finditer(r"(?<![A-Za-z\\])" + re.escape(tail), s):
                    line = s[:m.start()].count("\n") + 1
                    ctx = s[max(0, m.start() - 40):m.start() + 20]
                    ctx = ctx.replace("\n", "<NL>").replace("\t", "<TAB>")
                    lost_findings.append((rel, line, tail, LOST[tail], ctx))

    print("scanned %d text files under %s" % (scanned, ROOT))
    print("")
    print("=== CONTROL BYTES (%d) ===" % len(ctrl_findings))
    for rel, line, ch, ctx in ctrl_findings[:60]:
        print("  %s:%d  %s" % (rel, line, ch))
        print("      %s" % ctx)
    if len(ctrl_findings) > 60:
        print("  ... %d more" % (len(ctrl_findings) - 60))
    print("")
    print("=== LOST-BACKSLASH TAILS (%d) ===" % len(lost_findings))
    for rel, line, tail, proper, ctx in lost_findings[:60]:
        print("  %s:%d  '%s' (should be %s)" % (rel, line, tail, proper))
        print("      ...%s..." % ctx)
    if len(lost_findings) > 60:
        print("  ... %d more" % (len(lost_findings) - 60))
    print("")
    if not ctrl_findings and not lost_findings:
        print("TREE CLEAN")
        return 0
    print("TOTAL: %d control bytes, %d lost-backslash tails"
          % (len(ctrl_findings), len(lost_findings)))
    return 3


sys.exit(main())
