#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""Audit every LaTeX chapter for unbalanced environments and stray control bytes.

Written after two self-inflicted defects on 2026-10-03/04 that per-file spot
checks would not have caught on their own:

  * a non-raw heredoc string embedded literal TAB and BELL bytes in ch28 and
    mangled \noindent -> oindent, \textbf -> extbf;
  * a repair in ch25 opened a `remark` environment and never closed it.

Environment counts alone caught the second and missed the first; a control-byte
scan catches the first. Both checks are cheap, so run both over the whole corpus
after any edit pass.

Usage:
  tex_env_balance.py [chapters-dir]

Exit status is non-zero if anything is unbalanced or any control byte is found,
so this can gate a commit.
"""
import io
import os
import re
import sys

DEFAULT_DIR = "Principia_Fractalis_master_folder/chapters"

# Environments that must balance. Deliberately broad: a name that never appears
# contributes 0/0 and is silently fine.
ENVS = [
    "abstract", "advanced", "align", "align*", "cases", "center", "chapterobjectives",
    "corollary", "defn", "definition", "description", "enumerate", "equation",
    "equation*", "example", "figure", "gather", "greenbox", "intuitive", "itemize",
    "keyidea", "lemma", "level1", "level2", "level3", "manuscriptcorrection",
    "pmatrix", "proof", "proposition", "quote", "remark", "table", "tabular",
    "theorem", "thm", "verbatim",
]


def scan(path):
    """Return (list of (env, nbegin, nend) that disagree, list of control bytes)."""
    text = io.open(path, encoding="utf-8", errors="replace").read()
    problems = []
    for env in ENVS:
        esc = re.escape(env)
        nb = len(re.findall(r"\\begin\{" + esc + r"\}", text))
        ne = len(re.findall(r"\\end\{" + esc + r"\}", text))
        if nb != ne:
            problems.append((env, nb, ne))
    ctrl = [(i, repr(c)) for i, c in enumerate(text) if ord(c) < 32 and c != "\n"]
    return problems, ctrl


def main():
    base = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_DIR
    if not os.path.isdir(base):
        sys.stderr.write("not a directory: %s\n" % base)
        return 2

    files = sorted(
        os.path.join(base, n) for n in os.listdir(base) if n.endswith(".tex")
    )
    if not files:
        sys.stderr.write("no .tex files in %s\n" % base)
        return 2

    bad_env = 0
    bad_ctrl = 0
    for path in files:
        problems, ctrl = scan(path)
        name = os.path.basename(path)
        for env, nb, ne in problems:
            print("  UNBALANCED  %-38s %-24s %d begin / %d end" % (name, env, nb, ne))
            bad_env += 1
        if ctrl:
            print("  CONTROL     %-38s %d byte(s), first: %s"
                  % (name, len(ctrl), ctrl[:3]))
            bad_ctrl += 1

    print()
    print("files scanned:                %d" % len(files))
    print("unbalanced (file, env) pairs: %d" % bad_env)
    print("files with control bytes:     %d" % bad_ctrl)
    ok = (bad_env == 0 and bad_ctrl == 0)
    print("RESULT: %s" % ("CLEAN" if ok else "DEFECTS FOUND"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
