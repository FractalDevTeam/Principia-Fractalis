#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""36-chapter verification sweep, run BACKWARDS over everything already touched.

The ch34A lesson: five \textbf were written as TAB+"extbf" by a non-raw heredoc
and survived every environment and brace guard, because those guards check
structure and a lost backslash is not a structural error. A guard added
mid-campaign must therefore be run retrospectively over the whole corpus, not
only forward on new patches.

AND THE GUARD SCRIPT ITSELF WAS HIT BY THE SAME DEFECT, 2026-10-06, while being
edited: an unquoted heredoc used to patch this table turned the \n in "\nabla"
into a literal newline and the \t in "\textbf" into a TAB, splitting the
dictionary across lines and breaking the parse. Caught by the Python parser, not
by reading. The rule it violated was already on the books -- ship patches as
files, never inline through a heredoc -- which is the point: the defect class
does not care that you are writing the detector for it.

Checks per chapter:
  1. control bytes (anything < 0x20 other than newline)
  2. environment balance over the environments actually used
  3. brace delta
  4. empty math environments
  5. LOST-BACKSLASH COMMANDS -- a command tail standing alone, i.e. not preceded
     by its own letter or by a backslash.

On check 5's scope, which the first run of this script established. A non-raw
heredoc turns a backslash-escape into its control character, consuming the
backslash AND the next letter. Every such escape leaves a control byte that
check 1 reports -- EXCEPT the newline escape, because a newline is legal and
check 1 must permit it. So the commands beginning with that letter are the one
class the control-byte guard structurally cannot see, and they are the only
patterns below that add information; the rest are redundancy. The first run also
produced eighteen false positives from the English word "angle", which is
removed: its severed form would leave a carriage return, and check 1 reports
zero of those across all thirty-six chapters.
"""
import glob
import io
import os
import re
import sys

D = ("/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/"
     "Principia_Fractalis_master_folder/chapters")

ENVS = ("equation", "align", "itemize", "enumerate", "theorem", "lemma",
        "proof", "remark", "definition", "proposition", "example", "center",
        "tabular", "table", "figure", "corollary", "thm", "level1", "level2",
        "level3", "abstract", "quote", "verbatim", "cases", "pmatrix",
        "bmatrix", "array", "description", "equation*", "align*")

# Severed tail -> the command it came from. Written with doubled backslashes in
# ordinary strings so that no escape can be interpreted by anything upstream.
LOST = {
    # THE REAL RESIDUAL GAP: newline-initial commands (see module docstring).
    "abla": "backslash-nabla",
    "ewline": "backslash-newline",
    "ewcommand": "backslash-newcommand",
    "oindent": "backslash-noindent",
    "onumber": "backslash-nonumber",
    "otin": "backslash-notin",
    # Redundant with check 1, kept as belt-and-braces. Zero-noise tails only.
    "extbf": "backslash-textbf",
    "extit": "backslash-textit",
    "exttt": "backslash-texttt",
    "extsc": "backslash-textsc",
    "extrm": "backslash-textrm",
    "mph{": "backslash-emph-brace",
    "egin{": "backslash-begin-brace",
    "rac{": "backslash-frac-brace",
    # DROPPED as pure noise, with reasons: "angle" (the English word, 18 false
    # positives; its severed form leaves a CR, which check 1 covers and found
    # zero of); "ambda", "imes", "nfty" (their severed forms retain a letter
    # prefix, so this pattern can never fire on the actual defect); "ext{" and
    # "nd{" (subsumed by check 1, and backslash-text-brace is ubiquitous).
}


def main():
    files = sorted(glob.glob(os.path.join(D, "ch*.tex")))
    if not files:
        print("MISS: no chapters found at %s" % D)
        return 1
    bad_total = 0
    ctrl_total = 0
    brace_total = 0
    env_total = 0
    empty_total = 0
    lost_total = 0

    for f in files:
        name = os.path.basename(f)
        s = io.open(f, encoding="utf-8").read()
        probs = []

        ctrl = [c for c in s if ord(c) < 32 and c != "\n"]
        if ctrl:
            probs.append("CONTROL BYTES: %d (%s)"
                         % (len(ctrl), sorted(set(hex(ord(c)) for c in ctrl))))
            ctrl_total += len(ctrl)

        for env in ENVS:
            e = re.escape(env)
            nb = len(re.findall(r"\\begin\{" + e + r"\}", s))
            ne = len(re.findall(r"\\end\{" + e + r"\}", s))
            if nb != ne:
                probs.append("ENV %s unbalanced %d/%d" % (env, nb, ne))
                env_total += 1

        if s.count("{") != s.count("}"):
            probs.append("BRACES %d/%d (delta %d)"
                         % (s.count("{"), s.count("}"),
                            s.count("{") - s.count("}")))
            brace_total += 1

        em = re.findall(
            r"\\begin\{(equation|align)\*?\}\s*\\end\{(equation|align)\*?\}", s)
        if em:
            probs.append("EMPTY MATH ENV: %d" % len(em))
            empty_total += len(em)

        for tail in sorted(LOST):
            pat = r"(?<![A-Za-z\\])" + re.escape(tail)
            hits = list(re.finditer(pat, s))
            if hits:
                ctx = s[max(0, hits[0].start() - 25):hits[0].start() + 12]
                ctx = ctx.replace("\n", "<NL>")
                probs.append(
                    "LOST BACKSLASH: %d x '%s' (should be %s) first: ...%s..."
                    % (len(hits), tail, LOST[tail], ctx))
                lost_total += len(hits)

        if probs:
            bad_total += 1
            print("FAIL  %s" % name)
            for p in probs:
                print("        %s" % p)

    print("")
    print("swept %d chapters: %d with findings" % (len(files), bad_total))
    print("  control bytes        %d" % ctrl_total)
    print("  unbalanced envs      %d" % env_total)
    print("  brace deltas         %d" % brace_total)
    print("  empty math envs      %d" % empty_total)
    print("  lost-backslash hits  %d" % lost_total)
    if bad_total == 0:
        print("ALL %d CHAPTERS VERIFY" % len(files))
        return 0
    return 3


sys.exit(main())
