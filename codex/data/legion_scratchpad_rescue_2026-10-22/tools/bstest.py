#!/usr/bin/env python3
"""Measure, rather than assume, what a doubled backslash before \\subsection does.

Writes two minimal book-class documents into /tmp -- one with the defect exactly
as it appeared on ch24:599 (doubled backslash after a blank line), one with it
repaired -- and runs pdflatex on each. Touches nothing in the repo.

chr(92) throughout so no shell, heredoc or sed layer can alter the backslash
count, which is the entire subject of the test.
"""
import io
import os
import subprocess

BS = chr(92)
TMP = "/tmp/bstest"
os.makedirs(TMP, exist_ok=True)

HEAD = [
    BS + "documentclass{book}",
    BS + "begin{document}",
    BS + "chapter{Test}",
    "Some body text ending a paragraph.",
    "",            # the blank line -- this is what makes it fatal
]
TAIL = [BS + "end{document}", ""]


def build(name, heading_line):
    src = os.path.join(TMP, name + ".tex")
    io.open(src, "w", encoding="utf-8", newline="\n").write(
        "\n".join(HEAD + [heading_line] + ["", "Body of the subsection."] + TAIL))
    p = subprocess.run(
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
         "-output-directory", TMP, src],
        capture_output=True, text=True)
    out = p.stdout + p.stderr
    err = [L for L in out.split("\n") if L.startswith("!")]
    pdf = os.path.join(TMP, name + ".pdf")
    print("%-10s exit=%-3d pdf=%-5s  %s" % (
        name, p.returncode, os.path.exists(pdf),
        err[0][:70] if err else "(no ! error)"))
    # did the heading survive as a heading, or get typeset as literal prose?
    return p.returncode


print("heading line under test, byte-for-byte as ch24:599 had it:")
print("  " + BS + BS + "subsection{Example 2: Rank 1 Curve}")
print("")
build("defect", BS + BS + "subsection{Example 2: Rank 1 Curve}")
build("repaired", BS + "subsection{Example 2: Rank 1 Curve}")
