#!/usr/bin/env python3
"""Find doubled-backslash control sequences in LaTeX.

A doubled backslash followed by a LETTER is never a line break. In LaTeX `\\`
ends a line (legitimately followed by end-of-line or by `[2mm]`-style spacing),
so `\\subsection{X}` emits a line break and then typesets the literal text
`subsection{X}` -- the heading silently DISAPPEARS and shows up as body prose.

Built with chr(92) rather than escapes because this is exactly the class of bug
that a backslash-eating heredoc or sed round introduces, and I am not going to
write the detector in the notation that causes it.
"""
import io
import sys

BS = chr(92)
DOUBLE = BS + BS
LETTERS = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")

bad = 0
for fn in sys.argv[1:]:
    text = io.open(fn, encoding="utf-8").read()
    for i, line in enumerate(text.split("\n"), 1):
        j = 0
        while True:
            j = line.find(DOUBLE, j)
            if j < 0:
                break
            # a run of exactly two backslashes, followed by a letter
            run_start = j
            while run_start > 0 and line[run_start - 1] == BS:
                run_start -= 1
            run_end = j
            while run_end < len(line) and line[run_end] == BS:
                run_end += 1
            nbs = run_end - run_start
            nxt = line[run_end] if run_end < len(line) else ""
            if nbs == 2 and nxt in LETTERS:
                bad += 1
                shown = line.strip()[:140].encode("ascii", "replace").decode()
                print("%s:%d: %s" % (fn, i, shown))
            j = run_end

print("")
print("%d doubled-backslash-before-letter occurrence(s)" % bad)
sys.exit(1 if bad else 0)
