#!/usr/bin/env python3
"""Prove fixture F5 discriminates: revert ONLY the parser to the buggy form in
a throwaway copy and confirm F5 then gets the WRONG verdict.

A fixture that is only rejected because the parser is correct proves nothing
unless we also show it is ACCEPTED when the parser is wrong. Without this step
F5 would be another test that passes for the wrong reason.

Built with chr(39)/chr(92) so no shell or heredoc layer can alter the quoting,
which is exactly what defeated the first attempt at this probe.
"""
import io
import os
import shutil
import sys

Q = chr(39)       # '
BS = chr(92)      # \

SRC = ("/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/codex/"
       "ci_gate_selftest.sh")
DST = "/tmp/buggy_probe.sh"

# REC = re.compile(r"'([^\n]+)' depends on axioms:\s*\[(.*?)\]", re.DOTALL)
FIXED = ('REC = re.compile(r"' + Q + '([^' + BS + 'n]+)' + Q +
         ' depends on axioms:' + BS + 's*' + BS + '[(.*?)' + BS + ']", '
         're.DOTALL)')
# the pre-fix form, which stops at a prime inside the name
BUGGY = ('REC = re.compile(r"' + Q + '([^' + Q + ']+)' + Q +
         ' depends on axioms:' + BS + 's*' + BS + '[(.*?)' + BS + ']", '
         're.DOTALL)')

text = io.open(SRC, encoding="utf-8").read()
if text.count(FIXED) != 1:
    print("REFUSING: fixed-parser anchor found %d times (expected 1)"
          % text.count(FIXED))
    print("  looking for: %s" % FIXED)
    sys.exit(1)

io.open(DST, "w", encoding="utf-8", newline="\n").write(
    text.replace(FIXED, BUGGY, 1))
shutil.copymode(SRC, DST)
print("probe written to %s with the parser reverted to the buggy form" % DST)
print("  verify: buggy present=%s  fixed absent=%s" % (
    io.open(DST, encoding="utf-8").read().count(BUGGY) == 1,
    io.open(DST, encoding="utf-8").read().count(FIXED) == 0))
