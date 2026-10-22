#!/usr/bin/env python3
"""Check Lean block-comment nesting before paying another lock wait.

Lean block comments NEST: an inner `/-` inside a comment opens a new level, so
prose that quotes a comment-opening token silently swallows the closing `-/`.
That is the bug this catches -- it cost one 7-minute lock acquisition.

Walks the file tracking depth, ignoring `--` line comments (outside a block) and
string literals, and reports the final depth plus the line of any unbalanced
opener.
"""
import io
import sys

path = sys.argv[1]
src = io.open(path, encoding="utf-8").read()

depth = 0
opens = []          # stack of line numbers
line = 1
i = 0
n = len(src)
in_str = False

while i < n:
    c = src[i]
    nxt = src[i + 1] if i + 1 < n else ""
    if c == "\n":
        line += 1
        i += 1
        continue
    if depth == 0 and not in_str and c == '"':
        in_str = True
        i += 1
        continue
    if in_str:
        if c == "\\":
            i += 2
            continue
        if c == '"':
            in_str = False
        i += 1
        continue
    if c == "/" and nxt == "-":
        depth += 1
        opens.append(line)
        i += 2
        continue
    if c == "-" and nxt == "/":
        if depth == 0:
            print("line %d: stray closer -/ with no open comment" % line)
            sys.exit(1)
        depth -= 1
        opens.pop()
        i += 2
        continue
    if depth == 0 and c == "-" and nxt == "-":
        while i < n and src[i] != "\n":
            i += 1
        continue
    i += 1

print("%s: %d lines, final block-comment depth = %d" % (
    path, src.count("\n") + 1, depth))
if depth != 0:
    print("UNBALANCED -- comment opened at line(s): %s" % opens)
    sys.exit(1)
print("comment nesting balanced")
