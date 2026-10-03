#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Emit the fully-qualified name of every PROBEABLE theorem/lemma in a Lean file.

Background. The pristine gate probes axioms by generating `#print axioms <name>`.
It used to emit BARE names under a single `open` built by pasting every
`namespace` line into one dotted path; for nested namespaces that path names only
the innermost scope, so declarations in outer namespaces never resolved and
produced no axiom record, while the PASS line still cited the full declaration
count. `sort -u` on bare names additionally collapsed distinct declarations that
share a short name across namespaces.

Measured 2026-10-02 on PF/GaussLowerBound_r209.lean: 88 bare names -> 3 records;
93 qualified names -> 93 records, zero errors.

Two things are deliberately excluded from the output:

  * `private` declarations. Lean mangles these to
    `_private.<Module>.0.<Namespace>.<name>`, so `#print axioms` cannot resolve
    the plain qualified name. This is not a coverage hole: a private lemma's
    axioms appear in the dependency closure of every public declaration that
    uses it, and `#print axioms` on a public theorem reports that whole closure.
    Use --private-count to report how many were excluded, so the gate's coverage
    arithmetic stays truthful.

  * anything inside a comment. Comments are stripped here rather than trusting
    the caller, because Lean doc comments (`/-- ... -/`) routinely contain prose
    like "lemma is a direct projection", which a line regex happily reads as a
    declaration named `is` (PF/SubstrateRigidity.lean:1929).

Usage:
  qualified_decls.py <source.lean>                  -> probeable qualified names
  qualified_decls.py <source.lean> --private-count  -> count of private decls
"""
import io
import re
import sys

IDENT = r"[A-Za-z_À-￿][A-Za-z0-9_'!?À-￿]*"
DOTTED = IDENT + r"(?:\." + IDENT + r")*"

# A declaration line: optional attributes, optional modifiers, keyword, name.
# The name must be followed by a binder opener, type ascription, or line end --
# prose such as "lemma is a direct ..." is therefore not a declaration.
DECL = re.compile(
    r"^[ \t]*"
    r"(?:@\[[^\]]*\][ \t]*)*"
    r"(?P<mods>(?:(?:private|protected|nonrec|noncomputable)[ \t]+)*)"
    r"(?:theorem|lemma)[ \t]+"
    r"(?P<name>" + DOTTED + r")"
    r"(?=[ \t]*(?:$|[\(\{\[:<>⦃⟨{]|\.\.\.|\{))"
)
NAMESPACE = re.compile(r"^[ \t]*namespace[ \t]+(" + DOTTED + r")[ \t]*$")
SECTION = re.compile(r"^[ \t]*section(?:[ \t]+\S+)?[ \t]*$")
END = re.compile(r"^[ \t]*end(?:[ \t]+\S+)?[ \t]*$")


def strip_comments(text: str) -> str:
    """Remove Lean line and (nesting) block comments, preserving line structure."""
    out = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        ch = text[i]
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            continue
        if ch == '"':
            out.append(ch)
            i += 1
            while i < n:
                if text[i] == "\\" and i + 1 < n:
                    out.append("  ")
                    i += 2
                    continue
                out.append(text[i])
                if text[i] == '"':
                    i += 1
                    break
                i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def scan(path):
    with io.open(path, encoding="utf-8", errors="replace") as fh:
        src = strip_comments(fh.read())

    stack = []          # frames: ("ns", [components]) | ("sec", [])
    names, private = [], 0

    for line in src.splitlines():
        m = NAMESPACE.match(line)
        if m:
            stack.append(("ns", m.group(1).split(".")))
            continue
        if SECTION.match(line):
            stack.append(("sec", []))
            continue
        if END.match(line):
            if stack:
                stack.pop()
            continue
        m = DECL.match(line)
        if m:
            if "private" in m.group("mods"):
                private += 1
                continue
            prefix = []
            for kind, comps in stack:
                if kind == "ns":
                    prefix.extend(comps)
            names.append(".".join(prefix + [m.group("name")]) if prefix else m.group("name"))

    seen, uniq = set(), []
    for nm in names:
        if nm not in seen:
            seen.add(nm)
            uniq.append(nm)
    return uniq, private


def main() -> int:
    if len(sys.argv) < 2:
        sys.stderr.write("usage: qualified_decls.py <source.lean> [--private-count]\n")
        return 2
    names, private = scan(sys.argv[1])
    if "--private-count" in sys.argv[2:]:
        print(private)
    else:
        for nm in names:
            print(nm)
    return 0


if __name__ == "__main__":
    sys.exit(main())
