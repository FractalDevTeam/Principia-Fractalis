#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Measure how much of the corpus the PRE-2026-10-02 pristine gate actually
inspected under criterion (b), without running Lean.

Criterion (b) used to enumerate declarations by

    grep -nE '^[[:space:]]*(theorem|lemma)[[:space:]]+[A-Za-z_]' | sed ... | sort -u

and then probe those BARE names under a single `open` built by pasting every
`namespace` line into one dotted path. Three independent losses followed:

  1. the bare pattern misses declarations carrying attributes or modifiers
     (`@[simp] lemma`, `private theorem`, `protected`, `nonrec`);
  2. `sort -u` merges distinct declarations that share a short name across
     namespaces;
  3. for a file with more than one `namespace` line the pasted path names only
     the INNERMOST scope, and `open A.B.C` does not open `A.B`, so declarations
     in outer namespaces resolved to nothing and produced no axiom record --
     while the PASS line still cited the full declaration count.

This script quantifies 1+2 (declarations the old enumeration never saw) and 3
(modules where the surviving names could not resolve), over every built,
panel-free module in a tree. It is pure text analysis: no Lean, seconds to run.

Usage: gate_coverage_delta.py <tree-root>
"""
import importlib.util
import io
import os
import re
import sys

BARE = re.compile(r"^[ \t]*(?:theorem|lemma)[ \t]+([A-Za-z_][A-Za-z0-9_']*)")
NS = re.compile(r"^[ \t]*namespace[ \t]+\S+", re.M)
SKIP = re.compile(r"panel|Seg\d|Numerics", re.I)


def load_qualifier(root):
    path = os.path.join(root, "scripts", "lib", "qualified_decls.py")
    spec = importlib.util.spec_from_file_location("qd", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def built_sources(root):
    lib = os.path.join(root, ".lake", "build", "lib", "lean")
    base = os.path.join(lib, "PF")
    out = []
    for dirpath, _, names in os.walk(base):
        for name in names:
            if not name.endswith(".olean"):
                continue
            rel = os.path.relpath(os.path.join(dirpath, name), lib)
            if SKIP.search(rel):
                continue
            out.append(rel[:-6] + ".lean")
    return out


def main():
    if len(sys.argv) < 2:
        sys.stderr.write("usage: gate_coverage_delta.py <tree-root>\n")
        return 2
    root = sys.argv[1]
    qd = load_qualifier(root)

    rows = []
    for rel in built_sources(root):
        src = os.path.join(root, rel)
        if not os.path.isfile(src):
            continue
        text = io.open(src, encoding="utf-8", errors="replace").read()
        bare = {m.group(1) for m in (BARE.match(l) for l in text.splitlines()) if m}
        try:
            qual, priv = qd.scan(src)
        except Exception:
            continue
        rows.append({
            "mod": rel,
            "ns": len(NS.findall(text)),
            "bare": len(bare),
            "present": len(qual) + priv,
        })

    multi = [r for r in rows if r["ns"] > 1]
    missed = [r for r in rows if r["present"] - r["bare"] > 0]
    tot_present = sum(r["present"] for r in rows)
    tot_bare = sum(r["bare"] for r in rows)

    print("built panel-free modules examined: %d" % len(rows))
    print()
    print("(3) >1 namespace line, so surviving bare names could not resolve:")
    print("      %d modules (%.1f%%)" % (len(multi), 100.0 * len(multi) / max(len(rows), 1)))
    print("(1+2) declarations the old enumeration never saw at all:")
    print("      %d modules (%.1f%%)" % (len(missed), 100.0 * len(missed) / max(len(rows), 1)))
    print()
    print("declarations present:              %d" % tot_present)
    print("declarations old gate would probe: %d" % tot_bare)
    print("never probed:                      %d  (%.1f%%)"
          % (tot_present - tot_bare, 100.0 * (tot_present - tot_bare) / max(tot_present, 1)))
    print()
    print("worst modules by unseen declarations:")
    for r in sorted(rows, key=lambda x: -(x["present"] - x["bare"]))[:12]:
        gap = r["present"] - r["bare"]
        if gap <= 0:
            break
        print("   %-58s present=%-4d probed=%-4d unseen=%-4d  (%.0f%% coverage)"
              % (r["mod"], r["present"], r["bare"], gap,
                 100.0 * r["bare"] / max(r["present"], 1)))
    print()
    print("deepest namespace nesting:")
    for r in sorted(multi, key=lambda x: -x["ns"])[:8]:
        print("   ns=%-3d %s" % (r["ns"], r["mod"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
