#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""Convert the gate sweep's module-level verdicts into a STRUCTURE-level work
estimate.

Every (d2) failure observed is a dead field on a structure, and a structure is
shared across modules -- so the number of modules failing is NOT the amount of
work. This groups the DEAD/CONTAINED/VACUOUS findings by the declaration that
owns them, so the work estimate is "how many distinct structures" rather than
"how many modules".

Safe to run against a partial, in-progress TSV: it reports how far the sweep has
got and labels the figures accordingly.

Read-only.
"""
import collections
import io
import os
import sys

TSV = ("/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/"
       "codex/PRISTINE_SWEEP_2026-10-06.tsv")
TOTAL_CLOSURE = 1452


def owner_of(decl):
    """A finding names <Namespace>.<Structure>.<field>; the owner is the
    structure, i.e. everything up to the last dot."""
    return decl.rsplit(".", 1)[0] if "." in decl else decl


def classify(decl):
    """Not every finding is a dead STRUCTURE FIELD, and the first pass over this
    data wrongly assumed they all were.

    A corpus declaration looks like `PrincipiaTractalis.Foo.Bar.field` -- three
    or more dotted parts under a project namespace. Findings reported as bare
    names (`hypothesis`, `modus`) are dead PLAIN BINDERS, and findings on mathlib
    paths (`USize.toBitVec.toFin`, `Membership.mem`, `Units`) are neither ours
    nor structure fields. Lumping all three together inflated the structure count
    and produced a leverage figure that meant nothing.
    """
    parts = decl.split(".")
    if parts[0] in ("PrincipiaTractalis", "PF"):
        return "project_field" if len(parts) >= 3 else "project_decl"
    if len(parts) == 1:
        return "bare_binder"
    return "foreign"


def main():
    if not os.path.exists(TSV):
        print("MISS: %s absent" % TSV)
        return 1
    rows = []
    for line in io.open(TSV, encoding="utf-8"):
        parts = line.rstrip("\n").split("\t")
        if len(parts) >= 3 and parts[0] != "module":
            rows.append(parts)

    verdicts = collections.Counter(r[1] for r in rows)
    done = len(rows)

    print("=" * 74)
    print("SWEEP PROGRESS: %d of %d modules gated (%.1f%%)%s"
          % (done, TOTAL_CLOSURE, 100.0 * done / TOTAL_CLOSURE,
             "  [IN PROGRESS -- figures are provisional]"
             if done < TOTAL_CLOSURE else "  [COMPLETE]"))
    print("=" * 74)
    for v, n in verdicts.most_common():
        print("  %-9s %5d   %5.1f%% of gated" % (v, n, 100.0 * n / done))
    print("")

    crit = collections.Counter()
    owners = collections.Counter()
    owner_modules = collections.defaultdict(set)
    kinds = collections.Counter()
    classes = collections.Counter()
    unparsed = 0

    for mod, verdict, detail in ((r[0], r[1], r[2]) for r in rows):
        if verdict != "FAILED":
            continue
        head, _, tail = detail.partition("|")
        if head == "unparsed":
            unparsed += 1
        for c in head.split(","):
            if c:
                crit[c] += 1
        for item in tail.split(";"):
            if not item or ":" not in item:
                continue
            kind, decl = item.split(":", 1)
            kinds[kind] += 1
            cls = classify(decl)
            classes[cls] += 1
            # Only project structure fields are repair sites we own. Bare
            # binders are per-theorem fixes, foreign paths are not ours at all.
            if cls != "project_field":
                continue
            o = owner_of(decl)
            owners[o] += 1
            owner_modules[o].add(mod)

    print("FAILING CRITERIA (a module can fail more than one)")
    for c, n in crit.most_common():
        print("  %-6s %5d modules" % (c, n))
    if unparsed:
        print("  (%d FAILED rows carried no parseable criterion)" % unparsed)
    print("")
    print("FINDING KINDS")
    for k, n in kinds.most_common():
        print("  %-10s %5d" % (k, n))
    print("")
    print("FINDING TARGETS -- not all are dead structure fields")
    labels = {
        "project_field": "project structure field  (ours; structure-level fix)",
        "project_decl": "project bare declaration (ours; per-decl fix)",
        "bare_binder": "bare binder name         (ours; per-theorem fix)",
        "foreign": "mathlib / foreign path   (NOT ours)",
    }
    for c, n in classes.most_common():
        print("  %-10s %5d   %s" % (c, n, labels.get(c, c)))
    print("")

    print("=" * 74)
    print("THE WORK ESTIMATE: %d distinct project structures own %d field findings"
          % (len(owners), sum(owners.values())))
    print("=" * 74)
    touched = set().union(*owner_modules.values()) if owner_modules else set()
    leverage = (len(touched) / len(owners)) if owners else 0.0
    print("  across %d modules, so %.2f modules clear per structure fixed"
          % (len(touched), leverage))
    if leverage < 1.5:
        print("")
        print("  *** LEVERAGE IS LOW. The earlier claim that 'one structure fixed")
        print("  *** clears every module importing it' is NOT supported: most")
        print("  *** structures are used by a single module, so the work is")
        print("  *** roughly PROPORTIONAL to the failing-module count, not")
        print("  *** amortised across it.")
    print("")
    print("  HIGHEST LEVERAGE -- structures by modules they would unblock:")
    by_leverage = sorted(owners, key=lambda o: (-len(owner_modules[o]), -owners[o]))
    for o in by_leverage[:20]:
        print("    %3d modules, %2d dead fields   %s"
              % (len(owner_modules[o]), owners[o], o))
    if len(by_leverage) > 20:
        print("    ... %d more structures" % (len(by_leverage) - 20))
    print("")
    singles = [o for o in owners if len(owner_modules[o]) == 1]
    print("  %d of %d structures affect only one module each (long tail)"
          % (len(singles), len(owners)))
    return 0


sys.exit(main())
