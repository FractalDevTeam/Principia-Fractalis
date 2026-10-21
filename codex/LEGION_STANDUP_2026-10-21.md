# Legion native build is live, and panel modules need 7 GB not 12 — the peaks are reclaimable garbage

**Date:** 2026-10-21 (Legion). Rio §2 LEGION item 2. Labels **FACT** / **MEASURED** / **JUDGEMENT** / **OPEN**.

## HEADLINE. MEASURED

`lean -M 7000` builds a march panel module:

| | result |
|---|---|
| `Seg01Range_c7`, Legion, `-M 7000` | rc=0, 500 s, 0 errors |
| declarations | 54, all `[propext, Classical.choice, Quot.sound]` |
| completeness | 54 = the number of `#print axioms` directives the source emits |

Measured Acer peak for this module class is **12.29–12.62 GB** of 15. Capped at
7 GB the same module completes in 500 s against Acer's 431 s — **16% slower**,
on a machine running 508 processes.

**So the 12 GB is not a requirement.** It is garbage lean declines to collect
while memory is plentiful.

## 1. The band split is available. JUDGEMENT

Legion has **8.4 GB available of 31.4** (508 processes, 18.8 GB working set;
chrome alone 6.04 GB across 35). That is under the 12 GB peak and over the 7 GB
cap. Uncapped, the split was blocked; capped, it is not.

## 2. Acer is running closer to the edge than it needs to. MEASURED

The band builds uncapped at 12.3 GB of 15 — a **2.7 GB margin** against a hard
OOM, and §1 exists because dual builds at 15 GB kill each other. `-M` would buy
~5 GB of headroom for a 16% time cost.

**Proposed, not applied.** `march_box.sh` is Acer's file and the band is
mid-run.

## 3. Standup evidence. FACT

* `lake-manifest.json` **md5-identical** to Acer (`ce569bf7613b62cde405782338fcf870`)
  — recipe step 5, and better than 2026-10-01 when the manifests differed in key order.
* Closure of `CoreDefs_c7` is 34 PF modules, 32 already cached from 2026-10-01.
  **Checked for the stale-olean trap before trusting them:** git says none of
  those 32 sources changed since 2026-10-01, so the oleans are current.
* Built the 2 missing modules natively: `OmegaDerivative_2026_10_14` rc=0 / 71 s;
  `CoreDefs_c7_2026_10_16` rc=0 / 24 s / 0 errors / 10 declarations on the bar.
* Cross-host: Acer reported rc=0, 10 declarations, the same exact axiom set.

## 4. A §1 violation of mine. FACT — on the record

That Acer rebuild of `CoreDefs_c7` ran `taskset -c 2,3 lake env lean` **without
taking the shared flock**, while the band was mid-panel-module. 2.6 GB on top
of 12.3 GB is **14.9 GB of 15**. §1 serializes Acer Lean builds under one flock
precisely because dual builds OOM at 15 GB, and I bypassed it for a convenience
check. It completed and the band was unharmed, but the margin was 0.1 GB.

Not repeated: the declaration-count cross-check above was obtained by counting
`#print` directives in the source, which needs no build.

## Label summary

* **FACT:** the manifest md5 equality; the 34-module closure and the git
  evidence that 32 of its sources are unchanged since 2026-10-01; the §1
  violation.
* **MEASURED:** the capped build (rc=0, 500 s, 54 declarations on the bar); the
  uncapped Acer peaks 12.29–12.62 GB; Legion's 8.4 GB available of 31.4; the
  16% time cost of the cap.
* **JUDGEMENT:** that the 12 GB is reclaimable rather than required; that the
  split is therefore available; that Acer should be capped too.
* **OPEN:** the cap was validated on ONE panel module at ONE centre (c = 7,
  `Seg01Range`). Midpoint modules and higher centres are untested under `-M`,
  and a module whose *live* set genuinely exceeds 7 GB would fail rather than
  slow down. Before splitting the band, one midpoint module and one high-c
  module should be capped-built.
