# LEGION — status

**Updated:** 2026-10-21 evening · **Owner:** Legion session (march ownership, pipeline, research)

## Current task

Driving the D=1 band to the c=10 stop (Rio, evening). Two script fixes are
staged for **the stop, not before**. BSD gap-curve **pre-flight is below and
complete**; no proof code written yet.

## In flight

* **D=1 band**, `codex/march_run.sh` on Acer. 24 boxes landed, frontier
  **9.8125**; building **c=39/4** (Seg01Midpoint done 18:29, ~20 min left).
  Then **79/8**, then **c=10** → stop at frontier 10.0625.
  Untracked `_c39_4_` files in `PF/Analytic/` are that in-flight box —
  **`commit_box.sh` adds them; no other session should.**
* Nothing of mine building on Legion.

## Staged for the band stop — one commit, then push immediately

Per Rio: scripts do not change mid-flight.

1. **`march_box.sh`: `flock -n` → blocking `flock -w <timeout>`**, matching
   Acer's `-x` convention. My diagnosis confirmed: the fail-fast `-n` in the box
   script is the layer that turned contention into a stop. The `march_run.sh`
   retry (`5c48f698`) stays as belt-and-braces.
2. **`march_box.sh`: add `-M 7000`** to its `lake env lean` calls. Basis:
   capped panel builds measured 54/54 and 4/4 declarations on the three-axiom
   bar; the band runs at **12.3 GB of 15**; the cap costs ~16% on range modules
   and **nothing** on midpoint (449 s capped vs ~461 s uncapped).

`march_box.sh` is Acer's file — Rio ruled both changes mine to make at the stop.

## BSD gap-curve PRE-FLIGHT — complete, no proof code written

### Curve: **91a1**, `y² + y = x³ + x`, `(a₁..a₆) = (0,0,1,1,0)`, `P = (0,0)`

**102a1 is excluded, not a free choice** — two in-tree records flag rational
2-torsion at `x = 0` breaking the pipeline (`BSD_91A1_SPEC_2026-10-19` §1.3).

### Cheap falsification step — RUN, all five checks pass

| check | result |
|---|---|
| `Disc = −91` from `b₂,b₄,b₆,b₈ = 0,2,1,−1` | **OK** |
| b-relation `b₂b₆ − b₄² = 4b₈` | **OK** (−4 = −4) |
| `P = (0,0)` on the curve | **OK** |
| `−P = (0,−1) ≠ P` ⇒ not 2-torsion | **OK** |
| `2ⁿP` for n = 1…5 all on curve, no `O` | **OK**, `x`-heights 1 → 9 → 8845 → 6.09e15 → **1.24e60** |

The height growth (roughly squaring per doubling) is exactly the premise the
duplication window supplies. Nothing here is taken from the spec file; it was
recomputed.

### Route: **(b), the universal instantiation — NOT the ~800-line route**

The repo's own `BSD_91A1_SPEC_2026-10-19` §3–4 priced both and recommended (b):

| # | item | size |
|---|---|---|
| 1 | **`window ⇒ ¬IsOfFinAddOrder`, universal** — lift `E43a1RankOne_r135:777–789` off 43a1's constants. **This is the whole gap.** | ~80–150 L |
| 2 | `b_relation_91a1`, `disc_91a1` (both `decide`/`norm_num`, verified above) | ~15 L |
| 3 | `E_91a1_rank_ge_one` via `mordellWeil_rank_ge_one` | ~20 L |
| | total | **~120–200 L** |

Route (a) is the ~800-line longhand in Rio's note. I am **not** taking it: it is
the *twelfth* hand-written copy of a shape already written eleven times, and it
leaves 131a1/141a1 as expensive as they are today. After item 1, each remaining
gap curve is items 2+3 ≈ **35 lines**.

### Load-bearing facts, all present in-tree

* `PF/DuplicationHeightUniversal_r176.lean` — the universal height window; its
  own comment says it applies "with no curve-specific input whatsoever", and
  `window_389a1` is four lines.
* `PF/E43a1RankOne_r135.lean:777–789` — the non-torsion argument to lift. Uses
  only `pts n = 2ⁿ • P`, the window's growth, and mathlib's
  `IsOfFinAddOrder.finite_zmultiples`. ~60 of E43a1's 815 lines; **the only part
  never universalised**.
* `MordellWeilRankLowerBound_r129.mordellWeil_rank_ge_one` — two live consumers
  (`Ch24CurveANonTorsion_2026_10_15:492`, `Ch24CurveARankGeOne_2026_10_15:236`).
* mathlib at the pin has **no `L(E,s)`**, so nothing here touches analytic rank.

### Divergence from the instruction, stated before starting

Rio's note says "~800-line 2-descent route to **an exact rank statement**".
Three things in the repo's own adjudication cut against that, and I am not
silently reconciling them:

1. **The target cannot be an exact rank on 91a1 by this route.** What routes
   (a) and (b) both deliver is `1 ≤ Module.rank ℤ E.toAffine.Point` — a **lower**
   bound from a non-torsion point. `rank = 0` is **false** for all four gap
   curves (they are rank ≥ 1).
2. **"2-descent" names a different object here.** The in-tree 2-descent chain
   (`5ea7e0e9`+`4028e3c0`+`3e58279d`, on `y² = x³ + x`) is an **upper** bound
   proving rank 0 — opposite direction, disjoint machinery from the height
   descent used for lower bounds.
3. **An exact rank needs the upper bound, and 91a1 is the wrong curve for it.**
   `BSD_SCOPING…_2026-10-17:190` concludes a first upper bound "should be
   attempted on a newly chosen curve with rational 2-torsion". 2-Selmer
   finiteness is the route (`rank ≤ dim_F₂ Sel₂ − dim_F₂ E(ℚ)[2]`), and it has
   never been walked in this tree.

**What I will build, absent a contrary ruling:** items 1–3 above, target
`1 ≤ Module.rank ℤ E_91a1.toAffine.Point`, kernel-clean on the three-axiom bar.
That is a genuine new theorem and it makes the remaining gap curves cheap. It is
**not** an exact rank statement, and I will not label it one. If an exact rank
is the actual requirement, that is a different build on a different curve and I
need that ruling first.

Builds on Legion natively (verify tree manifest md5-matches Acer's
`ce569bf7…`); touches neither Acer's flock nor the march. Pauses if the D=2
decisions land.

## Blocked on Pablo

* **`--extend-midpoint` on/off for D ≥ 2**, and **safety 1.25× vs 1.0×**. Rio
  recommends extend ON + 1.25×. Measured: default boundary **does not reach 13
  under any safety factor** (stops 12.906250); extend+1.0× = 225.3 h,
  extend+1.25× = 287.5 h, default+1.0× = 397.8 h. No D=2 boxes emitted until
  these land (Rio: emitting early manufactures rework).

## Lanes / do-not-touch

* `PF/Analytic/TransferOperator.lean` — three docstrings (1244, 3050, 3854) call
  `T3_self_adjoint_conj` an `axiom`; zero axioms in the file, it is a proved
  theorem (3545). **Rio: leave it alone**, queued for after the march passes it.
* `codex/status/acer.md` — the `48ef3fca` attribution is Acer's to fix. Not
  touched.

## Outside the repo

Shipped earlier: `codex/data/rss_peaks_2026-10-21.log`,
`codex/data/d2_c81_8_seg01_evidence_2026-10-21.txt`, `codex/legion_build10.sh`.
Named, unchanged from `b8cadcac`: `/tmp/d2test/` (regenerable in one command),
the three untracked `_c81_8_` sources (deliberately not landed), the superseded
`/tmp/prod` and its no-density hazard, `/tmp/prodD`, `/tmp/prodR`, band logs,
and the Legion verify tree at `D:\CLAUDE-i9\_tmp\pf-ocirc-verify-20261001\`
(1732-olean build cache, not shippable; recipe in memory note
`infrastructure_legion_lean_verify_tree`).

**New this update:** the BSD falsification script lives only in the Legion
scratchpad (`scratchpad/`, ~50 lines of `Fraction` curve arithmetic). It is
named here rather than shipped because its five results are recorded in the
table above and it is trivially rewritten; if it becomes load-bearing it ships.

## Conflicts with other sessions

None new. `codex/status/acer.md` (upstream) has Acer in `PF/YangMills/*` on
Fubini Steps 5–6 — no overlap with the march, the producer, or BSD.
