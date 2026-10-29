# NS Route A: the three-item gap is ORDERED, not parallel — item 1 depends on item 3

**Date:** 2026-10-29 (Legion, library measurement on Acer). Analysis only, no
Lean landed. Labels **FACT** (measured) / **JUDGEMENT** / **OPEN**.
Delta over `codex/ROUTEA_SPEC_UPDATE_2026-10-19.md` (`8d23f11d`), which named
the gap as three items. Everything below is new.

---

## The finding, in one line

`8d23f11d` lists three build items as a flat list. **They are not independent:
item 1 (Schwartz dense in `L²`) cannot be built before item 3 (convolution
`L¹⋆L² → L²`), because the only route to item 1 runs through mollification, and
mollification is exactly item 3's estimate.** The build order is therefore
forced: **3, then 1, then 2b.** A session that opens on item 1 because it looks
like the smallest will spend its cycle discovering item 3.

## What is in the library — FACT, measured 2026-10-29

| needed for item 1 | mathlib | file |
|---|---|---|
| continuous compactly-supported dense in `Lp` | ✅ `MemLp.exists_hasCompactSupport_eLpNorm_sub_le` | `MeasureTheory/Function/ContinuousMapDense.lean:134` |
| bounded-continuous dense in `Lp` | ✅ `MemLp.exists_boundedContinuous_eLpNorm_sub_le` | same, `:232` |
| simple functions dense in `Lp` | ✅ (as `8d23f11d` noted) | `SimpleFuncDenseLp.lean` |
| **smooth** or **Schwartz** dense in `Lp` | ❌ **absent** | no file |
| the smoothing step (continuous ⟶ smooth in `Lp`) | ❌ **absent** | no file |

So the classical chain `L² ⟵ C_c ⟵ C_c^∞ ⟵ 𝒮` has its **first** link and not
its second. The standard proof of the missing link is mollification: convolve a
continuous compactly-supported `g` with a bump `φ_ε`, then show
`‖g ⋆ φ_ε − g‖_{L²} → 0`. That estimate is a convolution `L²` bound.

| needed for item 3 | mathlib | note |
|---|---|---|
| `convolution` | ✅ root-level | as `e2dcba22` recorded |
| `Integrable.integrable_convolution` | ✅ | the `p = 1` case only |
| convolution paired with `MemLp` / `eLpNorm` | ❌ **absent** | confirmed again |
| **Minkowski's integral inequality** | ❌ **absent** | the `Minkowski` hits are the finite/discrete triangle inequalities in `lpSpace.lean` and `MeanInequalities.lean`, not the integral form |

The absent Minkowski integral inequality is the usual engine for the convolution
`Lp` bound, so item 3 is absent at **two** levels: the statement and its standard
proof ingredient.

## Why this is worth a note rather than a build — JUDGEMENT

`8d23f11d`'s own closing verdict is *"the library gives Route A its plumbing for
free and none of its analysis."* This measurement sharpens it: the three items
are **one analytic dependency chain**, not three independent lookups, and the
root of the chain is the convolution estimate.

Consequence for scheduling: item 1 was the natural-looking first target —
smallest statement, ingredient named in the spec. It is in fact the *second*
target, and opening on it wastes the cycle. That is the same class of saving as
`8d23f11d`'s "four near-misses that will waste a build cycle" table, which is
why it is recorded in the same form.

## What is NOT claimed

Not claimed: that Route A is unreachable — it is not, and nothing here changes
the end-to-end assembly verification of `8d23f11d`, which stands. Not claimed:
that item 3 is hard in an absolute sense (Young's inequality for `L¹⋆L²` is
classical mathematics; it is absent from this library, which is a different
fact). Not claimed: any estimate of hours. And no anchor language anywhere ---
§0.2 binds: Navier–Stokes is **not** a settled anchor, the unforced Clay problem
is open, and ch22's conditional no-blow-up thesis is the lane's content.

## The next step, named

**Item 3 first**: a convolution bound `‖f ⋆ g‖_{L²} ≤ ‖f‖_{L¹}‖g‖_{L²}`, with
Minkowski's integral inequality as the likely prerequisite — meaning the real
first brick may be Minkowski, not Young. Measuring whether Minkowski's integral
form is reachable from mathlib's existing `MeanInequalities` is the cheapest
next probe, and it is a probe, not a build.
