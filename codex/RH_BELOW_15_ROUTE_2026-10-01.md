# RH below 15: the open step is not an argument-principle problem — 2026-10-01

**Headline: the argument principle is already in the corpus, kernel-clean, and already
instantiated on the exact rectangle. mathlib has none and cannot even define one at our
pin. The blocker is one layer above: nothing turns
`RectangleIntegral' (logDeriv ξ) zF wF` into a number. That bridge needs no numerics
and no winding number, and it is the next thing to write.**

Two claims in `codex/R331C_CAMPAIGN_CHARTER.md` are corrected below. Both corrections
*remove* a limitation.

## 1. What is already available

| ingredient | where | status |
|---|---|---|
| argument principle on a rectangle | `PF/Analytic/RectangleArgumentPrinciple_r327.lean` — `residueTheorem_finset:55`, `finite_zeros_rectangle:167`, `rectangleIntegral'_mul_logDeriv:391` | **0 `sorry`, 0 `native_decide`** (verified) |
| contour primitives | `PF/Analytic/PNT/ResidueCalcOnRectangles_r327.lean:46,49,67,73` — `HIntegral`, `VIntegral`, `RectangleIntegral`, `RectangleIntegral'` (primed carries `1/(2πi)`) | present |
| zero-count identity on *our* rectangle | `RiemannXiFullRectangleBoundary_r331e.lean:171` `xi_full_rectangle_zero_count_identity` | present (verified) |
| boundary zero-free, all four edges | `r328:135,179` (σ=0, σ=1, every t); `RiemannXiTopUnion:75`; `r331c:63,76`; `r331d:79,87` | present |
| lower bound `N ≥ 2` | `r331f:91` `two_distinct_critical_zeros_exists` | unconditional |
| top/bottom already in rotated form | `r331c:76` `top_edge_neg_xi_re_pos`, `r331d:87` — `0 < (-ξ).re` | **exactly the `ω = -1` form the bridge wants** |

## 2. mathlib at `eed770a43495` — what is absent

Grepped, zero hits each: `windingNumber` in any casing, "argument principle",
`rouche`/Rouché, any residue theorem (`Mathlib/Analysis/` has no residue file), any
zero-counting API beyond `analyticOrderNatAt`.

A winding number is not merely missing, it is **not definable** at this pin:
`Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean:192` still carries
`-- todo: upgrade this to IsCoveringMap Circle.exp`. `IsCoveringMap.liftPath` exists
generically but there is no instance for `Circle.exp`, so there is no continuous-argument
lifting to build a winding number from.

Jensen's formula is also absent. `Mathlib/Analysis/Complex/ValueDistribution/` has the
Nevanlinna scaffolding, but `FirstMainTheorem.lean` contains only
`abs_characteristic_sub_characteristic_shift_le` and its `eqO` form; the identity linking
`logCounting` to `circleAverage (log ‖f‖)` is not there.

Present and sufficient for the route below: `Mathlib/Analysis/Complex/CauchyIntegral.lean`
(what r327 is built on); `Complex.slitPlane` (`Complex/Basic.lean:574`), so the open
**right, upper and lower** half-planes are inside it and the left is not;
`HasDerivAt.clog_real` (`Complex/LogDeriv.lean:103`) for `ℝ → ℂ` paths, exactly the
`HIntegral`/`VIntegral` shape; `intervalIntegral.integral_eq_sub_of_hasDerivAt`.

## 3. The bridge — rotated branch primitives, no winding number, no numerics

For `|ω| = 1`, if `ω · ξ` stays in `slitPlane` along a segment then
`s ↦ Complex.log (ω · ξ s)` is a primitive of `logDeriv ξ` there — the `ω` cancels in
`f'/f` — and FTC-2 evaluates the edge integral in closed form. Two lemmas:

```lean
theorem hIntegral_logDeriv_eq_log_sub {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {x₁ x₂ y : ℝ} (ω : ℂ)
    (hmem : ∀ x ∈ Set.uIcc x₁ x₂, ω * f (⟨x, y⟩ : ℂ) ∈ Complex.slitPlane) :
    HIntegral (fun s => logDeriv f s) x₁ x₂ y
      = Complex.log (ω * f (⟨x₂, y⟩ : ℂ)) - Complex.log (ω * f (⟨x₁, y⟩ : ℂ))

theorem vIntegral_logDeriv_eq_log_sub {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {x y₁ y₂ : ℝ} (ω : ℂ)
    (hmem : ∀ y ∈ Set.uIcc y₁ y₂, ω * f (⟨x, y⟩ : ℂ) ∈ Complex.slitPlane) :
    VIntegral (fun s => logDeriv f s) x y₁ y₂
      = Complex.log (ω * f (⟨x, y₂⟩ : ℂ)) - Complex.log (ω * f (⟨x, y₁⟩ : ℂ))
```

`VIntegral` carries `I •` and the path `y ↦ ⟨x,y⟩` has derivative `I`, so the `I`s absorb.

**Why this removes the numerics from the integral.** Sum over sub-segments: the
`log_re = Real.log ‖·‖` parts cancel exactly around the closed loop, since each
subdivision point appears once as an endpoint and once as a start. What remains is `i ·`
a sum of `arg` differences. At a subdivision point `p` shared by rotations `ω_j` and
`ω_{j+1}`, both `ω_j ξ(p)` and `ω_{j+1} ξ(p)` have positive real part, so
`log(ω_{j+1}ξ(p)) − log(ω_j ξ(p))` is the **constant** `i · arg(ω_{j+1}/ω_j)`. The
integer is fixed combinatorially by the chain of rotations. **No numerical value of
`arg` is ever required.**

## 4. Correction 1 to the charter — the height ceiling should be withdrawn

`R331C_CAMPAIGN_CHARTER.md:197` records the margin as **0.2033 rad** and `:200` concludes
"**this proof shape works at T = 15 and fails by T = 16.** Any sequel at greater height
needs a different …".

0.2033 is `π − 2.9383`, i.e. the distance to the **principal-branch** wall at `π`. That
wall is an artifact of insisting on the principal branch along the whole right edge, not
a property of ξ.

With segmented rotated branches: let `θ₁ ∈ (π/2, 3π/2)` be the left-half-plane
determination of `arg ξ(1+15i)`, pinned by `Re ξ(1+15i) < 0`, and let `a = θ₁ + 2πm` be
the continuous value on the right edge starting from `arg ξ(1) = 0`. Top-edge
`Δarg = 2(π − θ₁)`, right-edge `Δarg = 2a`, and

```
N = 2 · (2a + 2π − 2θ₁) / (2π) = 4m + 2 .
```

`N ≥ 2` is already proved (`r331f:91`), so `N = 2 ⟺ m = 0 ⟺ a ∈ (π/2, 3π/2)`. The charter's
own value `a = 2.9383` sits in that window with **1.774 rad to the upper wall and 1.367 to
the lower — about 45%, not 6.5%.**

Checked independently: `π − 2.9383 = 0.2033` reproduces the charter's figure, and
`4.7124 − 2.9383 = 1.7741`, `2.9383 − 1.5708 = 1.3675` reproduce the corrected ones; the
`N = 4m+2` algebra substitutes and cancels as claimed.

So the ceiling claim is withdrawn, and the statement is kept. Per the project's
no-downgrade rule this is the direction repairs are supposed to go: a claimed limitation
turns out to be an artifact of the proof shape.

## 5. Correction 2 to the charter — statement B and the η detour are unnecessary

`:§8.4` declares statement B (`Im ξ(1+it) > 0` near `t = 0`) unprovable by certificate and
introduces `η(s) = (ξ(s) − 1/2)/(s − 1)` to repair it. Under the chain below the governing
claim near `t = 0` is instead R1's `Re ξ(1+it) > 0`, which at `t = 0` reads `1/2 > 0`.
B and η are not needed.

## 6. The half-plane chain, and where numerics remain

Numerics below are **mpmath at dps=25, not certificates.** Cross-checked at the corner
against `top15_re_lt_neg_1e4`: `Re ξ(1+15i) = −8.05948e−4`.

| edge | Δarg | source |
|---|---|---|
| bottom `t=−15`, σ:0→1 | +0.40657 | `−ξ` in right half-plane — **`r331d:87`, done** |
| right `σ=1`, t:−15→15 | +5.86574 | new |
| top `t=15`, σ:1→0 | +0.40657 | `−ξ` in right half-plane — **`r331c:76`, done** |
| left `σ=0`, t:15→−15 | +5.86574 | mirror of right, free from `r326` |

Total `12.5446 ≈ 4π`, so `N = 2`. Bottom equals top and left equals right **exactly**, by
`riemannXiEntire_conj` and `riemannXiEntire_reflect_vertical` — half the contour is free,
and the half that is already proved is in the right rotated form.

Right edge, closed sub-intervals so overlaps are automatic:

| segment | claim | ω | worst margin |
|---|---|---|---|
| R1 `t ∈ [0,13]` | `0 < Re ξ(1+it)` | `1` | `+2.50941e−3` at t=13 |
| R2 `t ∈ [13,29/2]` | `0 < Im ξ(1+it)` | `−I` | `+4.14183e−4` at t=29/2 |
| R3 `t ∈ [29/2,15]` | `Re ξ(1+it) < 0` | `−1` | `−5.59104e−4` at t=29/2 |

`ξ(1+13i) = (2.509e−3, 1.983e−3)` in Q1 and `ξ(1+29i/2) = (−5.591e−4, 4.142e−4)` in Q2, so
R1∩R2 and R2∩R3 overlap at shared endpoints; `ξ(1) = 1/2` makes R1 strict at `t = 0`; R3's
rotation is the **same** `ω = −1` as the top edge, so the corner `(1,15)` carries no
mismatch. Negative `t` is the conjugate mirror.

For scale, the existing panels resolve `Re ξ(σ+15i)` against `≈7.06e−4`. R1 is 3.5×
looser, R3 1.26× tighter, R2 1.7× tighter — the same precision band the panel machinery
already delivers.

## 7. What the 4,241 panels actually prove

One fact: **the sign of `Re ξ` on the single line `t = 15`, partitioned over
σ ∈ [1/2,1].** Structure verified on Box0: 40 u-quadrature segments × ~6 panels,
assembled by `RiemannXiBox0Bridge.lean` into one `intervalIntegral` over `u ∈ [1,5]` plus
an analytic tail envelope; `RiemannXiTopUnion` is a flat 18-way `by_cases` on σ. `t` is
the hard literal `15` (as `(15/2 : Interval)`) in every panel. **They cannot be repointed
at the interior as they stand.**

What *is* repointable: `realThetaReIntegrandN` (`r331b:425`) and `re_xi_at_s` / `im_xi_at_s`
(`r331a:96,116`) are general in both σ and t, and the vendored `girving/interval` accepts
non-degenerate intervals (`Interval.mem_approx_cos`, `Interval/Sincos.lean:623`), so
`cos((t/2)·log u)` over a *t*-interval is directly supported.
`PF/Analytic/RiemannXiEdgeEnclosure_r331c.lean` is already the consumer layer for that —
`EdgeReEnclosure:58`, `EdgeImEnclosure:64`, `re_xi_lower_bound_from_edge:112` — with 0
sorries, imported by nothing, never elaborated. **The missing piece is the producer: no
t-boxed quadrature exists.**

## 8. Alternatives, evaluated and rejected

**Box-covering `|ξ| > 0` on finitely many sub-boxes — impossible, not merely hard.**
`NoOffLineZeroInRightHalf` is vacuous at `σ = 1/2`, so its content is `ξ ≠ 0` on
`(1/2,1] × [−15,15]`. But `inf |ξ| = 0` there: `ξ → 0` as `σ → 1/2` at `t = ±14.1347`. No
finite cover of positive-`|ξ|` boxes reaches those two limit points. Repair needs a
certified lower bound on `|ξ'(ρ₀)| ≈ 8.9e−4` plus a Rouché radius — reintroducing exactly
the `ξ'` numerics the `r331f` part-2 decomposition removed.

**Jensen / Landau count from `|ξ|` bounds alone — blocked at this pin.** The one route
needing neither `ξ'` nor argument variation, but it needs the Jensen identity, which
mathlib does not have (§2). Building it is a mathlib-sized contribution.

**Real-analytic sign/monotonicity on the right half — no.** Both `Re ξ` and `Im ξ` change
sign in the interior; ξ is real on `σ = 1/2` and oscillates.

**Backlund/Turing via `N(T) = θ(T)/π + 1 + S(T)` — strictly more work.** Needs
Riemann–von Mangoldt (absent) *and* certified `arg Γ(1/4 + iT/2)` *and* the same argument
variation.

**Widen to `[−1,2] × [−15,15]` — real, on file as fallback.** ξ's zeros all lie in
`0 < Re s < 1` so the count is unchanged, and at `σ = 2` the margins are ~3× better
(`3.21e−3 / 1.75e−3 / 1.53e−3`) because `|ξ(2+15i)| = 1.54e−3` is small from
`|Γ(1+7.5i)| = 5.2e−5` — exponential smallness rather than cancellation, unlike the theta
representation which loses ~4 digits there. Blocker: needs certified `Complex.Gamma` on
vertical lines, and mathlib has no complex Stirling at this pin (`Gamma/` is
`Basic, Beta, BohrMollerup, Deligne, Deriv`; `Stirling.lean` is the `n!` asymptotic only).
Do not start here; keep it if the t-boxed quadrature stalls.

## 9. Order of work, and honest cost

1. **The two bridge lemmas** above, in a new `PF/Analytic/RectangleLogBranch_r331g.lean`,
   plus the four rotation-mismatch lemmas for `ω ∈ {1,−I,−1,I}` and the assembly
   `rectangleIntegral'_logDeriv_eq_of_branch_chain … = (2 : ℂ)` taking the eight
   half-plane sign facts as hypotheses. **No new numerics**, pure mathlib + r327,
   ~200–400 lines. This is the component that decides whether the architecture closes.
2. `re_xi_upper_bound_from_edge` — transpose of `r331a:186`, one screen. R3 needs it.
3. Elaborate `EdgeEnclosure_r331c`.
4. The t-boxed quadrature producer: R1 first (loosest margin, validates the generator
   transpose), R2/R3 last.

**Cost, split because the halves differ sharply.** The bridge and the symmetry/assembly
bookkeeping are **weeks** — two to four, one person, no build campaign, no generated
files. The t-boxed quadrature is **months of compute**: the t-sensitivity of a quadrature
node, `(log u)/2`, equals its σ-sensitivity, so t-boxes need the same widths the σ
campaign used; scaling the 18-box, 4,241-module σ campaign over `t ∈ [0,15]` and weighting
by the margin profile gives roughly **180–230 t-boxes and 40,000–60,000 generated
modules, 10–15× the existing campaign.** The existing one is a multi-day Acer build.

**One cheap experiment that should gate that campaign, and needs no Lean build:** run the
existing `opt40tight` tuner in Python at `σ = 1` over candidate t-boxes near `t = 14.5`
to get the real box schedule and module count for R2/R3. That number, not a scaling
argument, is what the decision should rest on.

## 10. Framing, kept

`riemannHypothesis_below_15` is RH on one finite rectangle, settled classically since
Riemann and Gram. **Nothing here bears on the open problem.** The value is that the finite
statement becomes machine-checked. Every claim above about Lean source is a reading of
source, not a kernel verdict; nothing in this document was built. The numerics are mpmath,
not certificates.

Verified independently before filing: r327 exists with the named theorems and zero
escape hatches; r331e's count identity exists as quoted; mathlib has no `windingNumber`
and no argument principle at the pin; the charter's `0.2033` and "fails by T = 16" are at
`R331C_CAMPAIGN_CHARTER.md:197,200`.

---

# Corrections, 2026-10-01 second pass

Five corrections to the document above, from an independent re-reading of the same
source. Three change the cost of the route; two are errors of fact in this document.

## C1. "Never elaborated" was wrong — and the module's own header is why

§7 above says `PF/Analytic/RiemannXiEdgeEnclosure_r331c.lean` has "0 sorries,
imported by nothing, **never elaborated**". The first two are right. The third is false.

The olean exists — 193,392 bytes, built 2026-09-08 — and its `.trace` records exactly
three log entries: one `trace` and two `warning` (`unused variable h_ne`), and **no
`error`**. The module compiled. Its source content has not changed since (git clean,
last touched by `00f8a634`, same day); only the file mtime moved, from a checkout.

**Where the error came from matters more than the error.** The file's own header said
"SKELETON, NOT YET ELABORATED … They have not been checked", and `§Axiom check` was
commented out *citing that claim* as the reason. The header was stale, a reading of it
produced this document's §7, and the claim then had to be corrected from build
artefacts. Same failure mode as `YangMillsPerelmanTemplateY1Y4Discharge`
(commit `2c1e7437`): a module's self-description outlived the facts and an audit
believed it. Both the header and the suppressed axiom block are now repaired, and
the module gates PRISTINE with four consumers.

## C2. Fourteen segments, not eight — but only three are new obligations

§6's table covers `t ∈ [0,15]` and defers the rest to "negative `t` is the conjugate
mirror". The right edge of the contour is `VIntegral f 1 (-15) 15`, so the mirror is
three more segments, and the left edge likewise. Honest accounting:

| | count |
|---|---|
| segments in the full traversal | **14** |
| primitive numerical obligations (R1, R2, R3) | **3** |
| already landed (`r331d:87` bottom, `r331c:76` top) | **2** |
| free by symmetry | **9** |

All four rotations `{1, -I, -1, I}` are genuinely used. Counterclockwise from
`zF = ⟨0,-15⟩`: bottom `-1`; right going up `(-1, +I, 1, -I, -1)`; top `-1`; left
going down `(-1, +I, 1, -I, -1)`. The three-rotation table in §6 is what you see if
you look only at `t ≥ 0`.

## C3. The symmetry buys slightly less than "left = right exactly"

§6 claims bottom = top and left = right **exactly**. Correct about the facts, wrong
about the rotations. Both symmetries are conjugations —
`riemannXiEntire_conj` (`r326:88`) and `riemannXiEntire_reflect_vertical` (`r326:109`)
— so each **preserves `Re` and negates `Im`.**

Consequence: the two `Re`-governed left segments do mirror the right ones, but the
`Im`-governed one does not. L2's fact is `Im ξ(0+it) < 0` with rotation `+I`, not
`Im > 0` with `-I`. Same flip on the negative-`t` segments R2' and L2'.

So the assembly cannot take eight identically-shaped hypotheses. It takes **three
primitive hypotheses plus two landed theorems and derives the other nine**, or it
takes fourteen and the caller discharges eleven. Three one-line transfer lemmas are
also missing: `im_reflect`, `re_conj_t`, `im_conj_t`. (`re_reflect` exists at
`r331c:53`; `re_conj_at_neg_15` exists at `r331d:69` but is specialised to `t = 15`.)

This is a small cost increase, not a structural one. The §9 estimate of weeks for the
bridge and symmetry layer stands.

## C4. `slitPlane` membership is clean on every segment — no endpoint hazard

Each of the four sign claims lands in the **left disjunct** of
`slitPlane = {z | 0 < z.re ∨ z.im ≠ 0}`, strictly, so `0` is excluded automatically:

| ω | `(ω·z).re` | claim gives |
|---|---|---|
| `1` | `z.re` | `0 < Re ξ` |
| `-I` | `z.im` | `0 < Im ξ` |
| `-1` | `-z.re` | `Re ξ < 0` |
| `+I` | `-z.im` | `Im ξ < 0` |

The segments are **closed and overlap at shared endpoints**, so at each junction both
adjacent rotated real parts are positive — exactly what §3's constant-mismatch
argument needs. The corner `(1,15)` carries no mismatch because R3 and the top edge
share `ω = -1`. At `t = 0`, `ξ(1) = ξ(0) = 1/2` exactly (`r328:110`, `r328:103`), and
`r329b:386` `riemannXiEntire_real_Icc_pos` covers the whole `t = 0` line — which is
the second, independent confirmation that §5 is right that statement B and the `η`
detour are unnecessary.

## C5. A representation mismatch that will stall the assembly if not anticipated

The contour primitives are stated in `x + y*I` form, not `⟨x,y⟩` form
(`ResidueCalcOnRectangles_r327.lean:46,49`, and note that file declares **no
namespace** — those definitions are root-level):

```lean
noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E := ∫ x in x₁..x₂, f (x + y * I)
noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E := I • ∫ y in y₁..y₂, f (x + y * I)
```

Every existing sign theorem in the corpus uses `⟨σ,t⟩`. So the §3 bridge lemmas as
drafted will **not** match `HIntegral`'s body by `rfl`. The fix is one rewrite with
`Complex.mk_eq_add_mul_I` (`Mathlib/Data/Complex/Basic.lean:246`, already used at
`PF/Analytic/XiRealWitness.lean:283`). Recorded because this is the kind of mismatch
that costs a day for no mathematical reason.

Also free, and worth knowing before writing the bridge:
`differentiable_riemannXiEntire` (`RiemannXiEntire_r325.lean:89`) discharges the
`Differentiable ℂ f` hypothesis of both primitives with no work.

## C6. Two things §1 should not be read as claiming

- `r328:135` and `r328:179` are `riemannXiEntire_ne_zero_on_re_one` and
  `..._on_re_zero` — **nonvanishing** on all of `ℝ`, not sign facts. They are what
  makes `full_rectangle_boundary_zero_free` (`r331e:99`) unconditional, and they
  contribute **nothing** to the vertical-edge rotation rows. The table in §1 lists
  them under "boundary zero-free", which is accurate, but they must not be mistaken
  for progress on R1–R3.
- `r331e`'s own docstring (`:4`) says the file "composes r331b (right edge)".
  `RiemannXiThetaRealFormAndBoxes_r331b.lean:2` is titled "CERTIFIED T=15 TOP EDGE"
  and its panels hardcode `t = 15`; the actual right edge at `r331e:138` is `r328`'s
  nonvanishing. That docstring is wrong and this document inherited the phrasing.
