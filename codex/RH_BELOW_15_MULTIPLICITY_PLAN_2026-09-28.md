# PLAN — the multiplicity-matching step for `riemannHypothesis_below_15`

**Date:** 2026-09-28
**Standing context:** r331d source-landed (kernel-check on Xavier in flight); r331e (full-rectangle boundary + zero-count identity + ξ↔ζ interior bridge) drafted in the ACTIVE tree.
**Purpose:** scope the ONE remaining step between r331e and `riemannHypothesis_below_15`.

---

## The gap

r331e delivers:

```
xi_full_rectangle_zero_count_identity :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) zF wF
      = ∑ ρ ∈ (finite_zeros_rectangle ...).toFinset,
          (analyticOrderNatAt riemannXiEntire ρ : ℂ)
```

The RHS is `Σ_{ρ ∈ Z} ord_ρ(ξ)` where `Z` is the finite set of interior zeros of ξ in `[0,1] × [-15, 15]`.

Together with r331e's `interior_xi_zero_iff_zeta_zero`, we know every ρ ∈ Z is also a ζ zero in the open critical strip. But we do NOT yet know:

- **Q1:** whether every ρ ∈ Z has `ρ.re = 1/2` (the RH conclusion below height 15).
- **Q2:** how many elements `Z` contains and with what multiplicities.

`riemannHypothesis_below_15` is the answer YES to Q1.

## Two independent routes

### Route A — enumeration + multiplicity 1

Prove that:
1. `Z = {ρ₁, conj ρ₁}` where `ρ₁ = ⟨1/2, γ₁⟩` with `γ₁ ≈ 14.13473`.
2. `analyticOrderNatAt riemannXiEntire ρ₁ = 1`.
3. Same for `conj ρ₁`.

Then `Σ = 2`, and every ρ ∈ Z has `ρ.re = 1/2`. Done.

**Cost.** Step 1 requires proving γ₁ is the UNIQUE ordinate of a ξ-zero in `(0, 15)` (equivalently, unique ζ zero in `(0, 15)` on the critical line by r326.F). The existence half is r324. The uniqueness half is not currently in the corpus and is *specific to γ₁*. Classical route: Weil's explicit formula + interval bounds on the counting function `N(T) ≈ T/2π · log(T/2πe) + 7/8 + o(1)`. Requires the Riemann-von Mangoldt formula — a significant mathlib gap.

Step 2 (multiplicity 1) requires proving `deriv riemannXiEntire ρ₁ ≠ 0`. Numerical: `|ξ'(1/2 + 14.13473i)| ≈ 8.9e-4`. Formalizing this needs certified numeric bounds on ξ' at a specific point.

**Verdict.** Route A is honest but requires substantial new work (Riemann–von Mangoldt formalization + certified numerics on ξ').

### Route B — direct contour value comparison

Prove:
1. The contour integral `(1/2πi) ∮_{∂R} logDeriv ξ` equals 2 (exactly the multiplicity sum on the critical line for `|t| < 15`).
2. All on-line zeros contribute nonnegatively; any off-line zero would also contribute nonnegatively (multiplicities are natural numbers).
3. Therefore the total = on-line-only count implies no off-line zeros.

**Cost.** Step 1 requires directly evaluating the contour integral. That's real analytic work — probably one contour parametrization + Riemann-Lebesgue-style estimates. The r331b/c/d boundary margins (`|Re ξ|` bounded away from 0, `|Im ξ|` bounded) may give the numerical control needed. But formalizing the evaluation to an integer needs precision management.

Step 2 is a mathlib fact once step 1 is done.

**Verdict.** Route B is direct but requires precise contour integration — hundreds of lines of quantitative analysis.

### Route C — HYBRID: use existing on-line witness + argument-principle inequality

Prove:
1. From r324 (`exists_critical_line_riemannZeta_zero_between_one_and_fifteen`), there is AT LEAST one ζ zero at some `t₀ ∈ (1, 15)`.
2. By r326.B conjugation symmetry, there is also a zero at `⟨1/2, -t₀⟩` in `(-15, -1)`.
3. Each contributes `≥ 1` to the multiplicity sum, so `Σ ≥ 2`.
4. Prove the contour integral value is EXACTLY 2 using r331b/c/d margins.
5. Combining: `Σ = 2`, both terms on-line, so no additional zeros exist (which would push `Σ ≥ 3`).

**Cost.** Steps 1-3 use existing lemmas. Step 4 is the same evaluation work as Route B step 1. Route C is fundamentally the same work as Route B but scaffolded around what's already proved.

**Verdict.** Route C = Route B + minor bookkeeping.

## Recommendation

**Route B/C is the least-new-mathlib path.** The multiplicity work does not require Riemann–von Mangoldt or certified ξ'.

The actual next brick is:
```
theorem contour_integral_value_eq_two_pi_i_times_two :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) zF wF
      = 2 * π * I * (2 : ℂ)
```

This is Route B step 1. Once it lands, `riemannHypothesis_below_15` is a short composition.

## What the r331b/c/d boundary margins buy

- r331c: `Re ξ⟨σ, 15⟩ < -1/10⁴` on `σ ∈ [0,1]` (top edge in open left half-plane).
- r331d: same for `t = -15` by conjugation.
- r331b (via `top15_re_lt_neg_1e4`): same for σ ∈ [1/2, 1] with t=15.
- Right edge (`σ = 1`): `Re ξ` positive for `Re s = 1` (from r328's `riemannXiEntire_ne_zero_on_re_one` + connectedness argument).
- Left edge (`σ = 0`): mirror of right by r326.A.

The critical property: **ξ traces a curve in ℂ \ {0} as `s` runs along `∂R`, and that curve has bounded winding number.** The winding number IS the contour integer `(1/2πi) ∮ logDeriv ξ`.

The r331b/c/d margins ensure the winding-number computation is stable: no small `|ξ|` on the boundary means log ξ has a continuous branch except across specific rotations. Detailed analysis: on the top/bottom edges `Re ξ < 0`, so `arg ξ ∈ (π/2, 3π/2)` there; on the left/right edges `Re ξ` has definite signs from FE + zeta bounds; corners connect the branches.

## Deferred: contour-integer evaluation

The r331b box campaign has all the numerical control needed for the winding-number argument. A separate landing (`RiemannXiWindingCount_r331f`?) is likely 200-500 lines and uses only existing mathlib complex-analysis primitives plus the r331 boundary margins.

## Sequencing

1. **r331d** — kernel-clean seal (in flight on Xavier).
2. **r331e** — full-rectangle boundary + count identity + ξ↔ζ bridge (drafted, awaits r331d build).
3. **r331f** — contour-integer evaluation via winding-number argument (~200-500 lines, unlanded, Route B step 1).
4. **`riemannHypothesis_below_15`** — short composition of r331e + r331f (~30 lines).

The chain to literal RH-below-15 is not "one composition module" — it is r331e (small) + r331f (medium research) + capstone (trivial).

**Do NOT auto-implement r331f.** Per POST-r315 directive, recommend and await explicit go/no-go.

---

## CORRECTION — 2026-09-29 (normalization defect in the r331f target)

**The r331f statement proposed above is wrong by a factor of 2πi and is not provable as written.**

The plan proposes:

```lean
theorem contour_integral_value_eq_two_pi_i_times_two :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) zF wF
      = 2 * π * I * (2 : ℂ)
```

But `RectangleIntegral'` (note the prime) already carries the `1/(2πi)` factor.
From `PF/Analytic/PNT/ResidueCalcOnRectangles_r327.lean:73`:

```lean
noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • RectangleIntegral f z w
```

This is consistent with the argument principle in
`PF/Analytic/RectangleArgumentPrinciple_r327.lean:391`, whose conclusion carries no 2πi:

```lean
theorem rectangleIntegral'_mul_logDeriv ... :
    RectangleIntegral' (fun s => g s * logDeriv f s) z w
      = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ
```

and with r331e's `xi_full_rectangle_zero_count_identity`, which equates
`RectangleIntegral' (logDeriv ξ) zF wF` directly to `∑ ord_ρ(ξ)` — again no 2πi.

**Corrected r331f target:**

```lean
theorem contour_integral_value_eq_two :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) zF wF = (2 : ℂ)
```

Writing the original form would have produced a goal off by 2πi — i.e. a false statement,
unclosable by any correct proof. Use the corrected form.

## Verified infrastructure status (2026-09-29)

Checked on the Acer ACTIVE tree. Relevant to sequencing r331f:

| Module | Lines | State |
|---|---|---|
| `RectangleArgumentPrinciple_r327` | 425 | clean — no `sorry` / `axiom` / `native_decide`; olean **CURRENT** |
| `RiemannXiRectangleCount_r327` | 168 | olean **CURRENT** |
| `RiemannXiEntire_r325` | — | olean **CURRENT** |
| `RiemannXiSymmetries_r326` | — | olean **CURRENT** |
| `RiemannXiFullRectangleBoundary_r331e` | 235 | complete, **no `sorry`** (the sole "sorry" match is a docstring); awaits r331d |
| `RiemannXiT15Endgame` | 103 | clean; independent route via `RiemannXiTopUnion` + r329b |

Two consequences:

1. **mathlib provides none of this.** There is no `RectangleIntegral`, no argument principle and
   no winding number in mathlib v4.24.0-rc1 — only `analyticOrderNatAt`. Route B rests entirely on
   PF's own r327 stack, which is clean. No mathlib gap blocks r331f.
2. **r331f can be developed without the panel rebuild.** The four r327/r325/r326 oleans are
   current, so the generic winding/counting machinery compiles against them today. Only the final
   application to ξ needs the r331c/d boundary margins, i.e. the panels.

Also note `RiemannXiT15Endgame` already reaches `xi_T15_zero_count_identity_unconditional` by a
different route (TopUnion + r329b) and is clean. Neither it nor r331e evaluates the count to an
integer, and `riemannHypothesis_below_15` appears nowhere in the corpus. The single remaining
brick is the contour-integer evaluation, as this plan states.
