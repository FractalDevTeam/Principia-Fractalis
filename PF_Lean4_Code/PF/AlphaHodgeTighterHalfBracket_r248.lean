/-
# r248: TIGHTER HODGE UPPER BRACKET — σ(α_Hodge) < 1/2.

★ 2026-08-13 r248 — the SIXTH sharp bracket landing, and the TIGHTEST
Hodge bracket obtainable at the current mathlib toolkit. Sharpens r243's
`σ_Hodge < log 2/log 3 ≈ 0.631` to `σ_Hodge < 1/2`, at the cost of
deriving from scratch the Taylor upper bound
`sin(x) ≤ x − x³/6 + x⁵/120` for `x ∈ [0, ∞)`. ★

## Chain

**Goal**: σ(α_Hodge = φ) < 1/2, i.e., `|1 + 2·cos(π · φ)| < √3`.
Since `cos(π · φ) > 0` (r226), the value is positive, so goal reduces to
`1 + 2·cos(π · φ) < √3`, i.e., `cos(π · φ) < (√3 − 1)/2`.

**Substitution**: `π · φ = π/2 + π√5/2 = 3π/2 + π(√5 − 2)/2`. Setting
`z := π(√5 − 2)/2`, we get `cos(π · φ) = cos(3π/2 + z) = sin(z)`. So the
goal reduces to `sin(z) < (√3 − 1)/2` with `z = π(√5 − 2)/2 ≈ 0.371`.

**Taylor bound (derived here)**: for `x ≥ 0`,
    `sin(x) ≤ x − x³/6 + x⁵/120`.
Proved by a three-level monotonicity cascade from mathlib's `Real.sin_le`
and `Real.one_sub_sq_div_two_le_cos`.

**Numerical bound**: with `√5 < 2237/1000` and `π < 3.1416`,
    `z < 3.1416 · (237/1000)/2 = 3.1416 · 237/2000 ≈ 0.37228`.
Evaluating the Taylor polynomial `x − x³/6 + x⁵/120` at this upper bound
gives `≈ 0.36374 < (√3 − 1)/2 ≈ 0.36603`. Margin ≈ 0.0023.

## Contents

§1 Level 4 lemma: `x − x³/6 ≤ sin(x)` for `x ≥ 0`. (Standard, but not in
   mathlib in this exact form — `sin_gt_sub_cube` has denominator 4.)
§2 Level 5 lemma: `cos(x) ≤ 1 − x²/2 + x⁴/24` for `x ≥ 0`.
§3 Level 6 lemma: `sin(x) ≤ x − x³/6 + x⁵/120` for `x ≥ 0`.
§4 Tight `√5` bound: `√5 < 2237/1000`.
§5 The z bound: `π(√5 − 2)/2 < 3.1416 · 237/2000`.
§6 Polynomial upper bound `< (√3 − 1)/2` at the z_upper.
§7 `sin_z_lt_sqrt_three_minus_one_div_two` — combine §3 + §6.
§8 `cos_pi_mul_goldenRatio_lt_sqrt_three_minus_one_div_two` — the key step.
§9 `sigma_alphaHodge_lt_half` — the sharp bracket.
§10 Axiom check.

## Scope

* NOT novel — the Taylor upper bound `sin(x) ≤ x − x³/6 + x⁵/120` is
  standard 19th-century analysis. What's new is deriving it in Lean under
  the substrate corpus's zero-project-axioms constraint.
* NOT a Millennium discharge.
* IS the sixth sharp substrate bracket, sharpening r243's Hodge bound
  to below the σ = 1/2 threshold — the tightest algebraically-clean
  Hodge bracket obtainable at HEAD.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.AlphaHodgeUpperBracketCantor_r243
import PF.AlphaNPLowerBracketPentagon_r247

open scoped Real

namespace PrincipiaTractalis.AlphaHodgeTighterHalfBracket

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis.AlphaHodgeSigmaPositive
open PrincipiaTractalis

/-! ## §1 Level 4 — `x − x³/6 ≤ sin(x)` on `[0, ∞)`. -/

/-- The building-block function `g(x) = sin(x) − x + x³/6`. Nonneg on
`[0, ∞)` by the monotonicity cascade. -/
private noncomputable def g4 (x : ℝ) : ℝ := Real.sin x - x + x^3 / 6

private lemma hasDerivAt_g4 (x : ℝ) :
    HasDerivAt g4 (Real.cos x - 1 + x^2 / 2) x := by
  have h1 : HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin x
  have h2 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
  have h3 : HasDerivAt (fun x : ℝ => x^3 / 6) (x^2 / 2) x := by
    have hp : HasDerivAt (fun x : ℝ => x^3) (3 * x^2) x := by
      simpa using (hasDerivAt_pow 3 x)
    have hd := hp.div_const 6
    convert hd using 1
    ring
  have := (h1.sub h2).add h3
  convert this using 1

private lemma deriv_g4 (x : ℝ) : deriv g4 x = Real.cos x - 1 + x^2 / 2 :=
  (hasDerivAt_g4 x).deriv

private lemma g4_deriv_nonneg (x : ℝ) : 0 ≤ deriv g4 x := by
  rw [deriv_g4]
  have := Real.one_sub_sq_div_two_le_cos (x := x)
  linarith

private lemma g4_differentiable : Differentiable ℝ g4 :=
  fun x => (hasDerivAt_g4 x).differentiableAt

private lemma g4_monotone : Monotone g4 :=
  monotone_of_deriv_nonneg g4_differentiable g4_deriv_nonneg

private lemma g4_zero : g4 0 = 0 := by unfold g4; norm_num

/-- **Level 4**: `x − x³/6 ≤ sin(x)` for `x ≥ 0`. -/
lemma sin_ge_x_sub_cube_div_six {x : ℝ} (hx : 0 ≤ x) :
    x - x^3 / 6 ≤ Real.sin x := by
  have hm : g4 0 ≤ g4 x := g4_monotone hx
  rw [g4_zero] at hm
  unfold g4 at hm
  linarith

/-! ## §2 Level 5 — `cos(x) ≤ 1 − x²/2 + x⁴/24` on `[0, ∞)`. -/

private noncomputable def h5 (x : ℝ) : ℝ := 1 - x^2 / 2 + x^4 / 24 - Real.cos x

private lemma hasDerivAt_h5 (x : ℝ) :
    HasDerivAt h5 (Real.sin x - x + x^3 / 6) x := by
  have h1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
  have h2 : HasDerivAt (fun x : ℝ => x^2 / 2) x x := by
    have hp : HasDerivAt (fun x : ℝ => x^2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    have hd := hp.div_const 2
    convert hd using 1
    ring
  have h3 : HasDerivAt (fun x : ℝ => x^4 / 24) (x^3 / 6) x := by
    have hp : HasDerivAt (fun x : ℝ => x^4) (4 * x^3) x := by
      simpa using (hasDerivAt_pow 4 x)
    have hd := hp.div_const 24
    convert hd using 1
    ring
  have h4 : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x
  have := ((h1.sub h2).add h3).sub h4
  convert this using 1
  ring

private lemma deriv_h5 (x : ℝ) : deriv h5 x = Real.sin x - x + x^3 / 6 :=
  (hasDerivAt_h5 x).deriv

private lemma h5_deriv_nonneg_on_Ici_zero :
    ∀ x ∈ interior (Set.Ici (0:ℝ)), 0 ≤ deriv h5 x := by
  intro x hx
  rw [interior_Ici] at hx
  have hx0 : 0 ≤ x := le_of_lt hx
  rw [deriv_h5]
  have := sin_ge_x_sub_cube_div_six hx0
  linarith

private lemma h5_continuous : Continuous h5 := by
  unfold h5
  continuity

private lemma h5_differentiable : Differentiable ℝ h5 :=
  fun x => (hasDerivAt_h5 x).differentiableAt

private lemma h5_monotoneOn : MonotoneOn h5 (Set.Ici 0) :=
  monotoneOn_of_deriv_nonneg (convex_Ici 0) h5_continuous.continuousOn
    h5_differentiable.differentiableOn h5_deriv_nonneg_on_Ici_zero

private lemma h5_zero : h5 0 = 0 := by
  unfold h5
  rw [Real.cos_zero]; norm_num

/-- **Level 5**: `cos(x) ≤ 1 − x²/2 + x⁴/24` for `x ≥ 0`. -/
lemma cos_le_one_sub_sq_div_two_add_fourth_div_twenty_four {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x^2 / 2 + x^4 / 24 := by
  have hm : h5 0 ≤ h5 x := h5_monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  rw [h5_zero] at hm
  unfold h5 at hm
  linarith

/-! ## §3 Level 6 — `sin(x) ≤ x − x³/6 + x⁵/120` on `[0, ∞)`. -/

private noncomputable def k6 (x : ℝ) : ℝ := x - x^3 / 6 + x^5 / 120 - Real.sin x

private lemma hasDerivAt_k6 (x : ℝ) :
    HasDerivAt k6 (1 - x^2 / 2 + x^4 / 24 - Real.cos x) x := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
  have h2 : HasDerivAt (fun x : ℝ => x^3 / 6) (x^2 / 2) x := by
    have hp : HasDerivAt (fun x : ℝ => x^3) (3 * x^2) x := by
      simpa using (hasDerivAt_pow 3 x)
    have := hp.div_const 6
    convert this using 1
    ring
  have h3 : HasDerivAt (fun x : ℝ => x^5 / 120) (x^4 / 24) x := by
    have hp : HasDerivAt (fun x : ℝ => x^5) (5 * x^4) x := by
      simpa using (hasDerivAt_pow 5 x)
    have hd := hp.div_const 120
    convert hd using 1
    ring
  have h4 : HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin x
  have := ((h1.sub h2).add h3).sub h4
  convert this using 1

private lemma deriv_k6 (x : ℝ) : deriv k6 x = 1 - x^2 / 2 + x^4 / 24 - Real.cos x :=
  (hasDerivAt_k6 x).deriv

private lemma k6_deriv_nonneg_on_Ici_zero :
    ∀ x ∈ interior (Set.Ici (0:ℝ)), 0 ≤ deriv k6 x := by
  intro x hx
  rw [interior_Ici] at hx
  have hx0 : 0 ≤ x := le_of_lt hx
  rw [deriv_k6]
  have := cos_le_one_sub_sq_div_two_add_fourth_div_twenty_four hx0
  linarith

private lemma k6_continuous : Continuous k6 := by
  unfold k6
  continuity

private lemma k6_differentiable : Differentiable ℝ k6 :=
  fun x => (hasDerivAt_k6 x).differentiableAt

private lemma k6_monotoneOn : MonotoneOn k6 (Set.Ici 0) :=
  monotoneOn_of_deriv_nonneg (convex_Ici 0) k6_continuous.continuousOn
    k6_differentiable.differentiableOn k6_deriv_nonneg_on_Ici_zero

private lemma k6_zero : k6 0 = 0 := by
  unfold k6
  rw [Real.sin_zero]; norm_num

/-- **Level 6 (the Taylor upper bound)**: `sin(x) ≤ x − x³/6 + x⁵/120` for `x ≥ 0`. -/
lemma sin_le_taylor_fifth_order {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x^3 / 6 + x^5 / 120 := by
  have hm : k6 0 ≤ k6 x := k6_monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  rw [k6_zero] at hm
  unfold k6 at hm
  linarith

/-! ## §4 Tight `√5 < 2237/1000`. -/

/-- **`sqrt_five_lt_2237_over_1000`** — via nlinarith on `(2237/1000)² > 5`. -/
lemma sqrt_five_lt_2237_over_1000 : Real.sqrt 5 < 2237 / 1000 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  nlinarith [Real.sqrt_nonneg 5, h5, sq_nonneg (Real.sqrt 5 - 2237/1000)]

/-! ## §5 The z upper bound. -/

/-- **`pi_mul_sqrt_five_sub_two_div_two_lt_zbound`** — `π(√5 − 2)/2 < 3723/10000`.

Numerically ≈ 0.37228 < 0.3723. Comes from `π < 3.1416` (Real.pi_lt_d4) and
`√5 < 2237/1000` (§4). -/
lemma pi_mul_sqrt_five_sub_two_div_two_lt_zbound :
    π * (Real.sqrt 5 - 2) / 2 < 3723 / 10000 := by
  have hpi : π < 3.1416 := Real.pi_lt_d4
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have hs5 := sqrt_five_lt_2237_over_1000
  have hs5_gt2 : (2 : ℝ) < Real.sqrt 5 := AlphaHodgeSigmaPositive.two_lt_sqrt_five
  have hd : Real.sqrt 5 - 2 < 237 / 1000 := by linarith
  have hd_pos : 0 < Real.sqrt 5 - 2 := by linarith
  nlinarith [hpi, hd, hpi_pos, hd_pos]

/-! ## §6 Polynomial upper bound at the rational `zb = 3723/10000`. -/

/-- **`taylor_poly_at_zbound_lt_target`** — at `zb = 3723/10000 ≈ 0.3723`,
the Taylor polynomial `zb − zb³/6 + zb⁵/120 < (√3 − 1)/2`.

Numerically: `poly(0.3723) ≈ 0.36376`, `(√3 − 1)/2 ≈ 0.36603`, margin ≈ 0.00227.

Proof: `√3 > 1.732` gives `(√3 − 1)/2 > 0.366`. `norm_num` evaluates poly. -/
lemma taylor_poly_at_zbound_lt_target :
    (3723 : ℝ) / 10000 - ((3723 : ℝ) / 10000)^3 / 6
      + ((3723 : ℝ) / 10000)^5 / 120 < (Real.sqrt 3 - 1) / 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hs3 : (1.732 : ℝ) < Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3, h3, sq_nonneg (Real.sqrt 3 - 1.732)]
  have hpoly_lt : (3723 : ℝ) / 10000 - ((3723 : ℝ) / 10000)^3 / 6
      + ((3723 : ℝ) / 10000)^5 / 120 < 0.364 := by norm_num
  linarith

/-! ## §7 `sin(z) < (√3 − 1)/2` for our specific z. -/

/-- **`sin_z_lt_target`** — combining §3 (Taylor at zb), §5 (z bound), §6 (poly < target)
via sin monotonicity on `[0, π/2]`. -/
lemma sin_z_lt_target :
    Real.sin (π * (Real.sqrt 5 - 2) / 2) < (Real.sqrt 3 - 1) / 2 := by
  set z : ℝ := π * (Real.sqrt 5 - 2) / 2 with hz_def
  have hs5_gt2 : (2 : ℝ) < Real.sqrt 5 := AlphaHodgeSigmaPositive.two_lt_sqrt_five
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have hz_pos : 0 ≤ z := by
    rw [hz_def]
    have h1 : 0 < Real.sqrt 5 - 2 := by linarith
    positivity
  set zb : ℝ := 3723 / 10000 with hzb_def
  have hz_lt_zb : z < zb := by
    rw [hz_def, hzb_def]
    exact pi_mul_sqrt_five_sub_two_div_two_lt_zbound
  have hzb_pos : (0 : ℝ) < zb := by rw [hzb_def]; norm_num
  -- zb < π/2. Since zb = 0.3723 and π/2 > 1.57.
  have hzb_lt_pihalf : zb < π / 2 := by
    have := Real.pi_gt_d2
    rw [hzb_def]; linarith
  -- z ≤ zb ≤ π/2. And z ≥ 0. Use sin monotone on [-(π/2), π/2].
  have hz_le_zb : z ≤ zb := le_of_lt hz_lt_zb
  have hz_lt_pihalf : z < π / 2 := lt_of_le_of_lt hz_le_zb hzb_lt_pihalf
  have hz_mem : z ∈ Set.Icc (-(π/2)) (π/2) := by
    refine ⟨?_, ?_⟩
    · have hpp : (0 : ℝ) < π / 2 := by positivity
      linarith
    · linarith
  have hzb_mem : zb ∈ Set.Icc (-(π/2)) (π/2) := by
    refine ⟨?_, ?_⟩
    · have hpp : (0 : ℝ) < π / 2 := by positivity
      linarith
    · linarith
  -- sin is monotone on [-π/2, π/2].
  have hsin_mono : Real.sin z ≤ Real.sin zb :=
    Real.strictMonoOn_sin.monotoneOn hz_mem hzb_mem hz_le_zb
  -- Taylor at zb.
  have hzb_taylor : Real.sin zb ≤ zb - zb^3 / 6 + zb^5 / 120 :=
    sin_le_taylor_fifth_order (le_of_lt hzb_pos)
  -- Poly at zb < target.
  have htarget : zb - zb^3 / 6 + zb^5 / 120 < (Real.sqrt 3 - 1) / 2 := by
    rw [hzb_def]
    exact taylor_poly_at_zbound_lt_target
  linarith [hsin_mono, hzb_taylor, htarget]

/-! ## §8 `cos(π · φ) < (√3 − 1)/2`. -/

/-- **`cos_pi_mul_goldenRatio_lt_sqrt_three_minus_one_div_two`** — via §7 + trigonometric
identity `cos(3π/2 + z) = sin(z)` where `z = π(√5 − 2)/2`.

Chain: `π · φ = π(1+√5)/2 = π/2 + π√5/2 = 3π/2 + π(√5 − 2)/2 = 3π/2 + z`. Then
`cos(3π/2 + z) = cos(3π/2)cos(z) − sin(3π/2)sin(z) = 0·cos(z) − (−1)·sin(z) = sin(z)`. -/
lemma cos_pi_mul_goldenRatio_lt_sqrt_three_minus_one_div_two :
    Real.cos (π * Real.goldenRatio) < (Real.sqrt 3 - 1) / 2 := by
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have heq : π * Real.goldenRatio = 3 * π / 2 + π * (Real.sqrt 5 - 2) / 2 := by
    unfold Real.goldenRatio
    ring
  rw [heq]
  -- cos(3π/2 + z) = cos(3π/2) · cos(z) - sin(3π/2) · sin(z) = 0 · cos(z) - (-1) · sin(z) = sin(z).
  rw [Real.cos_add]
  have hcos : Real.cos (3 * π / 2) = 0 := by
    have h : (3 : ℝ) * π / 2 = π + π / 2 := by ring
    rw [h, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi]
    ring
  have hsin : Real.sin (3 * π / 2) = -1 := by
    have h : (3 : ℝ) * π / 2 = π + π / 2 := by ring
    rw [h, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi, Real.cos_pi]
    ring
  rw [hcos, hsin]
  have := sin_z_lt_target
  linarith

/-! ## §9 The sharp bracket `σ(α_Hodge) < 1/2`. -/

/-- **`sigma_alphaHodge_lt_half`** — the tighter α_Hodge upper bracket.

`σ(α_Hodge = φ) < 1/2`. Sharpens r243's `σ_Hodge < log 2/log 3 ≈ 0.631`
to `σ_Hodge < 1/2 = 0.5`. -/
theorem sigma_alphaHodge_lt_half :
    PrincipiaTractalis.SigmaAbscissa.sigma Real.goldenRatio < 1 / 2 := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  have hcos_pos := cos_pi_mul_goldenRatio_pos
  have hcos_lt := cos_pi_mul_goldenRatio_lt_sqrt_three_minus_one_div_two
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hs3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)
  have hs3_gt_one : (1 : ℝ) < Real.sqrt 3 := by
    have h : Real.sqrt 1 < Real.sqrt 3 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using h
  have hval_pos : 0 < 1 + 2 * Real.cos (π * Real.goldenRatio) := by linarith
  have hval_lt_sqrt3 : 1 + 2 * Real.cos (π * Real.goldenRatio) < Real.sqrt 3 := by
    linarith
  rw [abs_of_pos hval_pos]
  -- σ = logb 3 x < 1/2 ⟺ x < 3^(1/2) = √3.
  have hstep : Real.logb 3 (1 + 2 * Real.cos (π * Real.goldenRatio)) < Real.logb 3 (Real.sqrt 3) :=
    Real.logb_lt_logb (by norm_num : (1:ℝ) < 3) hval_pos hval_lt_sqrt3
  have hlog_sqrt3 : Real.logb 3 (Real.sqrt 3) = 1 / 2 := by
    have h_sqrt3_sq : Real.sqrt 3 ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    have h_sqrt3_pos : 0 < Real.sqrt 3 :=
      Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)
    have hstep2 : Real.logb 3 (Real.sqrt 3 ^ 2) = 2 * Real.logb 3 (Real.sqrt 3) := by
      rw [Real.logb_pow]; ring
    rw [h_sqrt3_sq] at hstep2
    have hself : Real.logb 3 3 = 1 :=
      Real.logb_self_eq_one (by norm_num : (1:ℝ) < 3)
    linarith
  linarith [hlog_sqrt3 ▸ hstep]

/-! ## §10 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaHodgeTighterHalfBracket.sin_ge_x_sub_cube_div_six
#print axioms PrincipiaTractalis.AlphaHodgeTighterHalfBracket.cos_le_one_sub_sq_div_two_add_fourth_div_twenty_four
#print axioms PrincipiaTractalis.AlphaHodgeTighterHalfBracket.sin_le_taylor_fifth_order
#print axioms PrincipiaTractalis.AlphaHodgeTighterHalfBracket.sigma_alphaHodge_lt_half

end PrincipiaTractalis.AlphaHodgeTighterHalfBracket
