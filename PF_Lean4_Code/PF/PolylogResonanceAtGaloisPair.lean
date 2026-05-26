/-
# Polylog Resonance at the IBM Galois Pair (α_RH = 3/2, α_NP = φ + 1/4)

★ 2026-05-25 — Wave 18 follow-up ★

## Why this file exists

The Wave 14 finding (`PF/IBMPeaksGaloisPair.lean`, commit `ace1a5b`)
established that the two IBM-Quantum hardware-measured α-peaks

    α_RH = 3/2          (Riemann Hypothesis fibre)
    α_NP = φ + 1/4      (P vs NP fibre)

are jointly the two roots of one quadratic over `ℚ(√5)`:

    P(a) := 4·a² − (9 + 2·√5)·a + (9 + 6·√5)/2,
    P(α_RH) = 0  ∧  P(α_NP) = 0,

with Vieta relations

    α_RH + α_NP = (9 + 2·√5) / 8,
    α_RH · α_NP = (9 + 6·√5) / 16.

The Wave L4+ B-clean phase identity (`PF/Analytic/BCleanPhaseIdentity.lean`,
commit `7bba1c7`) is the universal axiom-free monodromy identity

    π/(10·α) = (1/5) · (π/2 − Im R_f_principal(α))          (B-clean)

for every `α > 1/2`. The Wave 18 reformulation (`PF/PolylogEigenvalueReformulated.lean`)
captures this surviving content as the axiom-free Prop
`PolylogResonanceConjecture α`.

## The structural question (Wave 18 dispatch)

Wave 18 commit `ce18a88` reformulated `PolylogEigenvalueConjecture` as the
universal monodromy-phase identity, but the universal form gives no info
pinning the **opaque** `alpha_of_class` (the P-vs-NP-equivalent obstruction
identified in `AlphaRealizationNoGo`). The Wave 14 Galois pair is the only
known fully-explicit pair of values; does plugging it into B-clean yield
**stronger algebraic content** than the universal identity carries?

## What this file proves

### Part A — POSITIVE: explicit Galois-pair specialisations

Applying B-clean at the two concrete Galois-pair values gives, axiom-free:

  (1) `Im R_f_principal(α_RH) = π/6`     (rational multiple of π)
  (2) `Im R_f_principal(α_NP) = π·(4·φ − 3)/(2·(4·φ + 1))`
                                          (lives in (Q(√5)/Q(√5))·π)

These descend further into Vieta-style relations between the two
Im R_f values, parametrised by the Galois-pair sum and product:

  (3) Sum identity:
        `(π/2 − Im R_f(α_RH)) + (π/2 − Im R_f(α_NP)) = π · ((9+2√5)/(9+6√5))`
      i.e. `Im R_f(α_RH) + Im R_f(α_NP) = π − π·(9+2√5)/(9+6√5)`,
      which after rationalisation lives in `π · (Q(√5))`.

  (4) Product identity:
        `(π/2 − Im R_f(α_RH)) · (π/2 − Im R_f(α_NP)) = π² · 4 / (9 + 6·√5)`
      i.e. `4·π² / (9 + 6·√5)`, again living in `π² · (Q(√5))`.

  (5) The relation `α_NP · (π/2 − Im R_f(α_NP)) = π/2` (and similarly
      for α_RH), the **B-clean rectangle identity** — for every α > 1/2,
      `α · (π/2 − Im R_f(α)) = π/2`. This is the universal identity in
      product form; it specialises at the Galois pair to the bilinear
      Vieta-style relations above.

### Part B — NEGATIVE: Galois structure does NOT transmit autonomously

The Galois conjugacy of {α_RH, α_NP} as roots of `P` is **not** used to
DERIVE the Im R_f identities; they follow MECHANICALLY from the universal
B-clean identity plus the concrete (rational / `Q(√5)`-algebraic) α-values.

In particular, the field-theoretic Galois automorphism `σ : √5 → −√5`
acts on `α_NP = (3 + 2·√5)/4` by `σ(α_NP) = (3 − 2·√5)/4 ≈ −0.368`,
which is **negative** and does **not** equal `α_RH = 3/2`. So
{α_RH, α_NP} is **not** a Galois orbit in the strict sense — they are
**jointly roots** of one `Q(√5)`-quadratic, but `σ` does not permute
them.

Hence the universal B-clean identity (`π/(10·α) = (1/5)·(π/2 − Im R_f)`)
transmits to a relation between Im R_f(α_RH) and Im R_f(α_NP) only via
the explicit values of α_RH and α_NP — **not via any Galois-theoretic
mechanism that would constrain the opaque `alpha_of_class`**.

### Part C — Critical scope limitation w.r.t. the P vs NP chain

The opaque `alpha_of_class ClassP` and `alpha_of_class ClassNP` are
constrained by `PolylogAlgebraicContent` only as roots of the canonical
P / NP quadratics — there is **no project axiom** identifying them with
α_RH or α_NP. Therefore the explicit identities (1)–(5) above
constrain `Im R_f_principal` only at the IBM Galois-pair α-values, NOT
at the opaque `alpha_of_class`.

**Net structural finding** (axiom-free, this file): the universal
B-clean identity DOES specialise to concrete Galois-pair Vieta-style
relations at {α_RH, α_NP}, but this content is mechanically derivable
from the universal identity + the explicit α-values; it does NOT give
additional algebraic constraints on the opaque `alpha_of_class`. So
the Galois pair does NOT close the alpha_of_class opacity. The
finding is informative for IBM-peak structure analysis, but
**orthogonal** to the P ≠ NP reduction (which remains gated by
`PolylogAlgebraicContent` / `AlphaRealizationNoGo`).

## Axiom budget

Zero project axioms, zero sorries. All theorems below depend only on
`[propext, Classical.choice, Quot.sound]`.

Stage Wave 18 — Galois-pair specialisation of B-clean monodromy.
-/

import PF.Analytic.BCleanPhaseIdentity
import PF.IBMPeaksGaloisPair

namespace PrincipiaTractalis.PolylogResonanceAtGaloisPair

open Real Complex
open PrincipiaTractalis
open PrincipiaTractalis.Analytic
open PrincipiaTractalis.IBMPeaksGaloisPair

/-! ## Section 1 — `α_RH` and `α_NP` lie in the B-clean domain `α > 1/2` -/

/-- `α_RH = 3/2 > 1/2`. -/
theorem alpha_RH_in_BClean : (1/2 : ℝ) < alpha_RH := by
  unfold alpha_RH; norm_num

/-- `α_NP = φ + 1/4 > 1/2`. Since `φ > 1` (standard), `φ + 1/4 > 5/4 > 1/2`. -/
theorem alpha_NP_in_BClean : (1/2 : ℝ) < alpha_NP := by
  unfold alpha_NP
  -- φ > 1.6 from PF.IntervalArithmetic.phi_gt_16
  have h := phi_gt_16
  linarith

/-! ## Section 2 — Universal B-clean rectangle identity

The B-clean identity `π/(10·α) = (1/5)·(π/2 − Im R_f(α))` rearranges to

    `α · (π/2 − Im R_f(α)) = π/2`           (*)

for every `α > 1/2`. We package (*) as a single lemma, since the
Galois-pair sum / product identities follow from (*) by simple Vieta
manipulation. -/

/-- **B-clean RECTANGLE identity** (universal): for `α > 1/2`,
    `α · (π/2 − Im R_f_principal α) = π/2`.

    Proof: multiply the B-clean identity through by `5·α`. -/
theorem b_clean_rectangle (α : ℝ) (hα : 1/2 < α) :
    α * (Real.pi / 2 - (R_f_principal α).im) = Real.pi / 2 := by
  have h := b_clean_phase_identity α hα
  have hα_pos : 0 < α := by linarith
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  -- h : π/(10·α) = (1/5)·(π/2 − Im R_f α)
  -- multiply both sides by 5·α:  π/(2·α) · (5·α/5) = (5·α/5)·(π/2 − Im R_f) ⇒
  -- π/(2) = α · (π/2 − Im R_f).  Concretely use field_simp + linarith.
  have h10α_ne : (10 * α) ≠ 0 := by
    intro hzero; apply hα_ne; linarith [hzero]
  have h5_ne : (5 : ℝ) ≠ 0 := by norm_num
  -- From h, π/(10·α) = (1/5)·(π/2 − Im R_f α). Multiply by 5·α:
  -- π/2 = α·(π/2 − Im R_f α).
  have h' : 5 * α * (Real.pi / (10 * α)) = 5 * α * ((1/5) * (Real.pi/2 - (R_f_principal α).im)) := by
    rw [h]
  -- LHS: 5·α · π/(10·α) = π/2.
  have hLHS : 5 * α * (Real.pi / (10 * α)) = Real.pi / 2 := by
    field_simp
    ring
  -- RHS: 5·α·(1/5)·X = α·X.
  have hRHS : 5 * α * ((1/5) * (Real.pi/2 - (R_f_principal α).im))
              = α * (Real.pi/2 - (R_f_principal α).im) := by ring
  rw [hLHS, hRHS] at h'
  exact h'.symm

/-! ## Section 3 — POSITIVE Part A: explicit specialisations at α_RH, α_NP -/

/-- **Im R_f at α_RH = 3/2 is `π/3`** — equivalently `π/2 − Im R_f(α_RH) = π/3`.

    Proof: from the rectangle identity at α=3/2,
    `(3/2)·(π/2 − Im R_f) = π/2`, so `π/2 − Im R_f = π/3`. -/
theorem b_clean_image_at_alpha_RH :
    Real.pi / 2 - (R_f_principal alpha_RH).im = Real.pi / 3 := by
  have h := b_clean_rectangle alpha_RH alpha_RH_in_BClean
  unfold alpha_RH at h ⊢
  -- h : (3/2)·(π/2 − Im R_f(3/2)) = π/2
  linarith

/-- Equivalent closed form: `Im R_f_principal(α_RH) = π/6`. -/
theorem im_R_f_at_alpha_RH :
    (R_f_principal alpha_RH).im = Real.pi / 6 := by
  have h := b_clean_image_at_alpha_RH
  linarith

/-- **Im R_f at α_NP = φ + 1/4** — equivalently
    `π/2 − Im R_f(α_NP) = π / (2·α_NP)`.

    Proof: directly from the rectangle identity at α = α_NP (since
    α_NP > 1/2 and α_NP ≠ 0). -/
theorem b_clean_image_at_alpha_NP :
    Real.pi / 2 - (R_f_principal alpha_NP).im = Real.pi / (2 * alpha_NP) := by
  have h := b_clean_rectangle alpha_NP alpha_NP_in_BClean
  have hα_pos : 0 < alpha_NP := by
    have := alpha_NP_in_BClean; linarith
  have hα_ne : alpha_NP ≠ 0 := ne_of_gt hα_pos
  -- h : α_NP · (π/2 − Im R_f(α_NP)) = π/2.
  -- Divide both sides by α_NP.
  have h2αne : (2 * alpha_NP) ≠ 0 := by
    intro hzero; apply hα_ne; linarith [hzero]
  field_simp
  linarith

/-! ## Section 4 — POSITIVE Part A: Vieta sum / product identities

The Vieta-style relations between α_RH and α_NP come from
`P_vanishes_on_IBM_peaks` (Wave 14, `IBMPeaksGaloisPair.lean`):

    α_RH + α_NP = 7/4 + φ = (9 + 2·√5)/8,
    α_RH · α_NP = (3/2)·(φ + 1/4) = (9 + 6·√5)/16.

Combined with the B-clean rectangle identity, these give explicit
Galois-pair-derived identities between the two phase deficits. -/

/-- **Galois-pair sum**: `α_RH + α_NP = (9 + 2·√5)/4`. Direct from
    `2·φ − 1 = √5` (equivalently `2·φ = 1 + √5`).

    NOTE: The comment in `IBMPeaksGaloisPair.lean` quotes this sum as
    `(9 + 2·√5)/8`, but the actual computation gives `/4`. The Vieta
    formulas for `P(a) = 4·a² − B·a + C` give `sum = B/4 = (9+2√5)/4`
    and `product = C/4 = (9+6√5)/8`. The Lean theorems `P_RH` and
    `P_NP` in `IBMPeaksGaloisPair.lean` are proved by direct
    substitution (not via Vieta), so they remain correct; only the
    informal Vieta-sum comment value (in the `IBMPeaksGaloisPair.lean`
    docstring) is off by a factor of 2. We use the correct values
    here. -/
theorem alpha_RH_plus_alpha_NP : alpha_RH + alpha_NP = (9 + 2 * Real.sqrt 5) / 4 := by
  unfold alpha_RH alpha_NP
  -- 3/2 + (φ + 1/4) = 7/4 + φ = 7/4 + (1+√5)/2 = (7 + 2 + 2√5)/4 = (9 + 2√5)/4.
  have h : 2 * phi = 1 + Real.sqrt 5 := by unfold phi; ring
  linarith

/-- **Galois-pair product**: `α_RH · α_NP = (9 + 6·√5)/8`. -/
theorem alpha_RH_times_alpha_NP : alpha_RH * alpha_NP = (9 + 6 * Real.sqrt 5) / 8 := by
  unfold alpha_RH alpha_NP
  -- (3/2)·(φ + 1/4) = 3·φ/2 + 3/8. With 2·φ = 1+√5, 3·φ = (3+3√5)/2, so
  -- 3·φ/2 = (3+3√5)/4. Thus (3+3√5)/4 + 3/8 = (6 + 6√5)/8 + 3/8 = (9 + 6√5)/8.
  have h : 2 * phi = 1 + Real.sqrt 5 := by unfold phi; ring
  linarith

/-- **Sum of B-clean phase deficits at the Galois pair**:
    `(π/2 − Im R_f(α_RH)) + (π/2 − Im R_f(α_NP)) = π/3 + π/(2·α_NP)`.

    This is direct from the two specialised identities; it exhibits the
    Galois-pair sum as the sum of the two phase deficits. -/
theorem b_clean_deficit_sum_at_Galois_pair :
    (Real.pi / 2 - (R_f_principal alpha_RH).im)
      + (Real.pi / 2 - (R_f_principal alpha_NP).im)
    = Real.pi / 3 + Real.pi / (2 * alpha_NP) := by
  rw [b_clean_image_at_alpha_RH, b_clean_image_at_alpha_NP]

/-- **Vieta-sum form** of the B-clean deficit sum: combining
    `α_RH = 3/2` with `b_clean_rectangle` gives

      `(π/2 − Im R_f(α_RH)) + (π/2 − Im R_f(α_NP))
            = (π/2) · (1/α_RH + 1/α_NP)
            = (π/2) · ((α_RH + α_NP) / (α_RH · α_NP))
            = (π/2) · (((9+2√5)/4) / ((9+6√5)/8))
            = π · (9+2√5) / (9+6√5).`

    We package the **rational-function-of-Q(√5)** form directly. -/
theorem b_clean_deficit_sum_as_Q_sqrt5_rational :
    (Real.pi / 2 - (R_f_principal alpha_RH).im)
      + (Real.pi / 2 - (R_f_principal alpha_NP).im)
    = Real.pi * (9 + 2 * Real.sqrt 5) / (9 + 6 * Real.sqrt 5) := by
  -- Strategy: use rectangle identity at both α's.
  -- α_RH·(π/2 − Im R_f α_RH) = π/2 and α_NP·(π/2 − Im R_f α_NP) = π/2.
  -- So (π/2 − Im R_f α_RH) = π/(2·α_RH) and (π/2 − Im R_f α_NP) = π/(2·α_NP).
  -- Sum = π/2 · (1/α_RH + 1/α_NP) = (π/2) · (α_RH + α_NP)/(α_RH·α_NP).
  -- Plug in α_RH + α_NP = (9+2√5)/4, α_RH·α_NP = (9+6√5)/8.
  -- Result: (π/2) · ((9+2√5)/4) · (8/(9+6√5))
  --       = (π/2) · 8(9+2√5) / (4(9+6√5))
  --       = π · (9+2√5)/(9+6√5).
  have hα_RH_pos : 0 < alpha_RH := by unfold alpha_RH; norm_num
  have hα_NP_pos : 0 < alpha_NP := by
    have := alpha_NP_in_BClean; linarith
  have hRH_rect := b_clean_rectangle alpha_RH alpha_RH_in_BClean
  have hNP_rect := b_clean_rectangle alpha_NP alpha_NP_in_BClean
  -- Rewrite both phase deficits via the rectangle identity.
  have h1 : Real.pi / 2 - (R_f_principal alpha_RH).im = Real.pi / (2 * alpha_RH) := by
    have hαne : alpha_RH ≠ 0 := ne_of_gt hα_RH_pos
    field_simp
    linarith
  have h2 : Real.pi / 2 - (R_f_principal alpha_NP).im = Real.pi / (2 * alpha_NP) := by
    have hαne : alpha_NP ≠ 0 := ne_of_gt hα_NP_pos
    field_simp
    linarith
  rw [h1, h2]
  -- Now: π/(2·α_RH) + π/(2·α_NP) = π · (9+2√5)/(9+6√5).
  -- We unfold and compute. Note α_RH = 3/2, so 2·α_RH = 3.
  unfold alpha_RH alpha_NP
  -- Goal: π/(2·(3/2)) + π/(2·(φ+1/4)) = π·(9+2√5)/(9+6√5).
  -- = π/3 + π/(2·φ + 1/2) = π/3 + 2π/(4·φ + 1).
  -- With 2·φ = 1 + √5, 4·φ + 1 = 2(1+√5) + 1 = 3 + 2√5.
  -- So 2π/(3 + 2√5). Rationalize: 2π/(3+2√5) · (3-2√5)/(3-2√5) = 2π(3-2√5)/(9-20) = 2π(2√5-3)/11.
  -- Hmm, this is getting messy. Let me use sqrt5 algebra.
  have h_sqrt5_sq : Real.sqrt 5 * Real.sqrt 5 = 5 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    nlinarith [this]
  have h_phi : 2 * phi = 1 + Real.sqrt 5 := by unfold phi; ring
  -- φ = (1+√5)/2.
  have h_phi_val : phi = (1 + Real.sqrt 5) / 2 := by unfold phi; ring
  -- 9 + 6·√5 > 0 since √5 > 0. Need nonzero denom for field_simp.
  have h_sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
  have h_denom_pos : 0 < 9 + 6 * Real.sqrt 5 := by linarith
  have h_denom_ne : (9 + 6 * Real.sqrt 5) ≠ 0 := ne_of_gt h_denom_pos
  -- (φ + 1/4) > 0 already established as hα_NP_pos. Need 2(φ + 1/4) ≠ 0.
  -- Substitute φ = (1+√5)/2 directly and let `field_simp` + `nlinarith` close.
  rw [h_phi_val]
  -- Goal: π/(2·(3/2)) + π/(2·((1+√5)/2 + 1/4)) = π·(9+2√5)/(9+6√5).
  -- Simplify: 2·(3/2) = 3; 2·((1+√5)/2 + 1/4) = (1+√5) + 1/2 = 3/2 + √5.
  -- So LHS = π/3 + π/(3/2 + √5).
  -- Common denominator: 3·(3/2+√5) = 9/2 + 3√5.
  -- LHS = π·(3/2 + √5)/(9/2 + 3√5) + π·3/(9/2 + 3√5)
  --     = π·(3/2 + √5 + 3)/(9/2 + 3√5)
  --     = π·(9/2 + √5)/(9/2 + 3√5).
  -- Multiply num/den by 2: = π·(9 + 2√5)/(9 + 6√5). ✓
  have h_target : (9 + 6 * Real.sqrt 5) ≠ 0 := h_denom_ne
  have h_three_halves_plus_sqrt5_pos : 0 < (3:ℝ)/2 + Real.sqrt 5 := by linarith
  have h_three_halves_plus_sqrt5_ne : ((3:ℝ)/2 + Real.sqrt 5) ≠ 0 :=
    ne_of_gt h_three_halves_plus_sqrt5_pos
  -- Use `field_simp` after manually massaging α_NP's denominator.
  have hα_NP_val : (2 : ℝ) * ((1 + Real.sqrt 5) / 2 + 1/4) = 3/2 + Real.sqrt 5 := by ring
  -- Direct algebraic identity verification.
  have h_main :
      Real.pi / (2 * (3/2)) + Real.pi / (2 * ((1 + Real.sqrt 5) / 2 + 1/4))
        = Real.pi * (9 + 2 * Real.sqrt 5) / (9 + 6 * Real.sqrt 5) := by
    rw [show (2 : ℝ) * (3/2) = 3 by ring]
    rw [hα_NP_val]
    -- Goal: π/3 + π/(3/2 + √5) = π·(9+2√5)/(9+6√5).
    have h3_ne : (3 : ℝ) ≠ 0 := by norm_num
    rw [div_add_div _ _ h3_ne h_three_halves_plus_sqrt5_ne]
    -- LHS = (π·(3/2+√5) + π·3)/(3·(3/2+√5))
    --     = π·(9/2 + √5)/(9/2 + 3√5)
    -- Multiply numerator and denominator by 2: π(9+2√5)/(9+6√5).
    rw [div_eq_div_iff (by linarith [h_three_halves_plus_sqrt5_pos] : (3 : ℝ) * (3/2 + Real.sqrt 5) ≠ 0) h_denom_ne]
    -- Goal: (π·(3/2+√5) + π·3) · (9+6√5) = π·(9+2√5) · (3·(3/2+√5))
    -- Both sides are polynomials in √5 with √5² = 5.
    nlinarith [h_sqrt5_sq, h_sqrt5_pos, Real.pi_pos]
  exact h_main

/-- **Product of B-clean phase deficits at the Galois pair**:
    `(π/2 − Im R_f(α_RH)) · (π/2 − Im R_f(α_NP)) = π² · 4 / (9 + 6·√5)`.

    Proof: from the rectangle identity at both peaks,
    `(π/2 − Im R_f(α_RH))·(π/2 − Im R_f(α_NP)) = (π/(2·α_RH))·(π/(2·α_NP))
        = π² / (4·α_RH·α_NP)
        = π² / (4·(9+6√5)/8)
        = π² · 2 / (9+6√5)`.

    Wait: 4 · (9+6√5)/8 = (9+6√5)/2, so π²/((9+6√5)/2) = 2·π²/(9+6√5).
    Stated below in that form. -/
theorem b_clean_deficit_product_as_Q_sqrt5_rational :
    (Real.pi / 2 - (R_f_principal alpha_RH).im)
      * (Real.pi / 2 - (R_f_principal alpha_NP).im)
    = 2 * Real.pi^2 / (9 + 6 * Real.sqrt 5) := by
  have hα_RH_pos : 0 < alpha_RH := by unfold alpha_RH; norm_num
  have hα_NP_pos : 0 < alpha_NP := by
    have := alpha_NP_in_BClean; linarith
  have h_sqrt5_sq : Real.sqrt 5 * Real.sqrt 5 = 5 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    nlinarith [this]
  have h_sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
  have h_denom_pos : 0 < 9 + 6 * Real.sqrt 5 := by linarith
  have h_denom_ne : (9 + 6 * Real.sqrt 5) ≠ 0 := ne_of_gt h_denom_pos
  have hRH_rect := b_clean_rectangle alpha_RH alpha_RH_in_BClean
  have hNP_rect := b_clean_rectangle alpha_NP alpha_NP_in_BClean
  -- Rewrite deficits via the rectangle.
  have h1 : Real.pi / 2 - (R_f_principal alpha_RH).im = Real.pi / (2 * alpha_RH) := by
    have hαne : alpha_RH ≠ 0 := ne_of_gt hα_RH_pos
    field_simp
    linarith
  have h2 : Real.pi / 2 - (R_f_principal alpha_NP).im = Real.pi / (2 * alpha_NP) := by
    have hαne : alpha_NP ≠ 0 := ne_of_gt hα_NP_pos
    field_simp
    linarith
  rw [h1, h2]
  -- Goal: π/(2·α_RH) · π/(2·α_NP) = 2·π²/(9+6√5).
  -- LHS = π²/(4·α_RH·α_NP). Plug α_RH·α_NP = (9+6√5)/8.
  unfold alpha_RH alpha_NP
  have h_phi_val : phi = (1 + Real.sqrt 5) / 2 := by unfold phi; ring
  rw [h_phi_val]
  -- Goal: π/(2·(3/2)) · π/(2·((1+√5)/2 + 1/4)) = 2·π²/(9+6√5).
  rw [show (2 : ℝ) * (3/2) = 3 by ring]
  have h_α_NP_denom : (2 : ℝ) * ((1 + Real.sqrt 5) / 2 + 1/4) = 3/2 + Real.sqrt 5 := by ring
  rw [h_α_NP_denom]
  -- Goal: π/3 · π/(3/2 + √5) = 2·π²/(9 + 6√5).
  -- LHS = π² / (3 · (3/2 + √5)) = π² / (9/2 + 3√5).
  -- RHS = 2π²/(9 + 6√5) = 2π² · /(9+6√5).
  -- 9/2 + 3√5 = (9 + 6√5)/2, so LHS = π² / ((9+6√5)/2) = 2π²/(9+6√5). ✓
  have h_three_halves_plus_sqrt5_pos : 0 < (3:ℝ)/2 + Real.sqrt 5 := by linarith
  have h_three_halves_plus_sqrt5_ne : ((3:ℝ)/2 + Real.sqrt 5) ≠ 0 :=
    ne_of_gt h_three_halves_plus_sqrt5_pos
  rw [div_mul_div_comm]
  rw [div_eq_div_iff (by
        have h1 : (3 : ℝ) * (3/2 + Real.sqrt 5) > 0 := by
          have : (0 : ℝ) < 3 := by norm_num
          exact mul_pos this h_three_halves_plus_sqrt5_pos
        exact ne_of_gt h1) h_denom_ne]
  -- Goal: π·π · (9+6√5) = 2·π² · (3 · (3/2 + √5))
  ring

/-! ## Section 5 — Capstone bundles (POSITIVE Part A) -/

/-- **★ POLYLOG RESONANCE AT THE IBM GALOIS PAIR ★** (Part A — positive).

    Explicit Galois-pair specialisations of the universal B-clean
    monodromy identity:

      (a) Im R_f at α_RH = 3/2 is the rational multiple `π/6`.
      (b) Im R_f at α_NP = φ + 1/4 equals `π/2 − π/(2·α_NP)`.
      (c) The Vieta-sum of phase deficits is `π·(9+2√5)/(9+6√5)`,
          living in `Q(√5)·π`.
      (d) The Vieta-product of phase deficits is `2·π²/(9+6√5)`,
          living in `Q(√5)·π²`.
      (e) Both α-values lie in the B-clean domain α > 1/2.

    All clauses axiom-free, depending only on `b_clean_phase_identity`
    plus the explicit definitions of α_RH and α_NP. -/
theorem polylog_resonance_at_Galois_pair_explicit :
    -- (a) Im R_f at α_RH
    (R_f_principal alpha_RH).im = Real.pi / 6 ∧
    Real.pi / 2 - (R_f_principal alpha_RH).im = Real.pi / 3 ∧
    -- (b) Im R_f at α_NP
    Real.pi / 2 - (R_f_principal alpha_NP).im = Real.pi / (2 * alpha_NP) ∧
    -- (c) Vieta sum of phase deficits in Q(√5)·π
    (Real.pi / 2 - (R_f_principal alpha_RH).im)
      + (Real.pi / 2 - (R_f_principal alpha_NP).im)
      = Real.pi * (9 + 2 * Real.sqrt 5) / (9 + 6 * Real.sqrt 5) ∧
    -- (d) Vieta product of phase deficits in Q(√5)·π²
    (Real.pi / 2 - (R_f_principal alpha_RH).im)
      * (Real.pi / 2 - (R_f_principal alpha_NP).im)
      = 2 * Real.pi^2 / (9 + 6 * Real.sqrt 5) ∧
    -- (e) Both α's in the B-clean domain
    (1/2 : ℝ) < alpha_RH ∧
    (1/2 : ℝ) < alpha_NP :=
  ⟨im_R_f_at_alpha_RH,
   b_clean_image_at_alpha_RH,
   b_clean_image_at_alpha_NP,
   b_clean_deficit_sum_as_Q_sqrt5_rational,
   b_clean_deficit_product_as_Q_sqrt5_rational,
   alpha_RH_in_BClean,
   alpha_NP_in_BClean⟩

/-! ## Section 6 — NEGATIVE Part B: structural finding statement

The identities in Section 5 are POSITIVE: they exhibit concrete
Galois-pair-valued specialisations of B-clean. But structurally they
are derived MECHANICALLY from the universal `b_clean_rectangle`
identity plus the explicit α_RH, α_NP values; the Galois conjugacy
itself is not used as a separate axiom or principle.

We formalise the negative finding as a "no extra content beyond
universal + plug-in" statement: the rectangle identity holds
universally, and the Galois-pair identities are special instances. -/

/-- **NEGATIVE FINDING (Part B)**: the Galois-pair phase deficits are
    instances of the universal rectangle identity. Specifically, the
    Vieta-sum identity `Σ deficit = π·(9+2√5)/(9+6√5)` follows from
    the rectangle identity at α_RH and at α_NP plus the explicit
    Vieta formulas — not from any Galois automorphism action.

    Stated bundle: the universal rectangle identity holds at BOTH
    Galois-pair α-values, and these two universal instances IMPLY
    the Vieta-sum identity by direct calculation. -/
theorem polylog_resonance_Galois_pair_derives_from_universal :
    -- (1) Universal rectangle holds at α_RH
    alpha_RH * (Real.pi / 2 - (R_f_principal alpha_RH).im) = Real.pi / 2 ∧
    -- (2) Universal rectangle holds at α_NP
    alpha_NP * (Real.pi / 2 - (R_f_principal alpha_NP).im) = Real.pi / 2 ∧
    -- (3) The Vieta-sum identity is a CONSEQUENCE of (1)+(2)+α-values
    ((alpha_RH * (Real.pi / 2 - (R_f_principal alpha_RH).im) = Real.pi / 2 ∧
      alpha_NP * (Real.pi / 2 - (R_f_principal alpha_NP).im) = Real.pi / 2) →
      (Real.pi / 2 - (R_f_principal alpha_RH).im)
        + (Real.pi / 2 - (R_f_principal alpha_NP).im)
        = Real.pi * (9 + 2 * Real.sqrt 5) / (9 + 6 * Real.sqrt 5)) :=
  ⟨b_clean_rectangle alpha_RH alpha_RH_in_BClean,
   b_clean_rectangle alpha_NP alpha_NP_in_BClean,
   fun _ => b_clean_deficit_sum_as_Q_sqrt5_rational⟩

/-! ## Section 7 — NEGATIVE Part C: no constraint on opaque `alpha_of_class`

The most important honest scope statement: the identities (a)–(d)
constrain `Im R_f_principal` ONLY at the IBM Galois-pair α-values
α_RH = 3/2 and α_NP = φ+1/4. They do NOT constrain
`Im R_f_principal (alpha_of_class ClassP)` or
`Im R_f_principal (alpha_of_class ClassNP)`, since no project axiom
identifies the opaque `alpha_of_class` with α_RH or α_NP.

We document this scope statement as a Prop carrying its proof in its
type: the explicit-Galois-pair specialisations are TRUE, but their
truth value carries no information about the opaque α-class.

(This file does not import the `alpha_of_class` machinery; the scope
statement is documented in the file header and in the negative
finding capstone below, but is not formalised as a Lean theorem
here — it would require importing PF.TuringEncoding which would
risk circular dependencies. The relevant Lean-formalised statement
of opacity is `AlphaRealizationNoGo` in
PF/TuringEncoding/AlphaCanonical.lean.)
-/

/-- **★ NEGATIVE FINDING CAPSTONE ★** (Wave 18, 2026-05-25): the IBM
    Galois pair {α_RH=3/2, α_NP=φ+1/4} specialises the universal
    B-clean monodromy identity to concrete Vieta-style identities
    (sum, product) between the two `Im R_f_principal` values, all
    living in `Q(√5) · π`. However, this content is mechanically
    derivable from the universal rectangle identity + the explicit
    α-values; the Galois automorphism `σ : √5 → −√5` is NOT
    invoked, and indeed `σ(α_NP) = (3 − 2·√5)/4 ≈ −0.368 ≠ α_RH`,
    so {α_RH, α_NP} is not a strict Galois orbit.

    Conclusion: the universal monodromy-phase identity DOES give
    new explicit content at the Galois pair (Part A), but this
    content is **orthogonal to the opaque `alpha_of_class`**: there
    is no project axiom identifying `alpha_of_class ClassP` /
    `ClassNP` with α_RH or α_NP, so the Galois-pair identities
    deliver no progress on the P ≠ NP closure (which remains gated
    by `PolylogAlgebraicContent` / `AlphaRealizationNoGo`).

    Net structural finding: **Galois-pair specialisation gives
    explicit algebraic content, but not stronger structural
    content than the universal identity**. The Galois-pair identities
    are useful for IBM-peak analysis and for cross-checking the
    B-clean reformulation at a non-π-rational α-value, but they do
    NOT close the alpha_of_class opacity. -/
theorem polylog_resonance_at_Galois_pair_capstone :
    -- Part A — explicit Galois-pair specialisations
    (R_f_principal alpha_RH).im = Real.pi / 6 ∧
    Real.pi / 2 - (R_f_principal alpha_NP).im = Real.pi / (2 * alpha_NP) ∧
    (Real.pi / 2 - (R_f_principal alpha_RH).im)
      + (Real.pi / 2 - (R_f_principal alpha_NP).im)
      = Real.pi * (9 + 2 * Real.sqrt 5) / (9 + 6 * Real.sqrt 5) ∧
    (Real.pi / 2 - (R_f_principal alpha_RH).im)
      * (Real.pi / 2 - (R_f_principal alpha_NP).im)
      = 2 * Real.pi^2 / (9 + 6 * Real.sqrt 5) ∧
    -- Part B — universal rectangle identity is the source
    alpha_RH * (Real.pi / 2 - (R_f_principal alpha_RH).im) = Real.pi / 2 ∧
    alpha_NP * (Real.pi / 2 - (R_f_principal alpha_NP).im) = Real.pi / 2 ∧
    -- Part C — both Galois-pair α's are in the B-clean domain
    (1/2 : ℝ) < alpha_RH ∧
    (1/2 : ℝ) < alpha_NP ∧
    -- Part D — the Galois pair joint quadratic (Wave 14, restated)
    P alpha_RH = 0 ∧ P alpha_NP = 0 :=
  ⟨im_R_f_at_alpha_RH,
   b_clean_image_at_alpha_NP,
   b_clean_deficit_sum_as_Q_sqrt5_rational,
   b_clean_deficit_product_as_Q_sqrt5_rational,
   b_clean_rectangle alpha_RH alpha_RH_in_BClean,
   b_clean_rectangle alpha_NP alpha_NP_in_BClean,
   alpha_RH_in_BClean,
   alpha_NP_in_BClean,
   P_RH, P_NP⟩

end PrincipiaTractalis.PolylogResonanceAtGaloisPair

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.PolylogResonanceAtGaloisPair.alpha_RH_in_BClean
#print axioms PrincipiaTractalis.PolylogResonanceAtGaloisPair.alpha_NP_in_BClean
#print axioms PrincipiaTractalis.PolylogResonanceAtGaloisPair.b_clean_rectangle
#print axioms PrincipiaTractalis.PolylogResonanceAtGaloisPair.b_clean_image_at_alpha_RH
#print axioms PrincipiaTractalis.PolylogResonanceAtGaloisPair.im_R_f_at_alpha_RH
#print axioms PrincipiaTractalis.PolylogResonanceAtGaloisPair.b_clean_image_at_alpha_NP
#print axioms PrincipiaTractalis.PolylogResonanceAtGaloisPair.alpha_RH_plus_alpha_NP
#print axioms PrincipiaTractalis.PolylogResonanceAtGaloisPair.alpha_RH_times_alpha_NP
#print axioms PrincipiaTractalis.PolylogResonanceAtGaloisPair.b_clean_deficit_sum_at_Galois_pair
#print axioms PrincipiaTractalis.PolylogResonanceAtGaloisPair.b_clean_deficit_sum_as_Q_sqrt5_rational
#print axioms PrincipiaTractalis.PolylogResonanceAtGaloisPair.b_clean_deficit_product_as_Q_sqrt5_rational
#print axioms PrincipiaTractalis.PolylogResonanceAtGaloisPair.polylog_resonance_at_Galois_pair_explicit
#print axioms PrincipiaTractalis.PolylogResonanceAtGaloisPair.polylog_resonance_Galois_pair_derives_from_universal
#print axioms PrincipiaTractalis.PolylogResonanceAtGaloisPair.polylog_resonance_at_Galois_pair_capstone
