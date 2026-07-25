/-
# PF.Analytic.XiRealWitness

★★★★★ 2026-07-24 — Hardy route M1 brick (HARDY_SCOPING_2026-07-24 §6):
the Riemann Ξ-function is REAL-VALUED on the critical line, and a sign
change of it implies the Wave 58/59 atomic fact
`PositiveOnLineZetaZeroOrdinatesNonempty`.

## Goal

Wave 59 narrowed the framework's HP-positive RH residual to the SINGLE
atomic fact `PositiveOnLineZetaZeroOrdinatesNonempty` (∃ t > 0 with
`riemannZeta ⟨1/2, t⟩ = 0`; Hardy 1914 in the published literature).
This file builds the shared first milestone of BOTH candidate discharge
routes (Hardy-transform Route A and certified-numerics Route B):

  1. **Conjugation symmetry of ζ and Λ** — absent from mathlib at pin
     `v4.24.0-rc1`:
       `completedRiemannZeta₀_conj`, `completedRiemannZeta_conj`,
       `riemannZeta_conj`, `Gammaℝ_conj`.
     Proved on the halfplane `1 < re s` from the Dirichlet-series /
     Gamma-factor representation (real coefficients), then propagated to
     ALL of ℂ by the analytic identity theorem applied to the ENTIRE
     function `Λ₀` (`completedRiemannZeta₀`), using the antiholomorphic
     composition lemma `DifferentiableAt.conj_conj`. The `Λ ↔ Λ₀` and
     `ζ ↔ Λ` bridges (`completedRiemannZeta_eq`,
     `riemannZeta_def_of_ne_zero`) then transfer the symmetry with NO
     pole side-conditions (mathlib's `1/0 = 0` convention).

  2. **The real witness function**
       `Xi (t : ℝ) : ℝ := (completedRiemannZeta ⟨1/2, t⟩).re`
     with `Xi_im_eq_zero` (the imaginary part of `Λ` VANISHES on the
     critical line: conj symmetry + functional equation
     `completedRiemannZeta_one_sub`, since `conj ⟨1/2,t⟩ = 1 - ⟨1/2,t⟩`),
     `Xi_eq` (`Λ ⟨1/2,t⟩ = ↑(Xi t)`), and `continuous_Xi` (the critical
     line avoids the poles `s = 0, 1` for EVERY `t`, so `Xi` is
     continuous on ALL of ℝ).

  3. **The witness bridge**
       `xi_zero_at_pos_implies_nonempty` : a positive zero of `Xi`
         discharges the atom;
       `xi_sign_change_implies_on_line_zero` : a sign change
         `Xi a * Xi b < 0` with `0 < a < b` discharges the atom
     via the intermediate value theorem (`intermediate_value_uIcc`) and
     the Gamma-factor bridge (`ζ s = Λ s / Gammaℝ s`, so `Λ = 0 ⇒ ζ = 0`
     with no nonvanishing hypothesis needed in this direction).

## Brick value

The RH Nonempty atom is now EQUIVALENT-OR-WEAKER than a sign change of
an explicit continuous real-valued function of one real variable — a
strictly sharper reduction than the bare atom, required identically by
both Route A (Hardy 1914 slice) and Route B (certified evaluation of
`Ξ(14) < 0 < Ξ(15)`). The conjugation-symmetry lemmas are a genuine
mathlib gap and standalone upstream-PR material.

## Axiom budget

Zero project axioms, zero sorries. Theorems depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

import PF.Analytic.HilbertPolyaPositiveReductionToCountability
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

namespace PrincipiaTractalis.XiRealWitness

open PrincipiaTractalis.HilbertPolyaIdentificationBulletproof
open PrincipiaTractalis.HilbertPolyaPositiveImageRigidity
open PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability
open Complex Filter Topology Set
open scoped ComplexConjugate

/-! ## §1 — Conjugation of `cpow` on the nonnegative real ray -/

/-- `conj` passes through `π ^ w` (base `π > 0` is off the branch cut). -/
theorem pi_cpow_conj (w : ℂ) :
    (Real.pi : ℂ) ^ (conj w) = conj ((Real.pi : ℂ) ^ w) := by
  have harg : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Ne.symm Real.pi_ne_zero
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

/-- `conj` passes through `(n : ℂ) ^ w` for natural `n` (nonnegative real
    base is off the branch cut; `n = 0` included since `arg 0 = 0`). -/
theorem natCast_cpow_conj (n : ℕ) (w : ℂ) :
    (n : ℂ) ^ (conj w) = conj ((n : ℂ) ^ w) := by
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Ne.symm Real.pi_ne_zero
  rw [Complex.cpow_conj _ _ harg, Complex.conj_natCast]

/-! ## §2 — Conjugation symmetry of the Gamma factor -/

/-- **`Gammaℝ_conj`** — the Deligne archimedean factor
    `Gammaℝ s = π^(-s/2) Γ(s/2)` commutes with conjugation. -/
theorem Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul]
  have hneg : -(conj s) / 2 = conj (-s / 2) := by
    rw [map_div₀, map_neg, map_ofNat]
  have hhalf : (conj s) / 2 = conj (s / 2) := by
    rw [map_div₀, map_ofNat]
  rw [hneg, hhalf, pi_cpow_conj, Complex.Gamma_conj]

/-! ## §3 — Conjugation symmetry of `Λ` on the halfplane `1 < re s`

    On `1 < re s` the completed zeta has the representation
    `Λ s = π^(-s/2) Γ(s/2) ∑' n, 1/n^s` (mathlib
    `completedZeta_eq_tsum_of_one_lt_re`); every factor conjugates
    termwise since the Dirichlet coefficients are real. -/

theorem completedRiemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hs' : 1 < (conj s).re := by rwa [Complex.conj_re]
  rw [completedZeta_eq_tsum_of_one_lt_re hs', completedZeta_eq_tsum_of_one_lt_re hs,
    map_mul, map_mul]
  congr 1
  · congr 1
    · have hneg : -(conj s) / 2 = conj (-s / 2) := by
        rw [map_div₀, map_neg, map_ofNat]
      rw [hneg, pi_cpow_conj]
    · have hhalf : (conj s) / 2 = conj (s / 2) := by
        rw [map_div₀, map_ofNat]
      rw [hhalf, Complex.Gamma_conj]
  · have hterm : ∀ n : ℕ, 1 / (n : ℂ) ^ (conj s) = conj (1 / (n : ℂ) ^ s) := by
      intro n
      rw [natCast_cpow_conj, map_div₀, map_one]
    calc ∑' n : ℕ, 1 / (n : ℂ) ^ (conj s)
        = ∑' n : ℕ, conj (1 / (n : ℂ) ^ s) := tsum_congr hterm
      _ = conj (∑' n : ℕ, 1 / (n : ℂ) ^ s) := by
          simp only [starRingEnd_apply]
          exact tsum_star.symm

/-- Conjugation symmetry of the ENTIRE variant `Λ₀` on the halfplane,
    transported through `Λ = Λ₀ - 1/s - 1/(1-s)`
    (`completedRiemannZeta_eq`, valid for ALL `s`). -/
theorem completedRiemannZeta₀_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  have h := completedRiemannZeta_eq (conj s)
  have h' := completedRiemannZeta_eq s
  have e1 : completedRiemannZeta₀ (conj s)
      = completedRiemannZeta (conj s) + 1 / (conj s) + 1 / (1 - conj s) := by
    rw [h]; ring
  have e2 : conj (completedRiemannZeta₀ s)
      = conj (completedRiemannZeta s + 1 / s + 1 / (1 - s)) := by
    congr 1
    rw [h']; ring
  rw [e1, completedRiemannZeta_conj_of_one_lt_re hs, e2]
  simp only [map_add, map_sub, map_div₀, map_one]

/-! ## §4 — Identity-theorem propagation to all of ℂ

    `Λ₀` is entire (`differentiable_completedZeta₀`) and
    `conj ∘ Λ₀ ∘ conj` is entire (`DifferentiableAt.conj_conj`, the
    antiholomorphic-composition lemma). The two agree on the open
    halfplane `1 < re s` (§3), a neighbourhood of `2`, and `univ` is
    preconnected (convex), so they agree EVERYWHERE — the same
    identity-theorem machinery as the Wave 59 countability discharge. -/

/-- **`completedRiemannZeta₀_conj`** — conjugation symmetry of the
    entire completed zeta `Λ₀`, on ALL of ℂ. -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  have hg_diff : Differentiable ℂ
      (conj ∘ completedRiemannZeta₀ ∘ (conj : ℂ → ℂ)) := by
    intro z
    have h := (differentiable_completedZeta₀ (conj z)).conj_conj
    rwa [Complex.conj_conj] at h
  have hf : AnalyticOnNhd ℂ completedRiemannZeta₀ Set.univ :=
    differentiable_completedZeta₀.differentiableOn.analyticOnNhd isOpen_univ
  have hg : AnalyticOnNhd ℂ
      (conj ∘ completedRiemannZeta₀ ∘ (conj : ℂ → ℂ)) Set.univ :=
    hg_diff.differentiableOn.analyticOnNhd isOpen_univ
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2mem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
    simp only [Set.mem_setOf_eq, Complex.re_ofNat]
    norm_num
  have hfg : completedRiemannZeta₀
      =ᶠ[nhds (2 : ℂ)] (conj ∘ completedRiemannZeta₀ ∘ (conj : ℂ → ℂ)) := by
    filter_upwards [hopen.mem_nhds h2mem] with z hz
    simp only [Function.comp_apply]
    rw [completedRiemannZeta₀_conj_of_one_lt_re hz, Complex.conj_conj]
  have heq : Set.EqOn completedRiemannZeta₀
      (conj ∘ completedRiemannZeta₀ ∘ (conj : ℂ → ℂ)) Set.univ :=
    hf.eqOn_of_preconnected_of_eventuallyEq hg convex_univ.isPreconnected
      (Set.mem_univ (2 : ℂ)) hfg
  have h := congrArg conj (heq (Set.mem_univ s))
  simp only [Function.comp_apply, Complex.conj_conj] at h
  exact h.symm

/-- **`completedRiemannZeta_conj`** — conjugation symmetry of the
    completed Riemann zeta `Λ`, on ALL of ℂ (the poles at `0, 1` need
    no exclusion: `completedRiemannZeta_eq` is unconditional under the
    `1/0 = 0` convention). -/
theorem completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  simp only [completedRiemannZeta_eq, completedRiemannZeta₀_conj,
    map_sub, map_div₀, map_one]

/-- **`riemannZeta_conj`** — conjugation symmetry of the Riemann zeta
    function, on ALL of ℂ (at `s = 0` both sides are the real junk
    value `-1/2`). Absent from mathlib at pin `v4.24.0-rc1`. -/
theorem riemannZeta_conj (s : ℂ) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [map_zero, riemannZeta_zero, map_div₀, map_neg, map_one, map_ofNat]
  · have hs' : conj s ≠ 0 := by
      rw [starRingEnd_apply]
      exact star_ne_zero.mpr hs
    rw [riemannZeta_def_of_ne_zero hs', completedRiemannZeta_conj, Gammaℝ_conj,
      riemannZeta_def_of_ne_zero hs, map_div₀]

/-! ## §5 — The critical line: `conj s = 1 - s`, so `Λ` is self-conjugate -/

/-- On the critical line, conjugation coincides with the functional-
    equation reflection: `conj ⟨1/2, t⟩ = 1 - ⟨1/2, t⟩`. -/
theorem conj_critical_point (t : ℝ) :
    conj (⟨1/2, t⟩ : ℂ) = 1 - (⟨1/2, t⟩ : ℂ) := by
  apply Complex.ext
  · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
    norm_num
  · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im]
    norm_num

/-- `Λ` is SELF-CONJUGATE on the critical line: conjugation symmetry
    (§4) composed with the functional equation
    `completedRiemannZeta_one_sub`. -/
theorem completedRiemannZeta_critical_self_conj (t : ℝ) :
    conj (completedRiemannZeta ⟨1/2, t⟩) = completedRiemannZeta ⟨1/2, t⟩ := by
  rw [← completedRiemannZeta_conj, conj_critical_point,
    completedRiemannZeta_one_sub]

/-! ## §6 — The real witness function `Xi` -/

/-- **`Xi`** — the real-valued Riemann Ξ-witness: the real part of the
    completed zeta on the critical line. By `Xi_im_eq_zero` this is the
    WHOLE value, not a projection. -/
noncomputable def Xi (t : ℝ) : ℝ := (completedRiemannZeta ⟨1/2, t⟩).re

/-- The imaginary part of `Λ` VANISHES identically on the critical
    line. -/
theorem Xi_im_eq_zero (t : ℝ) : (completedRiemannZeta ⟨1/2, t⟩).im = 0 :=
  Complex.conj_eq_iff_im.mp (completedRiemannZeta_critical_self_conj t)

/-- **`Xi_eq`** — `Λ ⟨1/2, t⟩` IS the real number `Xi t` (coerced). -/
theorem Xi_eq (t : ℝ) :
    completedRiemannZeta ⟨1/2, t⟩ = ((Xi t : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
    rfl
  · rw [Complex.ofReal_im, Xi_im_eq_zero]

/-- The critical-line point is never the pole `s = 0`. -/
theorem critical_point_ne_zero (t : ℝ) : (⟨1/2, t⟩ : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

/-- The critical-line point is never the pole `s = 1`. -/
theorem critical_point_ne_one (t : ℝ) : (⟨1/2, t⟩ : ℂ) ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

/-- **`continuous_Xi`** — `Xi` is continuous on ALL of ℝ (the critical
    line avoids both poles of `Λ` for every `t`, including `t = 0`). -/
theorem continuous_Xi : Continuous Xi := by
  rw [continuous_iff_continuousAt]
  intro t
  have hline : ContinuousAt (fun u : ℝ => (⟨1/2, u⟩ : ℂ)) t := by
    have hrepr : (fun u : ℝ => (⟨1/2, u⟩ : ℂ))
        = fun u : ℝ => ((1/2 : ℝ) : ℂ) + (u : ℂ) * Complex.I := by
      funext u
      exact Complex.mk_eq_add_mul_I (1/2) u
    rw [hrepr]
    exact (continuous_const.add
      (Complex.continuous_ofReal.mul continuous_const)).continuousAt
  have hΛ : ContinuousAt completedRiemannZeta (⟨1/2, t⟩ : ℂ) :=
    (differentiableAt_completedZeta (critical_point_ne_zero t)
      (critical_point_ne_one t)).continuousAt
  exact Complex.continuous_re.continuousAt.comp (hΛ.comp hline)

/-! ## §7 — The witness bridge to the Wave 58/59 atom -/

/-- **`xi_zero_at_pos_implies_nonempty`** — a positive zero of `Xi`
    discharges `PositiveOnLineZetaZeroOrdinatesNonempty`. The
    Gamma-factor bridge `ζ s = Λ s / Gammaℝ s` needs NO nonvanishing
    hypothesis in this direction (`0 / x = 0`). -/
theorem xi_zero_at_pos_implies_nonempty {t : ℝ} (ht : 0 < t)
    (hXi : Xi t = 0) : PositiveOnLineZetaZeroOrdinatesNonempty := by
  have hΛ : completedRiemannZeta ⟨1/2, t⟩ = 0 := by
    rw [Xi_eq t, hXi, Complex.ofReal_zero]
  have hζ : riemannZeta ⟨1/2, t⟩ = 0 := by
    rw [riemannZeta_def_of_ne_zero (critical_point_ne_zero t), hΛ, zero_div]
  show PositiveOnLineZetaZeroOrdinates.Nonempty
  exact ⟨t, ht, hζ⟩

/-- **★★★★★ THE WITNESS BRIDGE ★★★★★** — a SIGN CHANGE of the explicit
    continuous real function `Xi` on the positive axis discharges the
    single remaining RH bucket-1 atom
    `PositiveOnLineZetaZeroOrdinatesNonempty`, via the intermediate
    value theorem. This is milestone M1 = A1+A2 = B1+B2 of
    HARDY_SCOPING_2026-07-24; both discharge routes feed through this
    single statement. -/
theorem xi_sign_change_implies_on_line_zero :
    (∃ a b : ℝ, 0 < a ∧ a < b ∧ Xi a * Xi b < 0) →
    PositiveOnLineZetaZeroOrdinatesNonempty := by
  rintro ⟨a, b, ha, hab, hsign⟩
  have hcont : ContinuousOn Xi (Set.uIcc a b) := continuous_Xi.continuousOn
  have h0 : (0 : ℝ) ∈ Set.uIcc (Xi a) (Xi b) := by
    rcases mul_neg_iff.mp hsign with ⟨hpa, hnb⟩ | ⟨hna, hpb⟩
    · exact Set.mem_uIcc.mpr (Or.inr ⟨hnb.le, hpa.le⟩)
    · exact Set.mem_uIcc.mpr (Or.inl ⟨hna.le, hpb.le⟩)
  obtain ⟨t, htmem, htzero⟩ := intermediate_value_uIcc hcont h0
  have hta : a ≤ t := by
    rw [Set.uIcc_of_le hab.le] at htmem
    exact htmem.1
  exact xi_zero_at_pos_implies_nonempty (lt_of_lt_of_le ha hta) htzero

end PrincipiaTractalis.XiRealWitness

-- Axiom check. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.XiRealWitness.Gammaℝ_conj
#print axioms PrincipiaTractalis.XiRealWitness.completedRiemannZeta₀_conj
#print axioms PrincipiaTractalis.XiRealWitness.completedRiemannZeta_conj
#print axioms PrincipiaTractalis.XiRealWitness.riemannZeta_conj
#print axioms PrincipiaTractalis.XiRealWitness.Xi_im_eq_zero
#print axioms PrincipiaTractalis.XiRealWitness.Xi_eq
#print axioms PrincipiaTractalis.XiRealWitness.continuous_Xi
#print axioms PrincipiaTractalis.XiRealWitness.xi_zero_at_pos_implies_nonempty
#print axioms PrincipiaTractalis.XiRealWitness.xi_sign_change_implies_on_line_zero
