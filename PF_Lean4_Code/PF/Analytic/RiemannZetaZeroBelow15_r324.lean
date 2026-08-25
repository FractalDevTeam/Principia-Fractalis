/-
# r324: LITERAL `Complex.riemannZeta` ZERO STRICTLY BETWEEN HEIGHTS 1 AND 15
        ON THE CRITICAL LINE

★ 2026-08-24 r324 — a tightened localization of r120's on-line ζ-zero
existence using r315 as a sharper right endpoint. ★

## What r324 proves

    ∃ t : ℝ, 1 < t ∧ t < 15 ∧ riemannZeta ⟨1/2, t⟩ = 0.

This is the LITERAL statement about mathlib's `Complex.riemannZeta`.

## Where the inputs come from

- `Xi_one_neg : Xi 1 < 0` — `PF/Analytic/XiOnLineZero.lean:380` (r120).
- `Xi_15_pos : 0 < Xi 15` — `PF/Analytic/XiOnLineZeroT15.lean:338` (r315).
- `continuous_Xi : Continuous Xi` — `PF/Analytic/XiRealWitness.lean:276`.
- `Xi_eq : completedRiemannZeta ⟨1/2, t⟩ = ((Xi t : ℝ) : ℂ)` —
  `PF/Analytic/XiRealWitness.lean:255`.
- `critical_point_ne_zero : (⟨1/2, t⟩ : ℂ) ≠ 0` —
  `PF/Analytic/XiRealWitness.lean:263`.
- Mathlib's `intermediate_value_Ioo` — direct existence-with-strict-bounds
  from IVT.
- Mathlib's `riemannZeta_def_of_ne_zero` — the `ζ = Λ / Gammaℝ` bridge.

## Position in the corpus

r120's endpoint `positiveOnLineZetaZeroOrdinatesNonempty`
(`PF/Analytic/XiOnLineZero.lean:392`) proves `∃ t > 0, riemannZeta ⟨1/2, t⟩ = 0`
via the sign change on `[1, 77/5]` (Xi(1) < 0 < Xi(77/5)) plus IVT plus the
Xi → ζ bridge.  That theorem uses `xi_sign_change_implies_on_line_zero`
which THROWS AWAY the upper bound: only `0 < t` is retained.

r324 uses r315's `Xi_15_pos` as the RIGHT endpoint (in place of r120's
`Xi_154_pos`) AND uses `intermediate_value_Ioo` directly (in place of the
existing bridge lemma) so both interval bounds `1 < t < 15` are preserved.

Result: literal ζ-zero existence in the STRICTLY SMALLER interval `(1, 15)`
than r120's `(0, ∞)`, using only the r315-tightened right endpoint.

## Scope — explicit

* IS: `∃ t : ℝ, 1 < t ∧ t < 15 ∧ riemannZeta ⟨1/2, t⟩ = 0` —
  a rigorous tightening of r120's existence interval using r315's
  right endpoint.
* IS: kernel-verified via IVT + Xi → ζ bridge; uses ONLY certified
  r120 (`Xi_one_neg`), r315 (`Xi_15_pos`), `continuous_Xi`, and
  mathlib's standard IVT / division algebra.
* NOT: uniqueness of the zero.
* NOT: simplicity of the zero.
* NOT: "the first zero" — this is one zero somewhere in `(1, 15)`,
  not necessarily the smallest positive.
* NOT: finite-height RH below 15.
* NOT: an EXACT TOTAL COUNT of nontrivial ζ zeros with `0 < Im s < 15`
  (which is the load-bearing residual for finite-height RH below 15;
  see `codex/RH_FINITE_HEIGHT_FEASIBILITY_2026-08-24.md`).
* NOT: dependent on α-skeleton, r128 StructuralLaws, I9, H_3, or T3.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.Analytic.XiOnLineZero
import PF.Analytic.XiOnLineZeroT15

namespace PrincipiaTractalis.RiemannZetaZeroBelow15

open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.XiOnLineZero
open PrincipiaTractalis.XiOnLineZeroT15

/-! ## §1 — Xi has a zero strictly between t = 1 and t = 15 -/

/-- **`exists_Xi_zero_between_one_and_fifteen`** — IVT on `Xi` between the
r120 endpoint `Xi_one_neg : Xi 1 < 0` and the r315 endpoint
`Xi_15_pos : 0 < Xi 15` gives a zero of `Xi` in the OPEN interval `(1, 15)`.

Proof: `intermediate_value_Ioo` applied to `1 ≤ 15`, `Xi` continuous on
`Icc 1 15`, and `0 ∈ Ioo (Xi 1) (Xi 15)` (which holds because
`Xi 1 < 0 < Xi 15`). -/
theorem exists_Xi_zero_between_one_and_fifteen :
    ∃ t : ℝ, 1 < t ∧ t < 15 ∧ Xi t = 0 := by
  have h1_le_15 : (1 : ℝ) ≤ 15 := by norm_num
  have hcont : ContinuousOn Xi (Set.Icc 1 15) := continuous_Xi.continuousOn
  have h0_mem : (0 : ℝ) ∈ Set.Ioo (Xi 1) (Xi 15) := ⟨Xi_one_neg, Xi_15_pos⟩
  obtain ⟨t, htmem, hXi_t⟩ := intermediate_value_Ioo h1_le_15 hcont h0_mem
  exact ⟨t, htmem.1, htmem.2, hXi_t⟩

/-! ## §2 — Literal `Complex.riemannZeta` zero strictly between 1 and 15 -/

/-- **★★★ r324 — LITERAL `Complex.riemannZeta` ZERO IN `(1, 15)` ★★★**

There exists `t : ℝ` with `1 < t < 15` and `riemannZeta ⟨1/2, t⟩ = 0`.

Proof: `exists_Xi_zero_between_one_and_fifteen` gives `t` with
`1 < t < 15` and `Xi t = 0`.  The Xi → ζ bridge on the critical line
(using `Xi_eq` + `critical_point_ne_zero` + `riemannZeta_def_of_ne_zero`
+ `zero_div`) converts `Xi t = 0` into `riemannZeta ⟨1/2, t⟩ = 0`.

Companion / position: r120's `positiveOnLineZetaZeroOrdinatesNonempty`
gives `∃ t > 0, riemannZeta ⟨1/2, t⟩ = 0` (existence with only `0 < t`;
upper bound thrown away by the existing bridge lemma).  r324 tightens
the localization to `1 < t < 15` using the r315-sharpened right endpoint
and a direct `intermediate_value_Ioo` application. -/
theorem exists_critical_line_riemannZeta_zero_between_one_and_fifteen :
    ∃ t : ℝ, 1 < t ∧ t < 15 ∧ riemannZeta ⟨1/2, t⟩ = 0 := by
  obtain ⟨t, h1, h15, hXi_t⟩ := exists_Xi_zero_between_one_and_fifteen
  have hΛ : completedRiemannZeta ⟨1/2, t⟩ = 0 := by
    rw [Xi_eq t, hXi_t, Complex.ofReal_zero]
  have hζ : riemannZeta ⟨1/2, t⟩ = 0 := by
    rw [riemannZeta_def_of_ne_zero (critical_point_ne_zero t), hΛ, zero_div]
  exact ⟨t, h1, h15, hζ⟩

end PrincipiaTractalis.RiemannZetaZeroBelow15

/-! ## §3 — Axiom check -/

#print axioms
  PrincipiaTractalis.RiemannZetaZeroBelow15.exists_Xi_zero_between_one_and_fifteen
#print axioms
  PrincipiaTractalis.RiemannZetaZeroBelow15.exists_critical_line_riemannZeta_zero_between_one_and_fifteen
