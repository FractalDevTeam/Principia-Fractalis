/-
# r325: CLASSICAL ENTIRE RIEMANN ξ + EXACT ζ-ZERO EQUIVALENCE IN THE
       OPEN CRITICAL STRIP

★ 2026-08-25 r325 — construct the classical entire Riemann ξ from
mathlib's `completedRiemannZeta₀` and prove its zeros in the open
critical strip `0 < Re s < 1` are EXACTLY the zeros of literal
`Complex.riemannZeta`. ★

## Definition

    riemannXiEntire (s : ℂ) := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

where `completedRiemannZeta₀ := completedHurwitzZetaEven₀ 0` is mathlib's
entire function (`differentiable_completedZeta₀`).

## Why this construction rather than `s(s-1) · Λ s / 2`

Mathlib's `completedRiemannZeta` (`Λ`) is totalized at its poles `s = 0`
and `s = 1`, so multiplying its pointwise values by `s(s-1)` does NOT
automatically install the removable-singularity extension. Instead,

    completedRiemannZeta s = completedRiemannZeta₀ s - 1/s - 1/(1-s)
                             (mathlib `completedRiemannZeta_eq`)

so multiplying by `s(s-1)` and cancelling:

    s(s-1) · completedRiemannZeta s = s(s-1) · completedRiemannZeta₀ s
                                     - (s - 1)         [from -s(s-1)/s]
                                     - (-s)             [from -s(s-1)/(1-s)]
                                    = s(s-1) · completedRiemannZeta₀ s + 1.

Dividing by 2:

    riemannXiEntire s := (s(s-1) · completedRiemannZeta₀ s + 1) / 2

is entire globally (as a polynomial-times-entire plus constant, divided
by 2), and agrees with `s(s-1) · Λ s / 2` off the poles.

## Endpoints in this file

- `riemannXiEntire`: the entire object.
- `differentiable_riemannXiEntire`: entireness.
- `riemannXiEntire_eq_completed`: off-pole factorization.
- `riemannXiEntire_eq_zero_iff_completedRiemannZeta_eq_zero`: zero
  equivalence with `Λ` off the poles.
- `riemannXiEntire_eq_zero_iff_riemannZeta_eq_zero_in_strip`: THE
  HEADLINE — zeros of `riemannXiEntire` in the open critical strip
  `0 < Re s < 1` are EXACTLY the zeros of `Complex.riemannZeta`.

## Scope — explicit

* IS: an entire complex function whose zeros in the open critical strip
  are EXACTLY the nontrivial ζ zeros there.
* IS: the correct counting object for an argument-principle-based
  finite-height RH proof (once the argument principle itself is
  available in mathlib — see `codex/RH_BELOW_15_TOTAL_COUNT_RESIDUAL_2026-08-24.md`).
* NOT: an argument-principle apparatus.
* NOT: a zero count.
* NOT: a finite-height RH theorem.
* NOT: a Millennium result.
* NOT: dependent on the α-skeleton, r128 StructuralLaws, I9, H_3, or
  T3 spectrum.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.

Author: Pablo Cohen + Claude Opus 4.7.  2026-08-25.
-/

import PF.Analytic.XiRealWitness

namespace PrincipiaTractalis.RiemannXiEntire

open Complex

/-! ## §1 — the entire object -/

/-- **`riemannXiEntire`** — the classical entire Riemann ξ-function,
constructed from `completedRiemannZeta₀` to avoid the pole issues of
`completedRiemannZeta` at `s = 0, 1`. -/
noncomputable def riemannXiEntire (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- **`differentiable_riemannXiEntire`** — the classical Riemann ξ is
entire (differentiable on all of ℂ), because `completedRiemannZeta₀`
is entire (`differentiable_completedZeta₀`) and multiplication by the
polynomial `s(s-1)` plus a constant plus division by `2` preserves
differentiability. -/
theorem differentiable_riemannXiEntire : Differentiable ℂ riemannXiEntire := by
  unfold riemannXiEntire
  have h_poly : Differentiable ℂ (fun s : ℂ => s * (s - 1)) :=
    differentiable_id.mul (differentiable_id.sub_const 1)
  have h_polyΛ₀ : Differentiable ℂ
      (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s) :=
    h_poly.mul differentiable_completedZeta₀
  have h_num : Differentiable ℂ
      (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) :=
    h_polyΛ₀.add_const 1
  exact h_num.div_const 2

/-! ## §2 — off-pole factorization -/

/-- **`riemannXiEntire_eq_completed`** — the off-pole identity:
for `s ≠ 0` and `s ≠ 1`,

    riemannXiEntire s = s (s - 1) · completedRiemannZeta s / 2.

Proof uses `completedRiemannZeta_eq : Λ = Λ₀ - 1/s - 1/(1-s)` (mathlib);
clearing denominators with `field_simp` and closing with `ring`. -/
theorem riemannXiEntire_eq_completed {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXiEntire s = s * (s - 1) * completedRiemannZeta s / 2 := by
  unfold riemannXiEntire
  rw [completedRiemannZeta_eq s]
  have hs_1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h_1_s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

/-! ## §3 — zero equivalence with the completed zeta off the poles -/

/-- **`riemannXiEntire_eq_zero_iff_completedRiemannZeta_eq_zero`** — off
the poles `s = 0, 1`, the zeros of `riemannXiEntire` are exactly the
zeros of `completedRiemannZeta`.

Direct: after `riemannXiEntire_eq_completed`, the polynomial factor
`s (s - 1)` is nonzero (by hypothesis) and `2 ≠ 0`, so
`riemannXiEntire s = 0 ↔ completedRiemannZeta s = 0`. -/
theorem riemannXiEntire_eq_zero_iff_completedRiemannZeta_eq_zero
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXiEntire s = 0 ↔ completedRiemannZeta s = 0 := by
  rw [riemannXiEntire_eq_completed hs0 hs1, div_eq_zero_iff]
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hs_1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h_poly : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs_1
  constructor
  · rintro (h | h)
    · exact (mul_eq_zero.mp h).elim (fun h' => absurd h' h_poly) id
    · exact absurd h h2
  · intro h
    exact Or.inl (by rw [h]; ring)

/-! ## §4 — HEADLINE: literal `Complex.riemannZeta` zero equivalence in
          the open critical strip -/

/-- **★★★ r325 HEADLINE — LITERAL ζ ZERO EQUIVALENCE IN THE OPEN CRITICAL
STRIP. ★★★**

For `s : ℂ` with `0 < s.re` and `s.re < 1`, the zeros of
`riemannXiEntire` are EXACTLY the zeros of `Complex.riemannZeta`:

    riemannXiEntire s = 0 ↔ riemannZeta s = 0.

Proof: `0 < Re s` gives `s ≠ 0` (and `Gammaℝ s ≠ 0` via
`Gammaℝ_ne_zero_of_re_pos`); `Re s < 1` gives `s ≠ 1`. Then
`§3 riemannXiEntire_eq_zero_iff_completedRiemannZeta_eq_zero` reduces
to `completedRiemannZeta s = 0 ↔ riemannZeta s = 0`, which follows from
`riemannZeta_def_of_ne_zero : ζ s = Λ s / Gammaℝ s` (for `s ≠ 0`) and
`div_eq_zero_iff` with the nonvanishing `Gammaℝ`.

This is the entire object whose zeros are the nontrivial ζ zeros in
the open critical strip. -/
theorem riemannXiEntire_eq_zero_iff_riemannZeta_eq_zero_in_strip
    {s : ℂ} (hre0 : 0 < s.re) (hre1 : s.re < 1) :
    riemannXiEntire s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre0
    exact lt_irrefl 0 hre0
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hre1
    exact lt_irrefl 1 hre1
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre0
  rw [riemannXiEntire_eq_zero_iff_completedRiemannZeta_eq_zero hs0 hs1,
      riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff]
  constructor
  · intro h
    exact Or.inl h
  · rintro (h | h)
    · exact h
    · exact absurd h hGamma

end PrincipiaTractalis.RiemannXiEntire

/-! ## §5 — Axiom check -/

#print axioms PrincipiaTractalis.RiemannXiEntire.differentiable_riemannXiEntire
#print axioms PrincipiaTractalis.RiemannXiEntire.riemannXiEntire_eq_completed
#print axioms
  PrincipiaTractalis.RiemannXiEntire.riemannXiEntire_eq_zero_iff_completedRiemannZeta_eq_zero
#print axioms
  PrincipiaTractalis.RiemannXiEntire.riemannXiEntire_eq_zero_iff_riemannZeta_eq_zero_in_strip
