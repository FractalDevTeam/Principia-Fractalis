/-
# r270: `dirichletEtaExt (1/2) = (1 - √2) · ζ(1/2)`.

★ 2026-08-15 r270 — the algebraic evaluation of the r269 extension at
`s = 1/2`. Uses only:
- `1 - 1/2 = 1/2` in `ℂ`.
- `(2 : ℂ)^(1/2 : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ)` via `Complex.ofReal_cpow`
  and `Real.sqrt_eq_rpow`.

This is the exact expression r266's conditional hypothesis names.

## What r270 adds

- `two_cpow_half_eq_sqrt`:
  `(2 : ℂ) ^ ((1/2) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ)`
  — the algebraic bridge from complex cpow to real sqrt.

- `dirichletEtaExt_half_eq`:
  `dirichletEtaExt (1/2 : ℂ) = (1 - ((Real.sqrt 2 : ℝ) : ℂ)) * riemannZeta (1/2 : ℂ)`
  — the specialization. Matches EXACTLY the RHS of r266's
  `zeta_half_re_neg_from_eta_zeta_identity` hypothesis.

## Route B substrate value

r270 produces the RHS of r266's Prop hypothesis on the nose. To
inhabit r266's conditional in r272, we still need the LHS bridge:
    `((dirichletEtaHalf : ℝ) : ℂ) = dirichletEtaExt (1/2 : ℂ)`
that is, connect r265's alternating-series limit to the r269 extension
value. r271 attacks that direction.

## Scope

* NOT novel — pure cpow arithmetic at s = 1/2.
* NOT a Millennium discharge.
* IS the algebraic evaluation brick.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.DirichletEtaExtension_r269

open scoped Real

namespace PrincipiaTractalis.DirichletEtaExtHalf

open Complex
open PrincipiaTractalis.DirichletEtaExtension

/-! ## §1 Algebraic bridge: `2^(1/2) = √2` in `ℂ`. -/

/-- **`two_cpow_half_eq_sqrt`** — `(2 : ℂ)^((1/2) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ)`.
Proof: rewrite `(2 : ℂ)^((1/2 : ℂ)) = ((2 : ℝ) : ℂ)^(((1/2 : ℝ)) : ℂ)`
via norm-cast, apply `Complex.ofReal_cpow` in reverse to descend to
`((2 : ℝ)^(1/2 : ℝ) : ℝ) : ℂ`, then apply `Real.sqrt_eq_rpow` in
reverse. -/
theorem two_cpow_half_eq_sqrt :
    (2 : ℂ) ^ ((1/2) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h_cast_base : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have h_cast_exp : (((1/2 : ℝ)) : ℂ) = ((1/2) : ℂ) := by norm_num
  have h_ofReal :
      (((2 : ℝ) ^ (1/2 : ℝ) : ℝ) : ℂ) = ((2 : ℝ) : ℂ) ^ (((1/2 : ℝ)) : ℂ) :=
    Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) (1/2 : ℝ)
  have h_sqrt : Real.sqrt 2 = (2 : ℝ) ^ (1/2 : ℝ) := Real.sqrt_eq_rpow 2
  rw [h_sqrt]
  rw [h_ofReal]
  rw [h_cast_base, h_cast_exp]

/-! ## §2 Specialization of `dirichletEtaExt` at s = 1/2. -/

/-- **`dirichletEtaExt_half_eq`** — the r269 extension evaluated at s = 1/2
equals `(1 - √2) · ζ(1/2)`. Matches EXACTLY the RHS of r266's
`zeta_half_re_neg_from_eta_zeta_identity` hypothesis. -/
theorem dirichletEtaExt_half_eq :
    dirichletEtaExt (1/2 : ℂ) =
      (1 - ((Real.sqrt 2 : ℝ) : ℂ)) * riemannZeta (1/2 : ℂ) := by
  rw [dirichletEtaExt_apply]
  have h_arg : (1 : ℂ) - (1/2 : ℂ) = (1/2 : ℂ) := by norm_num
  rw [h_arg]
  rw [two_cpow_half_eq_sqrt]

/-! ## §3 Axiom check. -/

#print axioms PrincipiaTractalis.DirichletEtaExtHalf.two_cpow_half_eq_sqrt
#print axioms PrincipiaTractalis.DirichletEtaExtHalf.dirichletEtaExt_half_eq

end PrincipiaTractalis.DirichletEtaExtHalf
