/-
# r278: `Differentiable ℂ` ANALYTIC CONTINUATION OF η (ingredient (3)
# of the r271 four-ingredient Dirichlet 1858 residual).

★ 2026-08-16 r278 — attacks ingredient (3) of the r275 four-ingredient
design for the r271 Dirichlet 1858 residual: `Differentiable ℂ`
analytic continuation of η to `0 < Re s`.

Since r269 already delivered a total complex extension `dirichletEtaExt`
via the classical identity `η(s) = (1 - 2^(1-s)) · ζ(s)`, ingredient (3)
reduces to proving differentiability of `dirichletEtaExt`.

## Attack surface

`dirichletEtaExt s := (1 - (2 : ℂ)^(1 - s)) · riemannZeta s`.

- `(2 : ℂ)^(1 - s)` is `Complex.cpow` with fixed nonzero base `2`,
  differentiable everywhere via `differentiable_const_cpow_of_neZero`
  (`Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean:159`).
- `1 - (2 : ℂ)^(1 - s)` differentiable everywhere by subtraction from
  a constant.
- `riemannZeta s` is differentiable at every `s ≠ 1` via mathlib's
  `differentiableAt_riemannZeta`
  (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:133`); it has a
  simple pole at `s = 1`.
- Product `(1 - 2^(1-s)) · ζ(s)` is thus differentiable at every
  `s ≠ 1`.

At `s = 1`, the factor `(1 - 2^(1-s))` vanishes (since `2^0 = 1`)
and cancels the simple pole of `ζ`, giving a REMOVABLE singularity
with value `η(1) = log 2` (Euler's classical evaluation). Formalising
this removability requires a mathlib-PR-scale argument (bounded-near-
singularity ⇒ removable, or an explicit limit computation). r278
names it as a strictly-smaller REFINED residual and delivers full
differentiability on the punctured domain `{s : ℂ | s ≠ 1}`
unconditionally.

Since the r271 target is at `s = 1/2 ≠ 1`, this suffices for the
downstream identity-theorem application (ingredient (4)) at the
specific point required.

## What r278 adds

Unconditional differentiability at every `s ≠ 1`:

- `dirichletEtaExt_differentiableAt {s : ℂ} (hs : s ≠ 1)`:
  `DifferentiableAt ℂ dirichletEtaExt s`.

- `dirichletEtaExt_differentiableOn_ne_one`:
  `DifferentiableOn ℂ dirichletEtaExt {s : ℂ | s ≠ 1}`.

- `dirichletEtaExt_differentiableOn_pos_re_ne_one`:
  `DifferentiableOn ℂ dirichletEtaExt {s : ℂ | 0 < s.re ∧ s ≠ 1}`.

Refined named residual + composition:

- `DirichletEtaExt_DifferentiableAtOne : Prop`:
  the removable-singularity claim at `s = 1`. Standard Euler
  identity `η(1) = log 2` + removable-singularity theorem
  (Titchmarsh 1951 §2.1; Edwards 1974 Ch. 1).

- `dirichletEtaExt_differentiable_full_via_named`:
  under the named residual, `Differentiable ℂ dirichletEtaExt`
  on all of ℂ.

- `dirichletEtaExt_differentiableOn_pos_re_via_named`:
  under the named residual, `DifferentiableOn ℂ dirichletEtaExt
  {s : ℂ | 0 < s.re}` — the full ingredient (3) as stated in the
  r275 design.

## Net residual movement

Before r278:
- Ingredient (2) of the r271 four-ingredient design UNCONDITIONAL
  (r277).
- Ingredient (3) [Differentiable ℂ continuation] pending.

After r278:
- Ingredient (3) UNCONDITIONAL on `{s : ℂ | s ≠ 1}` (which contains
  the r271-target point `s = 1/2`).
- Full `Differentiable ℂ` on all of ℂ reduces to a strictly-smaller
  named residual `DirichletEtaExt_DifferentiableAtOne`.
- Only ingredient (4) [identity theorem match] remains from the r275
  design (modulo the s=1 removability residual).

## Framework-first position

Route B's mathlib-native RH front still depends on the r275 refined
residual `Dirichlet1858_PowerSeriesLimit_EqualsProductForm` + the
r262 numerical positive Xi witness. r278 does NOT reduce Route B's
residual list; it discharges another of the four historical Dirichlet
1858 ingredients at the classical-analysis layer.

Substrate closure via `unified_clay_closure_via_substrate_linkage_bulletproof`
unchanged; all six Clay axes still ONE bundle.

## Scope

* NOT novel — trivial application of mathlib's differentiability
  infrastructure for `cpow` and `riemannZeta`.
* NOT a Millennium discharge.
* IS the classical `Differentiable ℂ` analytic-continuation statement
  for η at every `s ≠ 1`, plus the named-residual reduction of the
  `s = 1` removability.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.
Kernel-only.
-/

import PF.DirichletEtaExtension_r269
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Complex

namespace PrincipiaTractalis.DirichletEtaExtDifferentiable

open PrincipiaTractalis.DirichletEtaExtension
open PrincipiaTractalis.DirichletEtaComplex

/-! ## §1 Differentiability of the constant-base cpow factor. -/

/-- The map `s ↦ (2 : ℂ)^(1 - s)` is differentiable at every `s : ℂ`. -/
private lemma differentiableAt_two_cpow_one_sub (s : ℂ) :
    DifferentiableAt ℂ (fun t : ℂ => (2 : ℂ)^(1 - t)) s := by
  have h_pow : Differentiable ℂ (fun z : ℂ => (2 : ℂ)^z) :=
    differentiable_const_cpow_of_neZero (2 : ℂ)
  have h_lin : DifferentiableAt ℂ (fun t : ℂ => (1 - t : ℂ)) s :=
    differentiableAt_id.const_sub 1
  exact h_pow.differentiableAt.comp s h_lin

/-- The map `s ↦ 1 - (2 : ℂ)^(1 - s)` is differentiable at every `s : ℂ`. -/
private lemma differentiableAt_one_sub_two_cpow (s : ℂ) :
    DifferentiableAt ℂ (fun t : ℂ => 1 - (2 : ℂ)^(1 - t)) s :=
  (differentiableAt_two_cpow_one_sub s).const_sub 1

/-! ## §2 Differentiability of `dirichletEtaExt` at every `s ≠ 1`. -/

/-- **`dirichletEtaExt_differentiableAt`** — UNCONDITIONAL.
`dirichletEtaExt` is differentiable at every `s : ℂ` with `s ≠ 1`.

Product of `(1 - 2^(1-s))` (entire) and `riemannZeta s`
(differentiable at `s ≠ 1` by `differentiableAt_riemannZeta`). -/
theorem dirichletEtaExt_differentiableAt {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ dirichletEtaExt s := by
  unfold dirichletEtaExt
  have h_factor : DifferentiableAt ℂ (fun t : ℂ => 1 - (2 : ℂ)^(1 - t)) s :=
    differentiableAt_one_sub_two_cpow s
  have h_zeta : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs
  exact h_factor.mul h_zeta

/-- **`dirichletEtaExt_differentiableOn_ne_one`** — UNCONDITIONAL.
`DifferentiableOn ℂ dirichletEtaExt {s : ℂ | s ≠ 1}`. -/
theorem dirichletEtaExt_differentiableOn_ne_one :
    DifferentiableOn ℂ dirichletEtaExt {s : ℂ | s ≠ 1} := by
  intro s hs
  exact (dirichletEtaExt_differentiableAt hs).differentiableWithinAt

/-- **`dirichletEtaExt_differentiableOn_pos_re_ne_one`** — UNCONDITIONAL.
`DifferentiableOn ℂ dirichletEtaExt {s : ℂ | 0 < s.re ∧ s ≠ 1}`. -/
theorem dirichletEtaExt_differentiableOn_pos_re_ne_one :
    DifferentiableOn ℂ dirichletEtaExt {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  intro s hs
  exact (dirichletEtaExt_differentiableAt hs.2).differentiableWithinAt

/-! ## §3 Refined named residual: differentiability at `s = 1`. -/

/-- **`DirichletEtaExt_DifferentiableAtOne`** — REFINED named
published-mathematics residual: `dirichletEtaExt` is differentiable
at `s = 1`.

Classical Euler evaluation `η(1) = ∑_{n=1}^∞ (-1)^(n+1)/n = log 2`
combined with the removable-singularity theorem: the simple zero of
`(1 - 2^(1-s))` at `s = 1` cancels the simple pole of `ζ(s)`, giving
a removable singularity for the product with value `log 2`.

Standard references: Titchmarsh, *The Theory of Functions*, 2nd ed.
1939, §9.11; Edwards, *Riemann's Zeta Function*, 1974, Ch. 1. -/
def DirichletEtaExt_DifferentiableAtOne : Prop :=
  DifferentiableAt ℂ dirichletEtaExt 1

/-- **`dirichletEtaExt_differentiable_full_via_named`** — under the
named refined residual, `dirichletEtaExt` is differentiable on all
of ℂ. -/
theorem dirichletEtaExt_differentiable_full_via_named
    (h_one : DirichletEtaExt_DifferentiableAtOne) :
    Differentiable ℂ dirichletEtaExt := by
  intro s
  by_cases hs : s = 1
  · rw [hs]; exact h_one
  · exact dirichletEtaExt_differentiableAt hs

/-- **`dirichletEtaExt_differentiableOn_pos_re_via_named`** — under
the named refined residual, the FULL ingredient (3) of the r275
design is discharged: `DifferentiableOn ℂ dirichletEtaExt` on the
right half-plane `{s : ℂ | 0 < s.re}` (including `s = 1`). -/
theorem dirichletEtaExt_differentiableOn_pos_re_via_named
    (h_one : DirichletEtaExt_DifferentiableAtOne) :
    DifferentiableOn ℂ dirichletEtaExt {s : ℂ | 0 < s.re} := by
  intro s _
  exact (dirichletEtaExt_differentiable_full_via_named h_one s).differentiableWithinAt

/-! ## §4 Axiom check. -/

#print axioms
  PrincipiaTractalis.DirichletEtaExtDifferentiable.dirichletEtaExt_differentiableAt
#print axioms
  PrincipiaTractalis.DirichletEtaExtDifferentiable.dirichletEtaExt_differentiableOn_ne_one
#print axioms
  PrincipiaTractalis.DirichletEtaExtDifferentiable.dirichletEtaExt_differentiableOn_pos_re_ne_one
#print axioms
  PrincipiaTractalis.DirichletEtaExtDifferentiable.dirichletEtaExt_differentiable_full_via_named
#print axioms
  PrincipiaTractalis.DirichletEtaExtDifferentiable.dirichletEtaExt_differentiableOn_pos_re_via_named

end PrincipiaTractalis.DirichletEtaExtDifferentiable
