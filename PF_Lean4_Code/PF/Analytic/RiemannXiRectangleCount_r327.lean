/-
# r327 (ξ specialization) — RECTANGLE ARGUMENT PRINCIPLE FOR THE CLASSICAL
# ENTIRE RIEMANN ξ

★ 2026-08-25.  Instantiates the generic rectangle argument-principle theorem
  ported in `PF/Analytic/RectangleArgumentPrinciple_r327.lean` to the
  classical entire Riemann ξ of r325 (`riemannXiEntire`).  Uses r325's
  entireness (`differentiable_riemannXiEntire`), r325's off-strip zero
  equivalence (`riemannXiEntire_eq_zero_iff_riemannZeta_eq_zero_in_strip`),
  and r326's symmetries.

## What this file gives

Kernel-clean specializations of the generic rectangle argument principle,
tailored to the entire counting object `riemannXiEntire`:

- **`riemannXiEntire_analyticOnNhd`** — `AnalyticOnNhd ℂ riemannXiEntire s`
  for every `s : Set ℂ`.  Immediate from `differentiable_riemannXiEntire`.

- **`rectangleZeroCount_riemannXiEntire`** — CORE.  Assuming
  `riemannXiEntire` is nonvanishing on the border of a closed rectangle
  `Rectangle z w` with `z.re ≤ w.re, z.im ≤ w.im`, the weighted contour
  integral of `logDeriv riemannXiEntire` around `∂Rectangle z w` equals
  `2πi · Σ_{ρ ∈ Z} analyticOrderNatAt riemannXiEntire ρ`, where `Z` is
  any `Finset ℂ` enumerating the interior zeros.  Wrapper of
  `rectangleIntegral'_mul_logDeriv` at `g := 1`.

- **`rectangleZeroCount_riemannXiEntire_self_contained`** — self-contained
  form producing the finite interior zero set automatically from
  `finite_zeros_rectangle`.  Requires nonvanishing at the SW corner (a
  natural place to witness).

## Scope — explicit

* IS: rigorous conditional zero-count identity for the entire ξ over any
  rectangle in ℂ where ξ is border-nonvanishing.
* IS: exact multiplicity accounting via `analyticOrderNatAt`.
* NOT: a certified nonvanishing condition on any specific rectangle.
* NOT: an evaluation of the resulting contour integer.
* NOT: a proof that any particular finite-height zero count equals 1.
* NOT: a finite-height RH theorem.
* NOT: a Millennium result.
* NOT: dependent on α-skeleton / r128 StructuralLaws / I9 / H_3 / T3.

The conditional-on-boundary-nonvanishing form is Pabs's PART VIII: the
boundary condition is exactly the remaining numerical dependency; the
argument-principle theorem itself is what r327 removes as a corpus gap.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.
Zero project axioms.

SPDX-License-Identifier: Apache-2.0
-/
import PF.Analytic.RectangleArgumentPrinciple_r327
import PF.Analytic.RiemannXiEntire_r325
import PF.Analytic.RiemannXiSymmetries_r326

open Complex Set Topology Filter Asymptotics Real
open Zeta23.Analytic
open PrincipiaTractalis.RiemannXiEntire

noncomputable section

namespace PrincipiaTractalis.RiemannXiRectangleCount

/-! ## §1 — `riemannXiEntire` is analytic on a neighbourhood of every set -/

/-- **`riemannXiEntire_analyticOnNhd`** — since `riemannXiEntire` is entire
(`differentiable_riemannXiEntire`), it is analytic on a neighbourhood of
every point, hence `AnalyticOnNhd ℂ riemannXiEntire s` for every set `s`. -/
theorem riemannXiEntire_analyticOnNhd (s : Set ℂ) :
    AnalyticOnNhd ℂ riemannXiEntire s :=
  fun z _ => differentiable_riemannXiEntire.analyticAt z

/-- The constant `1 : ℂ → ℂ` (weight function) is analytic everywhere. -/
theorem const_one_analyticOnNhd (s : Set ℂ) :
    AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) s :=
  fun z _ => analyticAt_const

/-! ## §2 — Weighted argument principle for `riemannXiEntire`

The generic `rectangleIntegral'_mul_logDeriv` from r327 says: for `f, g`
analytic on a neighbourhood of every point of `Rectangle z w`, `f` nonvanishing
on `∂Rectangle z w`, and `Z` a `Finset ℂ` enumerating the interior zeros of `f`
inside the rectangle,
`(1/2πi)∮_{∂R} g · f'/f = Σ_{ρ ∈ Z} ord_ρ(f) · g(ρ)`.

We specialize to `f := riemannXiEntire` at weight `g := (fun _ => 1)`.
-/

/-- **`rectangleZeroCount_riemannXiEntire`** — the classical entire ξ zero count
with multiplicity in a rectangle, as a contour integer.

Assuming
* the rectangle is well-oriented (`z.re ≤ w.re, z.im ≤ w.im`);
* `riemannXiEntire` is nonvanishing on `∂Rectangle z w` (the boundary);
* `Z : Finset ℂ` enumerates exactly the interior zeros of `riemannXiEntire`
  in `Rectangle z w`;

then the contour integral equals the multiplicity-weighted zero sum:

    (1/2πi) ∮_{∂Rectangle z w} riemannXiEntire' / riemannXiEntire
      = ∑ ρ ∈ Z, (analyticOrderNatAt riemannXiEntire ρ : ℂ).

Proof: direct application of the generic `rectangleIntegral'_mul_logDeriv` with
`f := riemannXiEntire, g := (fun _ => 1)`, noting `1 · x = x` and
`(ord · 1 : ℂ) = ord`. -/
theorem rectangleZeroCount_riemannXiEntire
    {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ RectangleBorder z w, riemannXiEntire s ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ s ∈ Rectangle z w, riemannXiEntire s = 0 ↔ s ∈ Z)
    (hZsub : (Z : Set ℂ) ⊆ Rectangle z w) :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) z w
      = ∑ ρ ∈ Z, (analyticOrderNatAt riemannXiEntire ρ : ℂ) := by
  have hApp := rectangleIntegral'_mul_logDeriv (f := riemannXiEntire)
    (g := fun _ : ℂ => (1 : ℂ)) hre him
    (riemannXiEntire_analyticOnNhd _) (const_one_analyticOnNhd _)
    hborder Z hZ hZsub
  -- rewrite `1 * logDeriv` → `logDeriv` and `ord * 1` → `ord`
  have hI : (fun s => (1 : ℂ) * logDeriv riemannXiEntire s) =
      fun s => logDeriv riemannXiEntire s := by
    funext s; ring
  have hS : (∑ ρ ∈ Z, (analyticOrderNatAt riemannXiEntire ρ : ℂ) * 1)
      = ∑ ρ ∈ Z, (analyticOrderNatAt riemannXiEntire ρ : ℂ) := by
    apply Finset.sum_congr rfl
    intro ρ _
    ring
  rw [hI] at hApp
  rw [hApp, hS]

/-- **`rectangleZeroCount_riemannXiEntire_self_contained`** — as
`rectangleZeroCount_riemannXiEntire`, but the finite zero set is produced
internally from `finite_zeros_rectangle`.  Requires a nonvanishing witness at
the south-west corner `z ∈ RectangleBorder z w`. -/
theorem rectangleZeroCount_riemannXiEntire_self_contained
    {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ RectangleBorder z w, riemannXiEntire s ≠ 0) :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) z w
      = ∑ ρ ∈ (finite_zeros_rectangle (riemannXiEntire_analyticOnNhd _)
              (rectangleBorder_subset_rectangle z w
                (show z ∈ RectangleBorder z w from
                  Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))))
              (hborder z (Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))))).toFinset,
        (analyticOrderNatAt riemannXiEntire ρ : ℂ) := by
  have hApp := rectangleIntegral'_mul_logDeriv' (f := riemannXiEntire)
    (g := fun _ : ℂ => (1 : ℂ)) hre him
    (riemannXiEntire_analyticOnNhd _) (const_one_analyticOnNhd _) hborder
  have hI : (fun s => (1 : ℂ) * logDeriv riemannXiEntire s) =
      fun s => logDeriv riemannXiEntire s := by
    funext s; ring
  have hS : ∀ ρ, (analyticOrderNatAt riemannXiEntire ρ : ℂ) * 1
      = (analyticOrderNatAt riemannXiEntire ρ : ℂ) := fun ρ => by ring
  rw [hI] at hApp
  rw [hApp]
  apply Finset.sum_congr rfl
  intro ρ _
  exact hS ρ

end PrincipiaTractalis.RiemannXiRectangleCount

/-! ## §3 — Axiom checks -/

#print axioms
  PrincipiaTractalis.RiemannXiRectangleCount.riemannXiEntire_analyticOnNhd
#print axioms
  PrincipiaTractalis.RiemannXiRectangleCount.rectangleZeroCount_riemannXiEntire
#print axioms
  PrincipiaTractalis.RiemannXiRectangleCount.rectangleZeroCount_riemannXiEntire_self_contained
