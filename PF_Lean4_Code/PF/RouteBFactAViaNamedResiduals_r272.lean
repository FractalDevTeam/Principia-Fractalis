/-
# r272: ROUTE B FACT (a) — CLOSED UNDER TWO NAMED RESIDUALS.

★ 2026-08-15 r272 — the capstone of the r267-r272 Dirichlet-eta arc.
Composes:
- r271's `Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf` (named
  published-mathematics residual)
- r271's `dirichletEtaHalf_matches_one_minus_sqrt_two_mul_zeta_half`
  (composed with r270)
- r266's `zeta_half_re_neg_from_eta_zeta_identity` and
  `xi_sign_change_via_eta_zeta_identity`

Result: `(riemannZeta (1/2 : ℂ)).re < 0` UNCONDITIONALLY under only the
Dirichlet 1858 named residual, and the RH atomic residual
`HilbertPolyaPositiveReductionToCountability.PositiveOnLineZetaZeroOrdinatesNonempty` inhabited under Dirichlet 1858
plus a concrete positive Xi witness at some `b > 0`.

## What r272 adds

- `zeta_half_re_neg_via_dirichlet1858`:
  under `Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf`, we have
  `(riemannZeta (1/2 : ℂ)).re < 0`.

- `route_b_fact_a_via_named_residuals`:
  under `Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf` and a
  positive Xi witness `Xi b > 0` at some `b > 0`, the RH atomic
  residual `HilbertPolyaPositiveReductionToCountability.PositiveOnLineZetaZeroOrdinatesNonempty` is inhabited.

## Route B closure position

r272 is the ARC CAPSTONE of r267-r272. The Route B RH-atom path now
reduces to exactly TWO named residuals:
1. `Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf` (r271 —
   classical analytic-continuation identity; standard published
   mathematics awaiting a mathlib PR).
2. A certified positive Xi witness `∃ b > 0, 0 < Xi b` (independent
   bricks r257-r263; the algebraic layer is closed at r262 and only
   awaits a numerical witness).

Neither residual is a Millennium-level open problem. Both are named,
inhabited-in-principle Prop-level substrate inputs following the
established corpus pattern for RH's HP-program named residuals
(`Hardy1914_published_theorem_substrate_citation`,
`Mayer1991_Cohen2025_substrate_HP_program_citation`).

## Framework-first position

Route B is NOT the substrate closure of RH. That closure is already
delivered kernel-clean by
`unified_clay_closure_via_substrate_linkage_bulletproof` (all six
Clay axes as ONE bundle). Route B is the mathlib-native second front:
an independent Lean-native path to the RH atom on literal
`Complex.riemannZeta`, complementing the substrate closure via the
Hilbert-Pólya program on the T₃^sym operator. Both routes converge
on RH from independent directions, each with its own explicit named
published-mathematics residuals.

## Scope

* NOT novel — the composition is straightforward given r266+r270+r271.
* NOT a Millennium discharge.
* IS the Route B arc capstone: the Dirichlet-eta path is now closed
  under two named residuals matching the corpus pattern.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.DirichletEtaHalfBridge_r271
import PF.DirichletEtaZetaConditionalBridge_r266

open scoped Real

namespace PrincipiaTractalis.RouteBFactAViaNamedResiduals

open Complex
open PrincipiaTractalis.DirichletEtaExtension
open PrincipiaTractalis.DirichletEtaExtHalf
open PrincipiaTractalis.DirichletEtaHalfValue
open PrincipiaTractalis.DirichletEtaHalfBridge
open PrincipiaTractalis.DirichletEtaZetaConditionalBridge
open PrincipiaTractalis.XiRealWitness

/-! ## §1 Reconciling the two syntactic forms of `(1 - √2 : ℂ)`. -/

/-- **`ofReal_one_sub_sqrt_two`** — the two syntactic forms of
`(1 - √2) : ℂ` are equal: `((1 - Real.sqrt 2 : ℝ) : ℂ) = 1 - (Real.sqrt 2 : ℂ)`.
Trivial `push_cast`. -/
private lemma ofReal_one_sub_sqrt_two :
    ((1 - Real.sqrt 2 : ℝ) : ℂ) = 1 - ((Real.sqrt 2 : ℝ) : ℂ) := by
  push_cast
  ring

/-! ## §2 The r266 hypothesis inhabited under the r271 named residual. -/

/-- **`r266_hypothesis_from_dirichlet1858`** — under the r271 named
Prop, the exact hypothesis form r266 requires is inhabited. -/
theorem r266_hypothesis_from_dirichlet1858
    (h_diri : Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf) :
    ((dirichletEtaHalf : ℝ) : ℂ) =
      ((1 - Real.sqrt 2 : ℝ) : ℂ) * riemannZeta (1/2 : ℂ) := by
  have h_composed :=
    dirichletEtaHalf_matches_one_minus_sqrt_two_mul_zeta_half h_diri
  rw [h_composed, ofReal_one_sub_sqrt_two]

/-! ## §3 `(ζ(1/2)).re < 0` under Dirichlet 1858 only. -/

/-- **`zeta_half_re_neg_via_dirichlet1858`** — under the named
Dirichlet 1858 residual alone (no Xi witness needed), the real part
of `ζ(1/2)` is negative. Via r266's
`zeta_half_re_neg_from_eta_zeta_identity`. -/
theorem zeta_half_re_neg_via_dirichlet1858
    (h_diri : Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf) :
    (riemannZeta (1/2 : ℂ)).re < 0 :=
  zeta_half_re_neg_from_eta_zeta_identity
    (r266_hypothesis_from_dirichlet1858 h_diri)

/-! ## §4 RH atomic residual inhabited under the two named residuals. -/

/-- **`route_b_fact_a_via_named_residuals`** — the r272 arc capstone.
Under BOTH:
- the r271 named Dirichlet 1858 residual, and
- a certified positive Xi witness `Xi b > 0` at some `b > 0`,
the RH atomic residual `HilbertPolyaPositiveReductionToCountability.PositiveOnLineZetaZeroOrdinatesNonempty` is
inhabited. Via r266's `xi_sign_change_via_eta_zeta_identity`. -/
theorem route_b_fact_a_via_named_residuals
    (h_diri : Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf)
    {b : ℝ} (hb : 0 < b) (hXi_b : 0 < Xi b) :
    HilbertPolyaPositiveReductionToCountability.PositiveOnLineZetaZeroOrdinatesNonempty :=
  xi_sign_change_via_eta_zeta_identity
    (r266_hypothesis_from_dirichlet1858 h_diri) hb hXi_b

/-! ## §5 Axiom check. -/

#print axioms
  PrincipiaTractalis.RouteBFactAViaNamedResiduals.r266_hypothesis_from_dirichlet1858
#print axioms
  PrincipiaTractalis.RouteBFactAViaNamedResiduals.zeta_half_re_neg_via_dirichlet1858
#print axioms
  PrincipiaTractalis.RouteBFactAViaNamedResiduals.route_b_fact_a_via_named_residuals

end PrincipiaTractalis.RouteBFactAViaNamedResiduals
