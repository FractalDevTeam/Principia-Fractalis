import PF.DirichletEtaExtDifferentiable_r278
import PF.DirichletEtaExtension_r269
import PF.DirichletEtaIdentityTheorem_r279
import PF.DirichletEtaZetaIdentity_r268

/-!
# Dirichlet-eta extension: universal-s identity

Closes open-item (4-construction-universal) of the Dirichlet-1858 chain
status checklist (see `PF/DirichletChainStatus_2026_11_16.lean`).

**Theorem.** For every `s : ℂ` with `s ≠ 1`,
    `dirichletEtaExt s = (1 - 2^(1-s)) · riemannZeta s`.

**Composition chain (all ingredients already in the corpus):**
  (a) `(1 - 2^(1-s)) · riemannZeta s` is differentiable on `ℂ \ {1}`
      (zeta via `differentiableAt_riemannZeta`; `2^(1-s)` via
      `Complex.differentiable_const_cpow_of_neZero`; product is
      differentiable where each factor is).
  (b) `dirichletEtaExt s = dirichletEta s` on `1 < s.re`
      (r269 `dirichletEtaExt_eq_dirichletEta`).
  (c) `dirichletEta s = (1 - 2^(1-s)) · riemannZeta s` on `1 < s.re`
      (r268 `dirichletEta_eq_one_sub_two_cpow_mul_riemannZeta`).
  (d) Identity theorem on the connected open `ℂ \ {1}`
      (r279 `eqOn_dirichletEtaExt_of_analyticOnNhd_agrees_on_one_lt_re`).

No new mathematical content. Composition of existing theorems.
Three-axiom bar `[propext, Classical.choice, Quot.sound]`.
-/

namespace PrincipiaTractalis.DirichletEtaExtUniversalIdentity

open Complex
open PrincipiaTractalis.DirichletEtaExtension (dirichletEtaExt dirichletEtaExt_eq_dirichletEta)
open PrincipiaTractalis.DirichletEtaIdentityTheorem
  (eqOn_dirichletEtaExt_of_analyticOnNhd_agrees_on_one_lt_re)
open PrincipiaTractalis.DirichletEtaZetaIdentity
  (dirichletEta_eq_one_sub_two_cpow_mul_riemannZeta)

/-- The product `(1 - 2^(1-s)) · ζ(s)`. -/
noncomputable def oneSubTwoCpow_mul_zeta : ℂ → ℂ :=
  fun s => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/-- `(1 - 2^(1-s))` is entire (differentiable everywhere on ℂ). -/
private lemma one_sub_two_cpow_differentiable :
    Differentiable ℂ (fun s : ℂ => (1 - (2 : ℂ) ^ (1 - s))) := by
  have h2 : NeZero (2 : ℂ) := ⟨by norm_num⟩
  have h_cpow : Differentiable ℂ (fun t : ℂ => (2 : ℂ) ^ t) :=
    differentiable_const_cpow_of_neZero (2 : ℂ)
  have h_arg : Differentiable ℂ (fun s : ℂ => (1 - s)) :=
    (differentiable_const (1 : ℂ)).sub differentiable_id
  exact (differentiable_const (1 : ℂ)).sub (h_cpow.comp h_arg)

/-- `oneSubTwoCpow_mul_zeta` is differentiable at every `s ≠ 1`. -/
private lemma oneSubTwoCpow_mul_zeta_differentiableAt_of_ne_one
    {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ oneSubTwoCpow_mul_zeta s :=
  (one_sub_two_cpow_differentiable.differentiableAt).mul
    (differentiableAt_riemannZeta hs)

/-- `oneSubTwoCpow_mul_zeta` is differentiable on `ℂ \ {1}`. -/
private lemma oneSubTwoCpow_mul_zeta_differentiableOn_ne_one :
    DifferentiableOn ℂ oneSubTwoCpow_mul_zeta {s : ℂ | s ≠ 1} := by
  intro s hs
  exact (oneSubTwoCpow_mul_zeta_differentiableAt_of_ne_one hs).differentiableWithinAt

/-- `oneSubTwoCpow_mul_zeta` is `AnalyticOnNhd` on `ℂ \ {1}`. -/
private lemma oneSubTwoCpow_mul_zeta_analyticOnNhd_ne_one :
    AnalyticOnNhd ℂ oneSubTwoCpow_mul_zeta {s : ℂ | s ≠ 1} :=
  oneSubTwoCpow_mul_zeta_differentiableOn_ne_one.analyticOnNhd
    isOpen_compl_singleton

/-- On the absolute-convergence region `1 < re s`, the product
`(1 - 2^(1-s)) · ζ(s)` equals the extension `dirichletEtaExt s`. -/
private lemma oneSubTwoCpow_mul_zeta_eq_dirichletEtaExt_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    oneSubTwoCpow_mul_zeta s = dirichletEtaExt s := by
  unfold oneSubTwoCpow_mul_zeta
  rw [← dirichletEta_eq_one_sub_two_cpow_mul_riemannZeta hs,
      ← dirichletEtaExt_eq_dirichletEta hs]

/-- **Main theorem.** The universal-s identity for the Dirichlet-eta
extension: for every `s ≠ 1`,
    `dirichletEtaExt s = (1 - 2^(1-s)) · riemannZeta s`.

Discharges open-item (4-construction-universal) of the
Dirichlet-1858 chain status checklist. -/
theorem dirichletEtaExt_eq_one_sub_two_cpow_mul_riemannZeta_universal
    {s : ℂ} (hs : s ≠ 1) :
    dirichletEtaExt s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have heq : Set.EqOn oneSubTwoCpow_mul_zeta dirichletEtaExt {s : ℂ | s ≠ 1} :=
    eqOn_dirichletEtaExt_of_analyticOnNhd_agrees_on_one_lt_re
      oneSubTwoCpow_mul_zeta_analyticOnNhd_ne_one
      oneSubTwoCpow_mul_zeta_eq_dirichletEtaExt_of_one_lt_re
  have := (heq hs).symm
  exact this

/-! ## §Axiom check. -/

#print axioms dirichletEtaExt_eq_one_sub_two_cpow_mul_riemannZeta_universal

end PrincipiaTractalis.DirichletEtaExtUniversalIdentity
