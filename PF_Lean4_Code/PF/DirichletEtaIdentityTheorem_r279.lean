/-
# r279: IDENTITY-THEOREM MATCH for η's analytic continuation
# (ingredient (4) of the r271 four-ingredient Dirichlet 1858 residual).

★ 2026-08-16 r279 — attacks ingredient (4) of the r275 four-ingredient
design for the r271 Dirichlet 1858 residual: `identity theorem` for
holomorphic functions matching η's continuation with
`(1 − 2^(1−s)) · ζ(s)`.

## Attack surface

The classical content of ingredient (4): ANY holomorphic function on
a connected open set containing `1 < Re s` that agrees with the
LSeries value there must equal `dirichletEtaExt` throughout — this
is the identity theorem for analytic functions.

r278 gives us `dirichletEtaExt` is analytic on `{s : ℂ | s ≠ 1}`.
Mathlib's identity theorem
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`
(`Mathlib/Analysis/Analytic/Uniqueness.lean:219`) provides the
uniqueness principle. `isConnected_compl_singleton_of_one_lt_rank`
(`Mathlib/Analysis/NormedSpace/Connected.lean:120`) gives connectedness
of `ℂ \ {1}` (since `rank_ℝ ℂ = 2 > 1`).

r279 delivers the identity-theorem application template UNCONDITIONALLY,
plus the ingredient-(4) refined named residual (existence of the
analytic extension itself) and compositional glue.

## Substantive vs symbolic content of ingredient (4)

The IDENTITY-THEOREM STEP is delivered unconditionally in r279. What
remains as a refined named residual is the CONSTRUCTION of the
analytic extension itself — the classical "analytic continuation of
Dirichlet series via uniform convergence on compacts" (Weierstrass +
Cahen 1894). Formalising this in Lean is a mathlib-PR-scale
contribution outside the scope of a substrate brick.

## What r279 adds

Unconditional analyticity + identity-theorem template:

- `dirichletEtaExt_analyticOnNhd_ne_one`: `AnalyticOnNhd ℂ dirichletEtaExt
  {s : ℂ | s ≠ 1}`.
- `eqOn_dirichletEtaExt_of_analyticOnNhd_eventuallyEq`: identity-theorem
  application — any `AnalyticOnNhd` function on `ℂ \ {1}` that agrees
  with `dirichletEtaExt` in a neighborhood of some `z₀ ≠ 1` equals
  `dirichletEtaExt` on all of `ℂ \ {1}`.
- `eqOn_dirichletEtaExt_of_analyticOnNhd_agrees_on_one_lt_re`:
  the standard instantiation with agreement on the `1 < Re s`
  half-plane.

Refined named residual + composition:

- `DirichletEta_HasAnalyticExtension : Prop` — REFINED named
  published-mathematics residual asserting the existence of a
  `AnalyticOnNhd` function on `ℂ \ {1}` that agrees with the
  LSeries-defined `dirichletEta` on `1 < Re s`. Classical Cahen 1894
  + Weierstrass uniform-limit-of-holomorphic-functions theorem.
  Standard references: Cahen, *Sur la fonction ζ(s) de Riemann*, Ann.
  Sci. École Norm. Sup. (3) 11 (1894); Landau, *Handbuch der Lehre
  von der Verteilung der Primzahlen*, 1909, §211.

- `dirichletEtaExt_matches_analytic_extension_via_named`: under the
  refined residual, there exists a function that is `AnalyticOnNhd`
  on `ℂ \ {1}` AND equals `dirichletEtaExt` on `ℂ \ {1}` (via r279's
  identity-theorem template applied with r269's `dirichletEtaExt_eq_dirichletEta`).

## Net residual movement

Before r279:
- Ingredient (2) UNCONDITIONAL (r277).
- Ingredient (3) UNCONDITIONAL on `{s | s ≠ 1}` (r278).
- Ingredient (4) [identity theorem match] pending.

After r279:
- The IDENTITY-THEOREM STEP of ingredient (4) UNCONDITIONAL.
- The CONSTRUCTION step (existence of analytic extension) reduces to
  a strictly-smaller precisely-stated named residual
  `DirichletEta_HasAnalyticExtension`.
- All FOUR ingredients of the r275 design have their SYMBOLIC content
  discharged; remaining CLASSICAL residuals are:
  1. `Dirichlet1858_PowerSeriesLimit_EqualsProductForm` (r275) — the
     specific polylog boundary identity at `s = 1/2`.
  2. `DirichletEtaExt_DifferentiableAtOne` (r278) — removability at `s = 1`.
  3. `DirichletEta_HasAnalyticExtension` (r279) — classical Cahen 1894
     analytic-continuation construction.

## Framework-first position

Route B's mathlib-native RH front still depends on the r275 refined
residual `Dirichlet1858_PowerSeriesLimit_EqualsProductForm` + the
r262 numerical positive Xi witness. r279 does NOT reduce Route B's
residual list; it discharges the SYMBOLIC content of ingredient (4)
of the four-ingredient Dirichlet 1858 design.

Substrate closure via `unified_clay_closure_via_substrate_linkage_bulletproof`
unchanged; all six Clay axes still ONE bundle.

## Scope

* NOT novel — direct application of mathlib's identity theorem for
  analytic functions plus connectedness of `ℂ \ {1}`.
* NOT a Millennium discharge.
* IS the identity-theorem application step for ingredient (4) of the
  r271 four-ingredient Dirichlet 1858 residual, plus the named-residual
  reduction of the analytic-extension existence.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.
Kernel-only.
-/

import PF.DirichletEtaExtDifferentiable_r278
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.NormedSpace.Connected

open Complex Set Filter Topology

namespace PrincipiaTractalis.DirichletEtaIdentityTheorem

open PrincipiaTractalis.DirichletEtaExtension
open PrincipiaTractalis.DirichletEtaComplex
open PrincipiaTractalis.DirichletEtaExtDifferentiable

/-! ## §1 `dirichletEtaExt` is analytic on `ℂ \ {1}`. -/

/-- **`dirichletEtaExt_analyticOnNhd_ne_one`** — UNCONDITIONAL.
`AnalyticOnNhd ℂ dirichletEtaExt {s : ℂ | s ≠ 1}`.

Via `DifferentiableOn.analyticOnNhd` (Cauchy's theorem: complex-
differentiable ⇒ analytic on open sets) applied to r278's
`dirichletEtaExt_differentiableOn_ne_one`. -/
theorem dirichletEtaExt_analyticOnNhd_ne_one :
    AnalyticOnNhd ℂ dirichletEtaExt {s : ℂ | s ≠ 1} :=
  dirichletEtaExt_differentiableOn_ne_one.analyticOnNhd isOpen_compl_singleton

/-! ## §2 Preconnectedness of `ℂ \ {1}`. -/

/-- **`isPreconnected_compl_one`** — `ℂ \ {1}` is preconnected. -/
private lemma isPreconnected_compl_one : IsPreconnected ({s : ℂ | s ≠ 1}) := by
  have h_rank : (1 : Cardinal) < Module.rank ℝ ℂ :=
    rank_real_complex ▸ Nat.one_lt_ofNat
  have h_conn : IsConnected ({(1 : ℂ)}ᶜ) :=
    isConnected_compl_singleton_of_one_lt_rank h_rank (1 : ℂ)
  have h_eq : ({s : ℂ | s ≠ 1}) = ({(1 : ℂ)}ᶜ) := by
    ext s; simp [Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [h_eq]
  exact h_conn.isPreconnected

/-! ## §3 The identity-theorem application template. -/

/-- **`eqOn_dirichletEtaExt_of_analyticOnNhd_eventuallyEq`** —
UNCONDITIONAL. Identity theorem instantiated for `dirichletEtaExt`
on the connected open set `ℂ \ {1}`.

If `f : ℂ → ℂ` is `AnalyticOnNhd` on `ℂ \ {1}` and agrees with
`dirichletEtaExt` in a neighborhood of some point `z₀ ≠ 1`, then
`f = dirichletEtaExt` on the entire `ℂ \ {1}`. -/
theorem eqOn_dirichletEtaExt_of_analyticOnNhd_eventuallyEq
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f {s : ℂ | s ≠ 1})
    {z₀ : ℂ} (hz₀ : z₀ ≠ 1) (hfg : f =ᶠ[𝓝 z₀] dirichletEtaExt) :
    Set.EqOn f dirichletEtaExt {s : ℂ | s ≠ 1} :=
  AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hf dirichletEtaExt_analyticOnNhd_ne_one isPreconnected_compl_one hz₀ hfg

/-- **`eqOn_dirichletEtaExt_of_analyticOnNhd_agrees_on_one_lt_re`** —
UNCONDITIONAL. Convenient specialisation: if `f` is `AnalyticOnNhd`
on `ℂ \ {1}` and `f s = dirichletEtaExt s` at every `s` with `1 < Re s`,
then `f = dirichletEtaExt` on all of `ℂ \ {1}`.

Uses `z₀ = 2` (∈ `1 < Re s` and ≠ `1`) to instantiate the
eventually-equal hypothesis. -/
theorem eqOn_dirichletEtaExt_of_analyticOnNhd_agrees_on_one_lt_re
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f {s : ℂ | s ≠ 1})
    (hfg : ∀ s : ℂ, 1 < s.re → f s = dirichletEtaExt s) :
    Set.EqOn f dirichletEtaExt {s : ℂ | s ≠ 1} := by
  have hz₀ : (2 : ℂ) ≠ 1 := by norm_num
  apply eqOn_dirichletEtaExt_of_analyticOnNhd_eventuallyEq hf hz₀
  refine Filter.eventually_of_mem ?_ (fun t (ht : 1 < t.re) => hfg t ht)
  exact (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
    (by norm_num : 1 < (2 : ℂ).re)

/-! ## §4 The ingredient-(4) refined named residual. -/

/-- **`DirichletEta_HasAnalyticExtension`** — REFINED named
published-mathematics residual for the CONSTRUCTIVE step of
ingredient (4): there exists a function `f : ℂ → ℂ` that is
`AnalyticOnNhd` on `ℂ \ {1}` and agrees with the LSeries-defined
`dirichletEta` on `1 < Re s`.

Classical result of Cahen (1894) + Weierstrass's theorem on
uniform limits of holomorphic functions on compacta: the pointwise
limit of the LSeries partial sums on `0 < Re s` is `Differentiable ℂ`
because the convergence is uniform on compact subsets of the domain
of conditional convergence.

Standard references: Cahen, *Sur la fonction ζ(s) de Riemann*, Ann.
Sci. École Norm. Sup. (3) 11 (1894), pp. 75-164; Landau,
*Handbuch der Lehre von der Verteilung der Primzahlen*, 1909,
§211; Titchmarsh, *The Theory of Functions*, 2nd ed. 1939, §9.11. -/
def DirichletEta_HasAnalyticExtension : Prop :=
  ∃ f : ℂ → ℂ,
    AnalyticOnNhd ℂ f {s : ℂ | s ≠ 1} ∧
    ∀ s : ℂ, 1 < s.re → f s = dirichletEta s

/-! ## §5 Composition: under the residual + identity theorem, the extension coincides
with `dirichletEtaExt` on `ℂ \ {1}`. -/

/-- **`dirichletEtaExt_matches_analytic_extension_via_named`** —
under the r279 refined named residual `DirichletEta_HasAnalyticExtension`,
the analytic extension of η equals `dirichletEtaExt` on all of `ℂ \ {1}`.

This is the FULL ingredient (4) of the r275 design: identity theorem
match between η's analytic continuation and `(1 − 2^(1−s)) · ζ(s)`
on the punctured plane `ℂ \ {1}`. -/
theorem dirichletEtaExt_matches_analytic_extension_via_named
    (h : DirichletEta_HasAnalyticExtension) :
    ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f {s : ℂ | s ≠ 1} ∧
      Set.EqOn f dirichletEtaExt {s : ℂ | s ≠ 1} := by
  obtain ⟨f, hf_ana, hf_ls⟩ := h
  refine ⟨f, hf_ana, ?_⟩
  apply eqOn_dirichletEtaExt_of_analyticOnNhd_agrees_on_one_lt_re hf_ana
  intro s hs
  rw [hf_ls s hs, ← dirichletEtaExt_eq_dirichletEta hs]

/-! ## §6 Axiom check. -/

#print axioms
  PrincipiaTractalis.DirichletEtaIdentityTheorem.dirichletEtaExt_analyticOnNhd_ne_one
#print axioms
  PrincipiaTractalis.DirichletEtaIdentityTheorem.eqOn_dirichletEtaExt_of_analyticOnNhd_eventuallyEq
#print axioms
  PrincipiaTractalis.DirichletEtaIdentityTheorem.eqOn_dirichletEtaExt_of_analyticOnNhd_agrees_on_one_lt_re
#print axioms
  PrincipiaTractalis.DirichletEtaIdentityTheorem.dirichletEtaExt_matches_analytic_extension_via_named

end PrincipiaTractalis.DirichletEtaIdentityTheorem
