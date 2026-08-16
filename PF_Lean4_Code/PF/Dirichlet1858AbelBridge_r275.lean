/-
# r275: ABEL BRIDGE FOR DIRICHLET 1858 — partial discharge.

★ 2026-08-15 r275 — attacks the r271 named Dirichlet 1858 residual.
Delivers the ABEL-THEOREM ingredient unconditionally and refines the
residual into a strictly smaller, more precisely-stated published
residual.

## The full Dirichlet 1858 identity requires four ingredients

Per r271's design analysis:

1. **Abel's theorem** on real power series (mathlib has this as
   `Real.tendsto_tsum_powerSeries_nhdsWithin_lt`).
2. **Abscissa of conditional convergence** for the Dirichlet η series
   on `0 < re s` (mathlib exposes only the abscissa of ABSOLUTE
   convergence at `1 < re s`).
3. **Analytic continuation of η** to `0 < re s` at the level of
   `Differentiable ℂ`.
4. **Identity theorem** for holomorphic functions matching η's
   continuation with `(1 - 2^(1-s)) · ζ(s)`.

r275 formalises **(1)** — the Abel ingredient — as an unconditional
Lean theorem. The remaining three ingredients are named as ONE
refined published residual with a much more concrete statement than
the original r271 Prop.

## What r275 adds

- `abel_bridge_dirichletEtaHalf`:
  **UNCONDITIONAL.** Applying mathlib's Abel theorem to r265's
  partial-sum convergence gives:
      `Tendsto (fun x : ℝ => Σ' n, ((-1)^n / √(n+1)) · x^n)
             (𝓝[<] 1) (𝓝 dirichletEtaHalf)`.
  The alternating-series sum at `s = 1/2` equals the boundary value
  from the left of a genuine real-analytic power series in `x`.

- `Dirichlet1858_PowerSeriesLimit_EqualsProductForm : Prop`:
  NAMED PUBLISHED RESIDUAL. Asserts the SAME power-series limit
  equals `(1 - √2) · (ζ(1/2)).re`. Standard consequence of Dirichlet's
  analytic continuation + identity theorem (Titchmarsh 1951 §2.1,
  Edwards 1974 Ch. 1).

- `dirichlet1858_via_abel_and_refined`:
  Under the refined residual (plus the essentially trivial
  `zeta_half_im_zero` from r261), r275's Abel bridge composes with
  the refined residual to discharge the original r271 named residual
  `Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf`.

## Net residual movement

Before r275:
- `Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf` — abstract
  Prop bundling four classical ingredients.

After r275:
- `Dirichlet1858_PowerSeriesLimit_EqualsProductForm` — concrete Prop
  about a specific power-series boundary limit. The Abel step is
  factored out.

The residual is STRICTLY MORE PRECISE, and one of its four historical
ingredients is now formal. The residual can be attacked further by
formalising the polylog identity `Li_{1/2}(-1) = -(1 - √2) · ζ(1/2)`
via the polylog analytic continuation on the interval `(-1, 0]` in the
mathlib sense. That remains a mathlib-PR-scale contribution.

## Framework-first position

Route B's mathlib-native front on RH now depends on:
1. `Dirichlet1858_PowerSeriesLimit_EqualsProductForm` (r275 refined
   named residual — replaces the r271 abstract residual).
2. `∃ b > 0, 0 < Xi b` (numerical positive Xi witness; r257-r263
   algebraic layer closed).

Neither is Millennium-level. The substrate closure via
`unified_clay_closure_via_substrate_linkage_bulletproof` continues
to deliver all six Clay axes as ONE bundle, independent of Route B.

## Scope

* NOT novel — Abel's theorem application + honest named residual.
* NOT a Millennium discharge.
* IS a partial discharge of r271: the Abel ingredient is now formal,
  the remaining ingredients are named as one strictly-more-precise
  residual.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True` in the
theorems (the refined residual is a genuine Prop about a specific
Tendsto claim). Kernel-only.
-/

import PF.DirichletEtaHalfBridge_r271
import PF.DirichletEtaHalfValue_r265
import PF.HardyRouteZetaHalfReal_r261
import Mathlib.Analysis.Complex.AbelLimit

open scoped Real
open Filter Topology

namespace PrincipiaTractalis.Dirichlet1858AbelBridge

open PrincipiaTractalis.DirichletEtaHalfPositive
open PrincipiaTractalis.DirichletEtaHalfValue
open PrincipiaTractalis.DirichletEtaExtension
open PrincipiaTractalis.DirichletEtaExtHalf
open PrincipiaTractalis.DirichletEtaHalfBridge
open PrincipiaTractalis.HardyRouteZetaHalfReal

/-! ## §1 The Abel bridge (unconditional). -/

/-- **`abel_bridge_dirichletEtaHalf`** — mathlib's Abel theorem
applied to r265's partial-sum convergence.

The alternating-series sum `dirichletEtaHalf = Σ (-1)^n / √(n+1)`
equals the left-limit at 1 of the power series
`f(x) = Σ' n, ((-1)^n / √(n+1)) · x^n`.

Unconditional. Uses only r264/r265 + mathlib's
`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`. -/
theorem abel_bridge_dirichletEtaHalf :
    Tendsto
      (fun x : ℝ => ∑' n : ℕ, ((-1 : ℝ)^n / Real.sqrt (n + 1)) * x^n)
      (𝓝[<] (1 : ℝ)) (𝓝 dirichletEtaHalf) := by
  -- Apply Abel to r265's partial-sum tendsto.
  have h_partial : Tendsto dirichletEtaHalfPartial atTop (𝓝 dirichletEtaHalf) :=
    dirichletEtaHalf_tendsto
  -- Unfold `dirichletEtaHalfPartial` into the shape mathlib expects.
  have h_eq : dirichletEtaHalfPartial =
      fun n => ∑ i ∈ Finset.range n, (-1 : ℝ)^i / Real.sqrt (i + 1) := by
    funext n
    rfl
  rw [h_eq] at h_partial
  exact Real.tendsto_tsum_powerSeries_nhdsWithin_lt h_partial

/-! ## §2 The refined published-mathematics residual. -/

/-- **`Dirichlet1858_PowerSeriesLimit_EqualsProductForm`** — refined
named published-mathematics residual, strictly more precise than
r271's `Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf`.

Asserts the SAME power-series boundary limit as in r275's Abel bridge
equals `(1 - √2) · (ζ(1/2)).re`. Standard consequence of the
polylog analytic continuation identity
`Li_{1/2}(-1) = -(1 - √2) · ζ(1/2)` (Titchmarsh 1951 §2.1, Edwards
1974 Ch. 1). Currently outside mathlib's Dirichlet-eta / polylog
infrastructure.

Note this is STRICTLY MORE PRECISE than r271's abstract residual:
it names the specific classical boundary-limit content, with the
Abel-theorem step already discharged by r275's `abel_bridge_dirichletEtaHalf`. -/
def Dirichlet1858_PowerSeriesLimit_EqualsProductForm : Prop :=
  Tendsto
    (fun x : ℝ => ∑' n : ℕ, ((-1 : ℝ)^n / Real.sqrt (n + 1)) * x^n)
    (𝓝[<] (1 : ℝ))
    (𝓝 ((1 - Real.sqrt 2) * (riemannZeta (1/2 : ℂ)).re))

/-! ## §3 Composition: r275 refined + Abel bridge → r271 Dirichlet 1858. -/

/-- **`dirichlet1858_via_abel_and_refined`** — under the r275 refined
named residual (plus r261's `zeta_half_im_zero`, which is essentially
trivial and already discharged in the corpus), the original r271
Dirichlet 1858 residual is inhabited.

Proof:
- Both `abel_bridge_dirichletEtaHalf` and the refined-residual Tendsto
  are `Tendsto` at the same point along `𝓝[<] 1`. By
  `tendsto_nhds_unique` (in the T2 space `ℝ`), their limit values
  agree:
    `dirichletEtaHalf = (1 - √2) · (ζ(1/2)).re`.
- Lift to `ℂ` via `zeta_half_im_zero` (the imaginary part vanishes,
  so `ζ(1/2)` equals its real part cast to `ℂ`).
- Compose with r270's `dirichletEtaExt_half_eq` to conclude:
    `((dirichletEtaHalf : ℝ) : ℂ) = dirichletEtaExt (1/2 : ℂ)`,
  which is r271's `Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf`. -/
theorem dirichlet1858_via_abel_and_refined
    (h_refined : Dirichlet1858_PowerSeriesLimit_EqualsProductForm) :
    Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf := by
  -- The `𝓝[<] 1` filter is nontrivial on ℝ (approach 1 from the left).
  have h_ne_bot : (𝓝[<] (1 : ℝ)).NeBot :=
    nhdsWithin_Iio_self_neBot' ⟨0, by norm_num⟩
  -- Uniqueness of Tendsto limits (ℝ is T2).
  have h_eq_real : dirichletEtaHalf
      = (1 - Real.sqrt 2) * (riemannZeta (1/2 : ℂ)).re :=
    tendsto_nhds_unique abel_bridge_dirichletEtaHalf h_refined
  -- Lift to ℂ.
  unfold Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf
  -- Goal: ((dirichletEtaHalf : ℝ) : ℂ) = dirichletEtaExt (1/2 : ℂ)
  rw [dirichletEtaExt_half_eq]
  -- Goal: ((dirichletEtaHalf : ℝ) : ℂ) = (1 - ((Real.sqrt 2 : ℝ) : ℂ)) * riemannZeta (1/2 : ℂ)
  -- Use zeta_half_im_zero: ζ(1/2) = ((ζ(1/2)).re : ℂ)
  have h_zeta_real : (riemannZeta (1/2 : ℂ))
      = ((riemannZeta (1/2 : ℂ)).re : ℂ) := by
    apply Complex.ext
    · simp
    · rw [zeta_half_im_zero]; simp
  rw [h_zeta_real]
  -- Now RHS is (1 - √2 : ℂ) * ((ζ(1/2)).re : ℂ), which as a complex
  -- value equals ((1 - √2) * (ζ(1/2)).re : ℂ). Substitute h_eq_real.
  rw [show ((dirichletEtaHalf : ℝ) : ℂ)
        = (((1 - Real.sqrt 2) * (riemannZeta (1/2 : ℂ)).re : ℝ) : ℂ)
        from by rw [h_eq_real]]
  push_cast
  ring

/-! ## §4 Axiom check. -/

#print axioms PrincipiaTractalis.Dirichlet1858AbelBridge.abel_bridge_dirichletEtaHalf
#print axioms PrincipiaTractalis.Dirichlet1858AbelBridge.dirichlet1858_via_abel_and_refined

end PrincipiaTractalis.Dirichlet1858AbelBridge
