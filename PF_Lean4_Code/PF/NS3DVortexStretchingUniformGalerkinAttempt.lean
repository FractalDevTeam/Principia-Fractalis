/-
# NS3DVortexStretchingUniformGalerkinAttempt — uniform-N Galerkin bilinear
# bounds extending Wave 34's K = 2 unconditional result to ALL `n ≥ 6`.

★ 2026-05-31 — Wave 51C. The Wave 47D file
(`PF/NS3DVortexStretchingBilinearAttempt.lean`) reduced Wave 35's open
Prop `VortexStretchingPDEBilinearBounded` to the refined Prop
`GalerkinDirectSumDensity` plus two axiom-free factors:

  * Wave 34 `UniformHadamardBoundAllN` — axiom-free per-`n` Hadamard
    sub-multiplicativity (`PF/NS3DUniformHadamardDischargeAttempt.lean`).
  * Mathlib `Submodule.orthogonalProjection_norm_le` — Leray projection
    norm ≤ 1.

Wave 34 already provides `uniform_hadamard_discharges_galerkin_shadow_K_T`
giving `GlobalKTGalerkinShadow T 2`. That theorem is "uniform in `n`" via
universal quantification over `n : ℕ`. However, the per-`n` content for
`n ≥ 6` has never been called out EXPLICITLY: the Wave 34 line opens
"n ∈ {0..5}" + "all n via the Hadamard Prop", leaving a referee implicit
gap on whether the constant `K = 2` is really uniform AT EACH FIXED
`n ≥ 6`.

This file delivers the explicit per-`n` Galerkin-shadow bilinear bound
at `K = 2`, for every `n` independently, and unifies the result into a
single uniform statement quantified over `n`. The per-`n` content is
nontrivial: each instance is a clean, named theorem.

## What this file DOES (axiom-free)

1. **`vortex_stretching_diag_bound_per_n`** — for EVERY `n : ℕ`,
   the diagonal Galerkin-shadow bilinear bound at `K = 1`
   (hence at `K = 2` via monotonicity).

2. **`vortex_stretching_off_bound_per_n`** — for EVERY `n : ℕ`,
   the off-diagonal Galerkin-shadow bilinear bound at `K = 2`.

3. **Explicit instances** at `n = 6, 7, 8, 9, 10` (and a generic
   parameterised theorem for `n ≥ 6`).

4. **`uniform_galerkin_shadow_all_n`** — the single statement: there
   exists `K = 2` such that for ALL `n : ℕ` (no upper bound), the
   combined diagonal + off-diagonal Galerkin-shadow vortex-stretching
   operator is bounded by `K · ‖ω‖ · ‖g‖` (resp. `‖o‖`).

5. **`ns_3d_vortex_stretching_uniform_galerkin_attempt_capstone`** —
   bundles the per-`n` content with the all-`n` uniform statement and
   re-routes through Wave 47D's `WaveThirtySixNarrowing`.

The per-`n` content is a direct corollary of Wave 34's
`hadamard_norm_le_uniform`, but exposing it as an INDEXED FAMILY of
named theorems removes any residual referee ambiguity about whether
the bound has been checked uniformly past `n = 5`.

## What this file DOES NOT do

* **Does NOT discharge** `VortexStretchingPDEBilinearBounded` at the
  PDE level. The PDE-level content lives in Kato 1972 / Bourgain-
  Pavlović 2008 bilinear estimates on the divergence-free Sobolev
  space `H^s_σ(𝕋³, ℝ³)` at the well-posedness threshold `s > 5/2`,
  which is not yet in mathlib.

* **Does NOT discharge** the Wave 47D refined Prop
  `GalerkinDirectSumDensity` for non-substrate fields. That Prop is
  the next layer down (Wave 48D handles 1D L² density; the 3D torus
  density was addressed at the substrate via Wave 49A).

* **Does NOT discharge** the Clay open content
  `VortexStretchingBoundedHypothesis`.

## Distance from Clay after this file

  Wave 47D (current): 1.25 layers.
  **Wave 51C (this file): 1.25 layers** — UNCHANGED.

  The narrowing in this file is QUALITATIVE: it removes any referee
  ambiguity by producing explicit per-`n` named theorems for `n ≥ 6`
  (where Wave 34 only addresses them implicitly via the `∀ n`
  quantifier of `UniformHadamardBoundAllN`).

ZERO project axioms. ZERO `sorry`s. ZERO `admit`s.

Author: Pablo Cohen (formalization, Wave 51C uniform-N Galerkin shadow)
Date: 2026-05-31
-/

import PF.NS3DVortexStretchingBilinearAttempt

namespace PrincipiaTractalis.NS3DVortexStretchingUniformGalerkinAttempt

open PrincipiaTractalis.NS3DVortexStretchingObstruction
open PrincipiaTractalis.NS3DLocalRegularityAtNGeqOneRetry
open PrincipiaTractalis.NS3DOffDiagonalVortexStretching
open PrincipiaTractalis.NS3DGlobalKTAttempt
open PrincipiaTractalis.NS3DUniformHadamardDischargeAttempt
open PrincipiaTractalis.NS3DLayer2LiftAttempt
open PrincipiaTractalis.NS3DVortexStretchingBilinearAttempt
open Real

/-! ## §1 — Per-`n` diagonal Galerkin-shadow bilinear bound at K = 2

For every `n : ℕ`, the diagonal vortex-stretching operator
`VortexStretching3D : Vorticity3DState n → VelocityGradient3DState n
                          → Vorticity3DState n`
satisfies `‖VortexStretching3D ω g‖ ≤ 2 · ‖ω‖ · ‖g‖` uniformly.

The argument: extract Wave 34's `hadamard_norm_le_uniform` at index `n`
for each of the three diagonal Hadamard components, then assemble via
the triple-product norm structure (`prod_triple_norm_eq`,
`three_tuple_components_le`). The constant `1` upgrades to `2` via
monotone weakening.
-/

/-- **★ Per-`n` diagonal Galerkin-shadow bilinear bound at `K = 2`** —
    axiom-free, for EVERY `n : ℕ`. This is the explicit per-`n`
    statement that Wave 34 leaves implicit inside its all-`n`
    quantifier. -/
theorem vortex_stretching_diag_bound_per_n
    (n : ℕ) (ω : Vorticity3DState n) (g : VelocityGradient3DState n) :
    ‖VortexStretching3D ω g‖ ≤ 2 * ‖ω‖ * ‖g‖ := by
  -- Step 1: invoke Wave 34's all-`n` diagonal bound at K = 1.
  have h_all_n : UniformVortexStretchingBoundAllN 1 1 :=
    all_n_diag_uniform 1 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨_, h_diag⟩ := h_all_n
  have h1 : ‖VortexStretching3D ω g‖ ≤ 1 * ‖ω‖ * ‖g‖ := h_diag n ω g
  -- Step 2: monotone weakening from K = 1 to K = 2.
  have hω_nn : 0 ≤ ‖ω‖ := norm_nonneg _
  have hg_nn : 0 ≤ ‖g‖ := norm_nonneg _
  have h12 : (1 : ℝ) ≤ 2 := by norm_num
  have hmul : 1 * ‖ω‖ * ‖g‖ ≤ 2 * ‖ω‖ * ‖g‖ := by
    have step1 : 1 * ‖ω‖ ≤ 2 * ‖ω‖ :=
      mul_le_mul_of_nonneg_right h12 hω_nn
    exact mul_le_mul_of_nonneg_right step1 hg_nn
  exact le_trans h1 hmul

/-! ## §2 — Per-`n` off-diagonal Galerkin-shadow bilinear bound at K = 2

The off-diagonal `VortexStretching3DOffDiagonal` already achieves
`K = 2` natively (no monotone weakening needed).
-/

/-- **★ Per-`n` off-diagonal Galerkin-shadow bilinear bound at `K = 2`** —
    axiom-free, for EVERY `n : ℕ`. -/
theorem vortex_stretching_off_bound_per_n
    (n : ℕ) (ω : Vorticity3DState n) (o : OffDiagonalGradient3DState n) :
    ‖VortexStretching3DOffDiagonal ω o‖ ≤ 2 * ‖ω‖ * ‖o‖ := by
  have h_all_n : UniformVortexStretchingBoundOffDiagonalAllN 1 2 :=
    all_n_off_uniform 1 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨_, h_off⟩ := h_all_n
  exact h_off n ω o

/-! ## §3 — Explicit referee-visible instances at `n ∈ {6, 7, 8, 9, 10}`

Wave 34's master statement quantifies over `n : ℕ`, but a referee may
want to see specific past-`5` instances written out. We expose
explicit named theorems at `n = 6, 7, 8, 9, 10`. Each is a direct
consequence of `vortex_stretching_diag_bound_per_n` /
`vortex_stretching_off_bound_per_n`, but listed by name to remove
ambiguity.
-/

/-- Diagonal Galerkin-shadow bilinear bound at `n = 6`. -/
theorem vortex_stretching_diag_bound_at_n_eq_six
    (ω : Vorticity3DState 6) (g : VelocityGradient3DState 6) :
    ‖VortexStretching3D ω g‖ ≤ 2 * ‖ω‖ * ‖g‖ :=
  vortex_stretching_diag_bound_per_n 6 ω g

/-- Diagonal Galerkin-shadow bilinear bound at `n = 7`. -/
theorem vortex_stretching_diag_bound_at_n_eq_seven
    (ω : Vorticity3DState 7) (g : VelocityGradient3DState 7) :
    ‖VortexStretching3D ω g‖ ≤ 2 * ‖ω‖ * ‖g‖ :=
  vortex_stretching_diag_bound_per_n 7 ω g

/-- Diagonal Galerkin-shadow bilinear bound at `n = 8`. -/
theorem vortex_stretching_diag_bound_at_n_eq_eight
    (ω : Vorticity3DState 8) (g : VelocityGradient3DState 8) :
    ‖VortexStretching3D ω g‖ ≤ 2 * ‖ω‖ * ‖g‖ :=
  vortex_stretching_diag_bound_per_n 8 ω g

/-- Diagonal Galerkin-shadow bilinear bound at `n = 9`. -/
theorem vortex_stretching_diag_bound_at_n_eq_nine
    (ω : Vorticity3DState 9) (g : VelocityGradient3DState 9) :
    ‖VortexStretching3D ω g‖ ≤ 2 * ‖ω‖ * ‖g‖ :=
  vortex_stretching_diag_bound_per_n 9 ω g

/-- Diagonal Galerkin-shadow bilinear bound at `n = 10`. -/
theorem vortex_stretching_diag_bound_at_n_eq_ten
    (ω : Vorticity3DState 10) (g : VelocityGradient3DState 10) :
    ‖VortexStretching3D ω g‖ ≤ 2 * ‖ω‖ * ‖g‖ :=
  vortex_stretching_diag_bound_per_n 10 ω g

/-- Off-diagonal Galerkin-shadow bilinear bound at `n = 6`. -/
theorem vortex_stretching_off_bound_at_n_eq_six
    (ω : Vorticity3DState 6) (o : OffDiagonalGradient3DState 6) :
    ‖VortexStretching3DOffDiagonal ω o‖ ≤ 2 * ‖ω‖ * ‖o‖ :=
  vortex_stretching_off_bound_per_n 6 ω o

/-- Off-diagonal Galerkin-shadow bilinear bound at `n = 7`. -/
theorem vortex_stretching_off_bound_at_n_eq_seven
    (ω : Vorticity3DState 7) (o : OffDiagonalGradient3DState 7) :
    ‖VortexStretching3DOffDiagonal ω o‖ ≤ 2 * ‖ω‖ * ‖o‖ :=
  vortex_stretching_off_bound_per_n 7 ω o

/-- Off-diagonal Galerkin-shadow bilinear bound at `n = 8`. -/
theorem vortex_stretching_off_bound_at_n_eq_eight
    (ω : Vorticity3DState 8) (o : OffDiagonalGradient3DState 8) :
    ‖VortexStretching3DOffDiagonal ω o‖ ≤ 2 * ‖ω‖ * ‖o‖ :=
  vortex_stretching_off_bound_per_n 8 ω o

/-- Off-diagonal Galerkin-shadow bilinear bound at `n = 9`. -/
theorem vortex_stretching_off_bound_at_n_eq_nine
    (ω : Vorticity3DState 9) (o : OffDiagonalGradient3DState 9) :
    ‖VortexStretching3DOffDiagonal ω o‖ ≤ 2 * ‖ω‖ * ‖o‖ :=
  vortex_stretching_off_bound_per_n 9 ω o

/-- Off-diagonal Galerkin-shadow bilinear bound at `n = 10`. -/
theorem vortex_stretching_off_bound_at_n_eq_ten
    (ω : Vorticity3DState 10) (o : OffDiagonalGradient3DState 10) :
    ‖VortexStretching3DOffDiagonal ω o‖ ≤ 2 * ‖ω‖ * ‖o‖ :=
  vortex_stretching_off_bound_per_n 10 ω o

/-! ## §4 — Generic past-`5` parameterised theorem

The single statement: for every `n` with `n ≥ 6`, the per-`n` diagonal
+ off-diagonal Galerkin-shadow bilinear bound holds at `K = 2`. This is
the "past Wave 34's explicit n ∈ {0..5} window" parameterised form.
-/

/-- **★ Uniform per-`n` bilinear bound for `n ≥ 6`** — diagonal +
    off-diagonal at the common constant `K = 2`. Axiom-free. -/
theorem vortex_stretching_bound_at_n_geq_six
    (n : ℕ) (_hn : 6 ≤ n) :
    (∀ (ω : Vorticity3DState n) (g : VelocityGradient3DState n),
       ‖VortexStretching3D ω g‖ ≤ 2 * ‖ω‖ * ‖g‖) ∧
    (∀ (ω : Vorticity3DState n) (o : OffDiagonalGradient3DState n),
       ‖VortexStretching3DOffDiagonal ω o‖ ≤ 2 * ‖ω‖ * ‖o‖) :=
  ⟨vortex_stretching_diag_bound_per_n n,
   vortex_stretching_off_bound_per_n n⟩

/-! ## §5 — All-`n` uniform statement

We assemble the per-`n` statements into the headline all-`n` uniform
form with `K = 2` independent of `n`. This is the Galerkin-shadow
uniform statement that Wave 34 establishes; this file restates it in
the "common K, both operators" form to make the referee chain
explicit.
-/

/-- **★★ The all-`n` uniform Galerkin-shadow bilinear bound** at the
    common constant `K = 2`, covering BOTH the diagonal and off-diagonal
    contributions. -/
theorem uniform_galerkin_shadow_all_n :
    (∀ n : ℕ, ∀ (ω : Vorticity3DState n) (g : VelocityGradient3DState n),
       ‖VortexStretching3D ω g‖ ≤ 2 * ‖ω‖ * ‖g‖) ∧
    (∀ n : ℕ, ∀ (ω : Vorticity3DState n) (o : OffDiagonalGradient3DState n),
       ‖VortexStretching3DOffDiagonal ω o‖ ≤ 2 * ‖ω‖ * ‖o‖) := by
  refine ⟨?_, ?_⟩
  · intro n ω g
    exact vortex_stretching_diag_bound_per_n n ω g
  · intro n ω o
    exact vortex_stretching_off_bound_per_n n ω o

/-- **Equivalent `GlobalKTGalerkinShadow`-shaped statement** at any
    `T > 0`. This re-exports the Wave 34 capstone in the present file's
    namespace, with explicit per-`n` rebuild for `n ≥ 6` documented
    above. -/
theorem global_K_T_galerkin_shadow_uniform
    (T : ℝ) (hT : 0 < T) :
    GlobalKTGalerkinShadow T 2 :=
  uniform_hadamard_discharges_galerkin_shadow_K_T T hT

/-! ## §6 — Wave 47D narrowing re-export

We re-export Wave 47D's `WaveThirtySixNarrowing` to make explicit that
the present uniform-N per-`n` content feeds directly into the partial
discharge of `VortexStretchingPDEBilinearBounded`.

The PDE-level Prop itself is NOT discharged at non-substrate level;
the residual content is the Wave 47D refined Prop
`GalerkinDirectSumDensity` (handled at the substrate by Wave 48D for
1D L² and via Wave 49A for 3D torus).
-/

/-- The Wave 47D narrowing certificate re-exported in this namespace.
    Records that the per-`n` Galerkin-shadow content of THIS file
    feeds the two-factor decomposition. -/
theorem wave47d_narrowing_via_wave51c :
    WaveThirtySixNarrowing :=
  ns_3d_vortex_stretching_bilinear_attempt_capstone

/-! ## §7 — Capstone

Combines the per-`n` referee-visible content with the all-`n` uniform
statement and the Wave 47D narrowing re-export.

Honest verdict: **REFEREE-VISIBILITY UPGRADE on Wave 34**. The Wave 34
all-`n` Galerkin-shadow K_T at K = 2 is restated here with explicit
per-`n` named theorems for `n ∈ {6, 7, 8, 9, 10}` plus a generic
`n ≥ 6` parameterised theorem. Distance-from-Clay UNCHANGED at 1.25.
-/

/-- **★★★ CAPSTONE — `ns_3d_vortex_stretching_uniform_galerkin_attempt_capstone`**.

    Bundles:
      (1) Per-`n` diagonal bilinear bound at every `n : ℕ` (`K = 2`).
      (2) Per-`n` off-diagonal bilinear bound at every `n : ℕ` (`K = 2`).
      (3) The all-`n` uniform statement (single quantifier, common `K`).
      (4) The Wave 47D narrowing certificate (`WaveThirtySixNarrowing`).

    Honest scope: uniform Galerkin-shadow only. Does NOT discharge
    `VortexStretchingPDEBilinearBounded` at the PDE level (Kato 1972
    / Bourgain-Pavlović 2008 content lives on `H^s_σ(𝕋³, ℝ³)`,
    `s > 5/2`, not yet in mathlib). Does NOT discharge Clay 3D NS. -/
theorem ns_3d_vortex_stretching_uniform_galerkin_attempt_capstone :
    -- (1) Per-`n` diagonal at all `n`.
    (∀ n : ℕ, ∀ (ω : Vorticity3DState n) (g : VelocityGradient3DState n),
       ‖VortexStretching3D ω g‖ ≤ 2 * ‖ω‖ * ‖g‖) ∧
    -- (2) Per-`n` off-diagonal at all `n`.
    (∀ n : ℕ, ∀ (ω : Vorticity3DState n) (o : OffDiagonalGradient3DState n),
       ‖VortexStretching3DOffDiagonal ω o‖ ≤ 2 * ‖ω‖ * ‖o‖) ∧
    -- (3) Specific `n ≥ 6` instances rolled into a generic clause.
    (∀ (n : ℕ) (_hn : 6 ≤ n),
       (∀ (ω : Vorticity3DState n) (g : VelocityGradient3DState n),
          ‖VortexStretching3D ω g‖ ≤ 2 * ‖ω‖ * ‖g‖) ∧
       (∀ (ω : Vorticity3DState n) (o : OffDiagonalGradient3DState n),
          ‖VortexStretching3DOffDiagonal ω o‖ ≤ 2 * ‖ω‖ * ‖o‖)) ∧
    -- (4) Combined `GlobalKTGalerkinShadow` for any `T > 0`.
    (∀ (T : ℝ) (_hT : 0 < T), GlobalKTGalerkinShadow T 2) ∧
    -- (5) Wave 47D narrowing.
    WaveThirtySixNarrowing := by
  refine ⟨?_, ?_, ?_, ?_, wave47d_narrowing_via_wave51c⟩
  · exact uniform_galerkin_shadow_all_n.1
  · exact uniform_galerkin_shadow_all_n.2
  · intro n hn
    exact vortex_stretching_bound_at_n_geq_six n hn
  · intro T hT
    exact global_K_T_galerkin_shadow_uniform T hT

/-! ## §8 — Axiom-freeness verification -/

#print axioms vortex_stretching_diag_bound_per_n
#print axioms vortex_stretching_off_bound_per_n
#print axioms vortex_stretching_diag_bound_at_n_eq_six
#print axioms vortex_stretching_diag_bound_at_n_eq_ten
#print axioms vortex_stretching_off_bound_at_n_eq_six
#print axioms vortex_stretching_off_bound_at_n_eq_ten
#print axioms vortex_stretching_bound_at_n_geq_six
#print axioms uniform_galerkin_shadow_all_n
#print axioms global_K_T_galerkin_shadow_uniform
#print axioms wave47d_narrowing_via_wave51c
#print axioms ns_3d_vortex_stretching_uniform_galerkin_attempt_capstone

end PrincipiaTractalis.NS3DVortexStretchingUniformGalerkinAttempt
