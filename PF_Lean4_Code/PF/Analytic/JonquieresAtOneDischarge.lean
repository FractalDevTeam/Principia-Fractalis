/-
# Jonquières Frequent-Agreement at `s = 1` — Closed-Form Reduction (Mercator)

This file SHARPENS `JonquieresFrequentAgreementAtHalf 1` (the
disc-agreement residual specialized to `s = 1`) by leveraging the
EXACT closed form `polyLog 1 z = -log(1 - z)` on the open unit disc
(proved in `PF/Analytic/Polylog.lean` as `polyLog_one`).

## Why `s = 1` is special

At `s = 1`, every coefficient `(n+1)^1 = (n+1)` reduces the
polylog tsum to the Mercator series for `-log(1 - z)`:

```
polyLog 1 z = Σ' n, z^(n+1) / (n+1) = -log(1 - z)    on ‖z‖ < 1.
```

This is **unconditional** (no named hypotheses) — it is purely
mathlib's `Complex.log` machinery + Taylor expansion.

Therefore, on the open unit disc,
`JonquieresFrequentAgreementAtHalf 1` is EQUIVALENT to:

```
∃ᶠ z in 𝓝[≠] (1/2), -log(1 - z) = jonquieresExpansion 1 z.
```

The polylog side has DISAPPEARED — replaced by an elementary
analytic function. The remaining open content is ENTIRELY on the
Jonquières-expansion side at the explicit value `s = 1`.

## What this file delivers (axiom-free, no `sorry`)

1. **`JonquieresExpansionEqualsLogFrequentlyAtHalf`** — the sharper
   named open Prop at `s = 1`:
   ```
   ∃ᶠ z in 𝓝[≠] (1/2 : ℂ),
       -Complex.log (1 - z) = jonquieresExpansion 1 z.
   ```

2. **`jonquieresFrequentAgreementAtHalf_one_of_log`** — the REDUCTION
   theorem: given the sharper Prop above, derive
   `JonquieresFrequentAgreementAtHalf 1`.

3. **`jonquieresFrequentAgreementAtHalf_one_of_sequence_log`** — a
   sequential constructor.

4. **`neg_log_at_half_eq_log_two`** — the explicit value at `z = 1/2`:
   `-log(1 - 1/2) = log 2`.

5. **`polyLog_one_eq_jonquieresExpansion_at_half_of_value`** —
   pointwise reduction at `z = 1/2`: if the Jonquières expansion
   at `(1, 1/2)` numerically equals `log 2`, the identity holds at
   the single point.

## Architecture

```
JonquieresExpansionEqualsLogFrequentlyAtHalf        (THIS FILE)
       ↓ jonquieresFrequentAgreementAtHalf_one_of_log
JonquieresFrequentAgreementAtHalf 1                  (GermAtHalfDischarge.lean)
       ↓ jonquieresIdentityPointGermAtHalf_of_frequentAgreement
JonquieresIdentityPointGermAtHalf 1                  (JonquieresLocalWitness.lean)
       ↓ jonquieresIdentityLocalWitness_of_germAtHalf
JonquieresIdentityLocalWitness 1                     (JonquieresIdentityDischarge.lean)
       ↓ discAgreementReduced_of_sharper_and_reachability
disc-wide agreement at s = 1.
```

Stage L18 — Frequent agreement at s = 1 via the Mercator closed form.
-/

import PF.Analytic.GermAtHalfDischarge

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## The sharper named Prop at `s = 1` -/

/-- **Frequent agreement of the Mercator closed form `-log(1-z)` with the
    Jonquières expansion at `s = 1`, near `1/2`**.

    This is the SHARPEST open content for the disc-wide identity at
    `s = 1`: the polylog has been replaced (via the unconditional
    closed form `polyLog 1 z = -log(1 - z)` on the open unit disc)
    by the elementary analytic function `-log(1 - z)`. The remaining
    open Prop is purely about the Jonquières expansion. -/
def JonquieresExpansionEqualsLogFrequentlyAtHalf : Prop :=
  ∃ᶠ z in 𝓝[≠] (1/2 : ℂ),
    -Complex.log (1 - z) = jonquieresExpansion 1 z

/-! ## The reduction theorem -/

/-- **Reduction**: from the sharper Prop (no polylog mention), derive
    `JonquieresFrequentAgreementAtHalf 1`.

    Proof: the polylog at `s = 1` equals `-log(1-z)` on the open unit
    disc, which contains a neighborhood of `1/2`. Frequent occurrence
    transfers across the eventual agreement. -/
theorem jonquieresFrequentAgreementAtHalf_one_of_log
    (h : JonquieresExpansionEqualsLogFrequentlyAtHalf) :
    JonquieresFrequentAgreementAtHalf 1 := by
  unfold JonquieresExpansionEqualsLogFrequentlyAtHalf at h
  unfold JonquieresFrequentAgreementAtHalf
  have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (1/2 : ℂ) :=
    (Metric.isOpen_ball).mem_nhds half_mem_ball_one
  have h_unit_nhdNE : Metric.ball (0 : ℂ) 1 ∈ 𝓝[≠] (1/2 : ℂ) :=
    nhdsWithin_le_nhds h_unit_nhd
  have h_eventually_log :
      ∀ᶠ z in 𝓝[≠] (1/2 : ℂ), polyLog 1 z = -Complex.log (1 - z) := by
    filter_upwards [h_unit_nhdNE] with z hz
    have h_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact polyLog_one z h_norm
  exact h.mp (h_eventually_log.mono (fun z hz_eq h_log => by
    rw [hz_eq, ← h_log]))

/-! ## Sequential constructor -/

/-- **Sequential constructor for the sharper Prop**. -/
theorem jonquieresExpansionEqualsLogFrequentlyAtHalf_of_sequence
    (z : ℕ → ℂ)
    (h_ne : ∀ n, z n ≠ (1/2 : ℂ))
    (h_tend : Tendsto z atTop (𝓝 (1/2 : ℂ)))
    (h_eq : ∀ n, -Complex.log (1 - z n) = jonquieresExpansion 1 (z n)) :
    JonquieresExpansionEqualsLogFrequentlyAtHalf := by
  unfold JonquieresExpansionEqualsLogFrequentlyAtHalf
  have h_tendNE : Tendsto z atTop (𝓝[≠] (1/2 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h_tend, ?_⟩
    exact Filter.Eventually.of_forall h_ne
  exact h_tendNE.frequently (Filter.Eventually.frequently
    (Filter.Eventually.of_forall h_eq))

/-- **Sequential constructor for `JonquieresFrequentAgreementAtHalf 1`
    via the Mercator form**. -/
theorem jonquieresFrequentAgreementAtHalf_one_of_sequence_log
    (z : ℕ → ℂ)
    (h_ne : ∀ n, z n ≠ (1/2 : ℂ))
    (h_tend : Tendsto z atTop (𝓝 (1/2 : ℂ)))
    (h_eq : ∀ n, -Complex.log (1 - z n) = jonquieresExpansion 1 (z n)) :
    JonquieresFrequentAgreementAtHalf 1 :=
  jonquieresFrequentAgreementAtHalf_one_of_log
    (jonquieresExpansionEqualsLogFrequentlyAtHalf_of_sequence
      z h_ne h_tend h_eq)

/-! ## Explicit form at the single point `z = 1/2` -/

/-- **Mercator closed form at `z = 1/2`**: `-log(1 - 1/2) = log 2`. -/
theorem neg_log_at_half_eq_log_two :
    -Complex.log (1 - (1/2 : ℂ)) = Complex.log 2 := by
  -- 1 - 1/2 = 1/2; -log(1/2) = log 2
  have h1 : (1 - (1/2 : ℂ)) = (1/2 : ℂ) := by ring
  rw [h1]
  -- side condition for log_inv: arg 2 ≠ π
  have harg : ((2 : ℂ)).arg ≠ Real.pi := by
    have : ((2 : ℂ)).arg = 0 := by
      rw [show ((2 : ℂ)) = ((2 : ℝ) : ℂ) from by norm_cast]
      exact Complex.arg_ofReal_of_nonneg (by norm_num)
    rw [this]
    exact (Real.pi_pos).ne
  -- (1/2 : ℂ) = (2 : ℂ)⁻¹ ; log ((2)⁻¹) = -log 2
  have h2 : (1 / 2 : ℂ) = (2 : ℂ)⁻¹ := by norm_num
  rw [h2, Complex.log_inv _ harg, neg_neg]

/-- **Reduction at the single point**: if the Jonquières expansion at
    `(s, z) = (1, 1/2)` numerically equals `log 2`, the literal pointwise
    identity holds there. -/
theorem polyLog_one_eq_jonquieresExpansion_at_half_of_value
    (h : jonquieresExpansion 1 (1/2 : ℂ) = Complex.log 2) :
    polyLog 1 (1/2 : ℂ) = jonquieresExpansion 1 (1/2 : ℂ) := by
  rw [h]
  rw [polyLog_one (1/2 : ℂ) (by
    have : (1/2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := half_mem_ball_one
    simpa [Metric.mem_ball, dist_zero_right] using this)]
  exact neg_log_at_half_eq_log_two

/-! ## Architecture summary

**This file establishes (axiom-free, no `sorry`)**:

* `JonquieresExpansionEqualsLogFrequentlyAtHalf` — the sharper open
  Prop at `s = 1`: frequent agreement of the Mercator closed form
  `-log(1-z)` with the Jonquières expansion at `s = 1`, near `1/2`.
  No polylog mention.
* `jonquieresFrequentAgreementAtHalf_one_of_log` — REDUCTION.
* `jonquieresExpansionEqualsLogFrequentlyAtHalf_of_sequence` —
  sequential constructor.
* `jonquieresFrequentAgreementAtHalf_one_of_sequence_log` —
  composition.
* `neg_log_at_half_eq_log_two` — `-log(1 - 1/2) = log 2`.
* `polyLog_one_eq_jonquieresExpansion_at_half_of_value` — point-wise
  reduction at `z = 1/2`.

**Residual gap (sharpest formulation at `s = 1`)**:

`JonquieresExpansionEqualsLogFrequentlyAtHalf` — a *purely
expansion-side* frequent-equality Prop: it asks for points
arbitrarily close to (but distinct from) `1/2` where the Jonquières
expansion at `s = 1` equals the elementary function `-log(1 - z)`.

Stage L18 — Frequent agreement at s = 1 via the Mercator closed form.
-/

end PrincipiaTractalis.Analytic.Sheaf
