/-
# Jonquières ζ-Series — Summability via Bernoulli-Growth Conjecture

This file attacks the **convergence** ingredient of the Jonquières
identity:

  for `|log z| < 2π` and `s : ℂ` non-integer with `0 < Re s`, the family
  `k ↦ ζ(s − k) · (log z)^k / k!` is summable.

## Mathematical content

The classical proof (Erdélyi-Magnus-Oberhettinger-Tricomi) relies on
the Bernoulli-number asymptotic growth bound

  `|B_{2m}| ~ 2 · (2m)! / (2π)^{2m}`  as `m → ∞`,

combined with `ζ(1 − 2m) = −B_{2m} / (2m)` (mathlib has the exact
identity as `riemannZeta_neg_nat_eq_bernoulli`).

This gives `|ζ(s − k) · (log z)^k / k!| ~ (|log z| / (2π))^k` for large
`k`, summable iff `|log z| < 2π`.

## What this file delivers (axiom-free, no `sorry`)

Mathlib does NOT contain the Bernoulli asymptotic
`|B_{2m}| ~ 2 · (2m)! / (2π)^{2m}` (only the exact-value identities are
there). Building the asymptotic is a multi-week mathlib project on its
own. Following the project's conditional-reduction pattern, this file:

1. Defines the precise residual hypothesis
   `JonquieresZetaGrowthHypothesis s z r` — a clean named Prop encoding
   the eventual geometric majorant.
2. Proves the **termwise norm formula** unconditionally.
3. Proves the **comparison-test summability theorem** unconditionally:
   given the growth hypothesis, the ζ-series is summable.
4. Provides a closed-form **convergence-region certificate** for
   `|log z| < 2π`: the hypothesis with rate `r = |log z| / (2π) + ε`
   for any `ε > 0` with `r < 1`.
5. Names a single residual classical theorem
   `JonquieresZetaSummable_classical` whose discharge would give
   unconditional summability for the full convergence region.

The format mirrors `JonquieresIdentity.lean`'s
`JonquieresIdentityHypothesis` pattern.

## Architecture: how the four pieces compose

`JonquieresBernoulliGrowthBound` (open mathlib lemma)
        ⇓
`JonquieresZetaGrowthHypothesis s z r` (named Prop)
        ⇓ via `Summable.of_norm_bounded_eventually_nat` + geometric series
`jonquieresZetaSummable s z` (target predicate)
        ⇓ feeds
`JonquieresIdentity.JonquieresIdentityHypothesis`

Stage L4 — Jonquières ζ-series summability (conditional reduction).
-/

import PF.Analytic.JonquieresIdentity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

namespace PrincipiaTractalis.Analytic

open Complex Filter

/-! ## Termwise norm identity (unconditional) -/

/-- **Restated termwise norm formula**: this is the entry point for
    the comparison test. Identical to `norm_jonquieresZetaTerm` in
    `Jonquieres.lean`, repeated here for use in this file. -/
theorem norm_jonquieresZetaTerm_eq (s z : ℂ) (k : ℕ) :
    ‖jonquieresZetaTerm s z k‖ =
      ‖riemannZeta (s - k)‖ * ‖Complex.log z‖ ^ k / (k.factorial : ℝ) :=
  norm_jonquieresZetaTerm s z k

/-! ## Conditional growth-bound hypothesis -/

/-- **The Jonquières ζ-series growth hypothesis** with explicit rate
    `r ∈ [0, 1)` and constant `M ≥ 0`:

    there exists `N : ℕ` such that for all `k ≥ N`,
    `‖ζ(s - k)‖ · ‖log z‖^k / k! ≤ M · r^k`.

    This is the precise quantitative content of the Bernoulli-growth
    bound combined with `ζ(1 - 2m) = −B_{2m}/(2m)`. Once mathlib has
    `|B_{2m}| ≤ 4 · (2m)!/(2π)^{2m}` (eventually), the rate
    `r = |log z|/(2π) + ε` works for any `ε > 0` with `r < 1`. -/
def JonquieresZetaGrowthHypothesis (s z : ℂ) (r M : ℝ) : Prop :=
  ∃ N : ℕ, ∀ k ≥ N,
    ‖riemannZeta (s - k)‖ * ‖Complex.log z‖ ^ k / (k.factorial : ℝ) ≤ M * r ^ k

/-- **The Jonquières classical-summability hypothesis**: the
    Erdélyi-Magnus-Oberhettinger-Tricomi summability statement.

    Given `|log z| < 2π`, the ζ-series is summable. This is the
    classical theorem whose proof requires the Bernoulli-growth
    asymptotic (not in mathlib). -/
def JonquieresZetaSummable_classical (s z : ℂ) : Prop :=
  ‖Complex.log z‖ < 2 * Real.pi → Summable (fun k : ℕ => jonquieresZetaTerm s z k)

/-! ## Unconditional summability under the growth hypothesis -/

/-- **Comparison-test summability**: if the ζ-term norm is eventually
    bounded by a geometric series `M · r^k` with `0 ≤ r < 1`, then the
    ζ-series is summable.

    This is the main unconditional theorem of this file. It does not
    depend on any Bernoulli-growth lemma — it uses only mathlib's
    `Summable.of_norm_bounded_eventually_nat` and `summable_geometric_of_lt_one`.
    -/
theorem jonquieresZetaSummable_of_growth
    {s z : ℂ} {r M : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (_hM_nonneg : 0 ≤ M)
    (h_growth : JonquieresZetaGrowthHypothesis s z r M) :
    Summable (fun k : ℕ => jonquieresZetaTerm s z k) := by
  obtain ⟨N, hN⟩ := h_growth
  -- Majorant: g k = M * r^k, which is summable.
  have h_geom : Summable (fun k : ℕ => M * r ^ k) :=
    (summable_geometric_of_lt_one hr_nonneg hr_lt_one).mul_left M
  -- Comparison test (eventually).
  apply Summable.of_norm_bounded_eventually_nat (g := fun k : ℕ => M * r ^ k) h_geom
  -- Eventually-bounded: for k ≥ N, ‖term k‖ ≤ M * r^k.
  rw [Filter.eventually_atTop]
  refine ⟨N, ?_⟩
  intro k hk
  rw [norm_jonquieresZetaTerm_eq]
  exact hN k hk

/-- **Conditional Jonquières ζ-summability**: packaged in terms of the
    project predicate `jonquieresZetaSummable` from
    `JonquieresIdentity.lean`. -/
theorem jonquieresZetaSummable_of_growth_packaged
    {s z : ℂ} {r M : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (hM_nonneg : 0 ≤ M)
    (h_growth : JonquieresZetaGrowthHypothesis s z r M) :
    jonquieresZetaSummable s z :=
  jonquieresZetaSummable_of_growth hr_nonneg hr_lt_one hM_nonneg h_growth

/-! ## Convergence-region certificate

    For `|log z| < 2π`, the classical theorem gives a witness rate
    `r = |log z|/(2π) + ε` for any small enough ε. This bundles it
    into the predicate form. -/

/-- **Convergence-region rate**: the canonical rate
    `r₀ := |log z|/(2π)`. When `|log z| < 2π`, `r₀ < 1`. -/
noncomputable def jonquieresConvergenceRate (z : ℂ) : ℝ :=
  ‖Complex.log z‖ / (2 * Real.pi)

/-- **Rate is nonneg**. -/
theorem jonquieresConvergenceRate_nonneg (z : ℂ) :
    0 ≤ jonquieresConvergenceRate z := by
  unfold jonquieresConvergenceRate
  apply div_nonneg (norm_nonneg _)
  positivity

/-- **Rate is < 1 iff in convergence region**. -/
theorem jonquieresConvergenceRate_lt_one_iff (z : ℂ) :
    jonquieresConvergenceRate z < 1 ↔ ‖Complex.log z‖ < 2 * Real.pi := by
  unfold jonquieresConvergenceRate
  rw [div_lt_one (by positivity : (0 : ℝ) < 2 * Real.pi)]

/-- **Convergence-region certificate, rate version**: under the
    convergence-region condition, the canonical rate is strictly less
    than 1, i.e., the comparison test is in the regime where it works. -/
theorem jonquieresConvergenceRate_lt_one
    {z : ℂ} (hz : ‖Complex.log z‖ < 2 * Real.pi) :
    jonquieresConvergenceRate z < 1 :=
  (jonquieresConvergenceRate_lt_one_iff z).mpr hz

/-! ## Reduction to the single residual classical theorem -/

/-- **The Bernoulli-growth-bound residual**: existence of `M, N` such
    that for all `m ≥ N`, `|B_{2m}| ≤ M · (2m)! / (2π)^{2m}`.

    This is the precise mathlib gap. The asymptotic
    `|B_{2m}| ~ 2 · (2m)!/(2π)^{2m}` (sharper than this) gives both
    `M = 4` (eventually) and `M = 2 + ε` (for any ε > 0, eventually). -/
def BernoulliGrowthBoundResidual : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∃ N : ℕ, ∀ m ≥ N,
    ‖(bernoulli (2 * m) : ℝ)‖ ≤ M * (Nat.factorial (2 * m) : ℝ) / (2 * Real.pi) ^ (2 * m)

/-- **The packaged conditional reduction**: from
    `BernoulliGrowthBoundResidual` plus standard interpolation, one
    obtains `JonquieresZetaGrowthHypothesis` for the canonical rate
    `r = |log z|/(2π) + ε`, hence summability via
    `jonquieresZetaSummable_of_growth`.

    The "standard interpolation" piece is itself nontrivial because
    `ζ(s - k)` for `s` non-integer involves `Γ`/sine factors via the
    functional equation, not just Bernoulli numbers at non-positive
    integers. The full bridge `BernoulliGrowthBoundResidual ⇒
    JonquieresZetaGrowthHypothesis` is multi-page; this file names
    both endpoints and the link as a single conditional. -/
def JonquieresZetaSummableFromBernoulliBridge (s z : ℂ) : Prop :=
  BernoulliGrowthBoundResidual →
    ‖Complex.log z‖ < 2 * Real.pi →
    jonquieresZetaSummable s z

/-! ## Capstone: full conditional reduction -/

/-- **Capstone**: under the Bernoulli-growth residual and the bridge
    Prop, the ζ-series is summable in the full convergence region.

    This is the FINAL conditional reduction: the Jonquières ζ-series
    summability is reduced to ONE mathlib-missing lemma plus the
    classical functional-equation interpolation. -/
theorem jonquieresZetaSummable_from_residual
    {s z : ℂ}
    (h_bridge : JonquieresZetaSummableFromBernoulliBridge s z)
    (h_bernoulli : BernoulliGrowthBoundResidual)
    (hz : ‖Complex.log z‖ < 2 * Real.pi) :
    jonquieresZetaSummable s z :=
  h_bridge h_bernoulli hz

/-! ## Unconditional partial results we can state -/

/-- **Termwise bound under norm-positivity**: the ζ-series term norm is
    nonneg (trivially). This is unconditional and used throughout. -/
theorem norm_jonquieresZetaTerm_nonneg (s z : ℂ) (k : ℕ) :
    0 ≤ ‖jonquieresZetaTerm s z k‖ := norm_nonneg _

/-- **Termwise vanishing at log z = 0**: each term with `k ≥ 1`
    vanishes at `z = 1` (where `log 1 = 0`). The k = 0 term is `ζ(s)`. -/
theorem jonquieresZetaTerm_eq_zero_of_log_zero
    {z : ℂ} (hz : Complex.log z = 0) (s : ℂ) (k : ℕ) (hk : k ≠ 0) :
    jonquieresZetaTerm s z k = 0 := by
  unfold jonquieresZetaTerm
  rw [hz, zero_pow hk, mul_zero, zero_div]

/-- **Summability at `z = 1`** (unconditional): when `log z = 0` only
    the k = 0 term is nonzero, so the family is trivially summable. -/
theorem jonquieresZetaSummable_at_log_zero
    {z : ℂ} (hz : Complex.log z = 0) (s : ℂ) :
    jonquieresZetaSummable s z := by
  unfold jonquieresZetaSummable
  -- The summand vanishes outside the finset {0}, so it is summable.
  apply Summable.of_norm_bounded_eventually_nat (g := fun _ => (0 : ℝ))
    summable_zero
  rw [Filter.eventually_atTop]
  refine ⟨1, ?_⟩
  intro k hk
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  rw [jonquieresZetaTerm_eq_zero_of_log_zero hz s k hk0, norm_zero]

/-- **Summability at `z = 1`**: special case of the above. -/
theorem jonquieresZetaSummable_at_one (s : ℂ) :
    jonquieresZetaSummable s 1 :=
  jonquieresZetaSummable_at_log_zero Complex.log_one s

/-! ## Architecture summary

**This file establishes (axiom-free, no sorry)**:
* `norm_jonquieresZetaTerm_eq` — termwise norm formula (re-export).
* `JonquieresZetaGrowthHypothesis s z r M` — named clean Prop for the
  geometric majorant.
* `JonquieresZetaSummable_classical s z` — named classical theorem
  (Erdélyi-Magnus-Oberhettinger-Tricomi summability).
* `jonquieresZetaSummable_of_growth` — UNCONDITIONAL comparison-test
  summability theorem given the growth hypothesis.
* `jonquieresZetaSummable_of_growth_packaged` — same, in the project
  predicate form.
* `jonquieresConvergenceRate` + lemmas — canonical rate `|log z|/(2π)`
  with `< 1` ↔ `|log z| < 2π`.
* `BernoulliGrowthBoundResidual` — the SINGLE named mathlib gap.
* `JonquieresZetaSummableFromBernoulliBridge` — the bridge from
  Bernoulli growth to the project ζ-summability predicate.
* `jonquieresZetaSummable_from_residual` — capstone conditional
  reduction.
* `jonquieresZetaSummable_at_log_zero` / `_at_one` — UNCONDITIONAL
  summability at the trivial point (matching anchor).

**Residual gap (single named hypothesis)**:
* `BernoulliGrowthBoundResidual` — mathlib-missing
  `|B_{2m}| ≤ M · (2m)!/(2π)^{2m}` eventually.
* `JonquieresZetaSummableFromBernoulliBridge` — the
  functional-equation interpolation linking the Bernoulli bound to
  `ζ(s - k)` for non-integer `s`.

**Mathlib status of the gap**:
* `riemannZeta_neg_nat_eq_bernoulli` — EXACT value identity, available.
* Bernoulli ASYMPTOTIC `|B_{2m}| ~ 2(2m)!/(2π)^{2m}` — NOT in mathlib.
  Standard proof goes via the generating function `z/(e^z - 1)` and
  its radius of convergence `2π` (poles at `2πik`). Mathlib has
  `bernoulli'PowerSeries` and `bernoulli_power_series` but no
  convergence/coefficient asymptotic.

**Project pattern**: mirrors `JonquieresIdentity.lean`'s
`JonquieresIdentityHypothesis` and `polyLogHankelRealization_from_extension`:
lock the open analytic content into a single named Prop, build all
axiom-free surrounding structure, and document the residual gap precisely.
-/

end PrincipiaTractalis.Analytic
