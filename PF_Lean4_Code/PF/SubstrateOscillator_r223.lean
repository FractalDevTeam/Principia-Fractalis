/-
# r223: `SubstrateOscillator` — the unified per-α substrate machine.

★ 2026-08-12 r223 — ELEVATING the r212 / r220 / r221 / r222 stack to a single
per-α substrate structure. All 9 canonical corpus alphas become instances of
ONE Lean object; every substrate-side theorem becomes a universal method on
that object; each pillar's prediction becomes an evaluation. No fragmentation,
no per-axis attacks. Framework first. ★

## What this file does

Packages the substrate machinery from
- r212 `PF/SigmaAbscissa_r212.lean` — `σ(α) = log₃ |1 + 2 cos(πα)|`,
- r220 `PF/LogPeriodicity_r220.lean` — `logFrequency = 2π / ln 3`, `χ(ω)`,
- r221 `PF/ChiNormUnity_r221.lean`   — `‖χ(e^{iπα})‖ = 1 ↔ α ∈ ½ℤ+½ ∪ 2ℤ+1`,
- r222 `PF/LogCosineNextZero_r222.lean` — `√3` shift forced by frequency,

into a single Lean structure

    structure SubstrateOscillator where
      α  : ℝ
      A  : ℝ
      φ₀ : ℝ
      hA : A ≠ 0

with methods

- `sigma : ℝ`                             — r212 abscissa
- `g : ℝ → ℝ`                             — `gLogCos A σ φ₀`
- `next_zero_forced`                      — r222 √3 shift, EVERY oscillator
- `zero_at_sqrt_three_pow_{up,down}`      — the full AP of zeros, EVERY oscillator
- `constant_amplitude_iff_full`           — r212 classification (three branches)
- `constant_amplitude_iff_half_or_odd`    — r221 characterisation, non-degenerate branch

and 9 corpus instances `SO_αPoincare … SO_αNS`, each named after r212's canonical table.

## The elevation

Before r223, each substrate consequence was written per-pillar. r223 replaces
that with `α ↦ SubstrateOscillator α`, so every substrate consequence is a
**method** on the structure. The 9 corpus alphas are 9 evaluations, not 9
separate proofs. New candidate pillars (e.g. `α_HN = 5` from
`docs/COSMOLOGY_LOGPERIODIC_G_2026-08-12.md`) are added by extending the
corpus instance list — no proof engineering required.

## The cross-pillar dichotomy (§5)

Among r212's 9 canonical corpus alphas, EXACTLY TWO are constant-amplitude
(`σ = 0`):

    α_Poincaré = 1     — constant amplitude (odd integer, r221 hit)
    α_RH       = 3/2   — constant amplitude (half-integer, r221 hit)
    α_YM       = 2     — σ = 1 (linear amplitude growth)
    α_Hodge    = φ     — σ ≈ +0.496
    α_P        = √2    — σ ≈ -0.692
    α_NP       = φ+1/4 — σ ≈ +0.947
    α_QG       = √(2π) — σ ≈ -0.039 (near-critical)
    α_BSD      = 3π/4  — σ ≈ +0.571
    α_NS       = 3π/2  — σ ≈ -1.308 (cosmology axis)

Universally quantified as `corpus_constant_amplitude_dichotomy` — nine
conjuncts, each a direct application of r212's per-alpha `sigma_*` and
`sigma_alpha*_ne_zero_one` theorems, unified as one Lean theorem over the
`SubstrateOscillator` structure.

## Scope

* NOT a Millennium discharge. The 9 canonical claims remain ancillary
  consequences of the substrate; this file organises them as instances of
  one machine, not as separate attacks.
* NOT a substrate derivation of the 9 alpha values themselves. They are
  named inputs from the corpus manuscript.
* NOT a physical claim about any pillar's observable. Each `g` is a
  parametrised prediction structure, not a fit to data.
* IS a unified elevation of the r212/r220/r221/r222 stack into one Lean
  object, with the 9 canonical pillars as instances and the cross-pillar
  dichotomy as a corpus-wide theorem.

## Contents

§1 The structure and its methods (`sigma`, `g`).
§2 Universal theorems inherited from r222: √3 shift and iterations.
§3 Universal theorems inherited from r212/r221: constant-amplitude classification.
§4 The 9 corpus instances `SO_αPoincare … SO_αNS`.
§5 The corpus-wide dichotomy `corpus_constant_amplitude_dichotomy`.
§6 Axiom check.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.ChiNormUnity_r221
import PF.LogCosineNextZero_r222

open scoped Real

namespace PrincipiaTractalis

/-! ## §1 The structure and its methods. -/

/-- **The substrate oscillator at a pillar's alpha.**

Packages
* `α`  : the pillar's alpha (any real; the 9 canonical corpus values are instances),
* `A`  : amplitude (data-fit),
* `φ₀` : phase (data-fit),
* `hA` : `A ≠ 0` (otherwise `g ≡ 0`, trivial).

The abscissa `σ(α)` and the observable
`g(a) = A · a^σ · cos(logFrequency · ln a + φ₀)` are derived. All
substrate-side theorems (√3 shift, constant-amplitude classification)
become methods on this structure. -/
structure SubstrateOscillator where
  α  : ℝ
  A  : ℝ
  φ₀ : ℝ
  hA : A ≠ 0

namespace SubstrateOscillator

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis.LogPeriodicity
open PrincipiaTractalis.ChiNormUnity
open PrincipiaTractalis.LogCosineNextZero

/-- The r212 abscissa `σ(α) = log₃ |1 + 2 cos(πα)|` at this oscillator's α. -/
noncomputable def sigma (SO : SubstrateOscillator) : ℝ :=
  PrincipiaTractalis.SigmaAbscissa.sigma SO.α

/-- The observable `g(a) = A · a^σ(α) · cos(logFrequency · log a + φ₀)` — the
r220 log-cosine ansatz at this pillar's α, with envelope exponent σ. -/
noncomputable def g (SO : SubstrateOscillator) (a : ℝ) : ℝ :=
  gLogCos SO.A SO.sigma SO.φ₀ a

/-! ## §2 Universal theorems inherited from r222 — the `√3` shift. -/

/-- **Every `SubstrateOscillator` inherits the r222 `√3` shift.** If `a₀ > 0`
is a zero of the observable, then both `√3 · a₀` and `a₀ / √3` are zeros —
regardless of which pillar. The multiplier `√3` depends only on
`logFrequency = 2π/ln 3`, not on the pillar's `α`. -/
theorem next_zero_forced (SO : SubstrateOscillator)
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hzero : SO.g a₀ = 0) :
    SO.g (Real.sqrt 3 * a₀) = 0 ∧ SO.g (a₀ / Real.sqrt 3) = 0 :=
  g_logcos_next_zero_forced_by_frequency SO.hA ha₀ hzero

/-- **Up-direction iteration.**  For every `n : ℕ`, `√3^n · a₀` is a zero. -/
theorem zero_at_sqrt_three_pow_up (SO : SubstrateOscillator)
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hzero : SO.g a₀ = 0) (n : ℕ) :
    SO.g (Real.sqrt 3 ^ n * a₀) = 0 :=
  g_logcos_zero_at_sqrt_three_pow_up SO.hA ha₀ hzero n

/-- **Down-direction iteration.**  For every `n : ℕ`, `a₀ / √3^n` is a zero. -/
theorem zero_at_div_sqrt_three_pow (SO : SubstrateOscillator)
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hzero : SO.g a₀ = 0) (n : ℕ) :
    SO.g (a₀ / Real.sqrt 3 ^ n) = 0 :=
  g_logcos_zero_at_div_sqrt_three_pow SO.hA ha₀ hzero n

/-! ## §3 Universal theorems inherited from r212/r221 — the constant-amplitude classification. -/

/-- **Constant-amplitude classification, full version.**  From r212's
`sigma_eq_zero_iff_full`: `σ = 0` iff `α` lies in one of the three
level-set branches — the two clean branches (half-integers, odd integers)
plus the degenerate branch `1 + 2·cos(πα) = 0` (α ∈ `2ℤ/3`). -/
theorem constant_amplitude_iff_full (SO : SubstrateOscillator) :
    SO.sigma = 0 ↔
      1 + 2 * Real.cos (π * SO.α) = 0
        ∨ Real.cos (π * SO.α) = 0
        ∨ Real.cos (π * SO.α) = -1 :=
  sigma_eq_zero_iff_full SO.α

/-- **Constant-amplitude classification, non-degenerate branch.**  Under the
non-degeneracy hypothesis `1 + 2·cos(πα) ≠ 0`, `σ = 0` iff `α` is a
half-integer or an odd integer — the exact r221 characterisation. -/
theorem constant_amplitude_iff_half_or_odd (SO : SubstrateOscillator)
    (hne : 1 + 2 * Real.cos (π * SO.α) ≠ 0) :
    SO.sigma = 0 ↔
      (∃ k : ℤ, SO.α = 1 / 2 + k) ∨ (∃ k : ℤ, SO.α = 1 + 2 * k) := by
  rw [show SO.sigma = PrincipiaTractalis.SigmaAbscissa.sigma SO.α from rfl,
      sigma_eq_zero_iff SO.α hne]
  constructor
  · rintro (h | h)
    · exact Or.inl ((cos_pi_mul_eq_zero_iff SO.α).mp h)
    · exact Or.inr ((cos_pi_mul_eq_neg_one_iff SO.α).mp h)
  · rintro (h | h)
    · exact Or.inl ((cos_pi_mul_eq_zero_iff SO.α).mpr h)
    · exact Or.inr ((cos_pi_mul_eq_neg_one_iff SO.α).mpr h)

end SubstrateOscillator

/-! ## §4 The 9 corpus instances — r212's canonical alphas as `SubstrateOscillator`s. -/

/-- `α_Poincaré = 1`. -/
def SO_αPoincare (A φ₀ : ℝ) (hA : A ≠ 0) : SubstrateOscillator :=
  { α := 1, A := A, φ₀ := φ₀, hA := hA }

/-- `α_RH = 3/2`. -/
noncomputable def SO_αRH (A φ₀ : ℝ) (hA : A ≠ 0) : SubstrateOscillator :=
  { α := 3 / 2, A := A, φ₀ := φ₀, hA := hA }

/-- `α_YM = 2`. -/
def SO_αYM (A φ₀ : ℝ) (hA : A ≠ 0) : SubstrateOscillator :=
  { α := 2, A := A, φ₀ := φ₀, hA := hA }

/-- `α_Hodge = φ` (golden ratio). -/
noncomputable def SO_αHodge (A φ₀ : ℝ) (hA : A ≠ 0) : SubstrateOscillator :=
  { α := Real.goldenRatio, A := A, φ₀ := φ₀, hA := hA }

/-- `α_P = √2`. -/
noncomputable def SO_αP (A φ₀ : ℝ) (hA : A ≠ 0) : SubstrateOscillator :=
  { α := Real.sqrt 2, A := A, φ₀ := φ₀, hA := hA }

/-- `α_NP = φ + 1/4`. -/
noncomputable def SO_αNP (A φ₀ : ℝ) (hA : A ≠ 0) : SubstrateOscillator :=
  { α := Real.goldenRatio + 1 / 4, A := A, φ₀ := φ₀, hA := hA }

/-- `α_QG = √(2π)`. -/
noncomputable def SO_αQG (A φ₀ : ℝ) (hA : A ≠ 0) : SubstrateOscillator :=
  { α := Real.sqrt (2 * π), A := A, φ₀ := φ₀, hA := hA }

/-- `α_BSD = 3π/4`. -/
noncomputable def SO_αBSD (A φ₀ : ℝ) (hA : A ≠ 0) : SubstrateOscillator :=
  { α := 3 * π / 4, A := A, φ₀ := φ₀, hA := hA }

/-- `α_NS = 3π/2` (cosmology axis). -/
noncomputable def SO_αNS (A φ₀ : ℝ) (hA : A ≠ 0) : SubstrateOscillator :=
  { α := 3 * π / 2, A := A, φ₀ := φ₀, hA := hA }

/-! ## §5 The cross-pillar dichotomy — exactly TWO of the 9 canonical alphas are constant-amplitude. -/

/-- **The corpus dichotomy.**  Among r212's 9 canonical corpus alphas, EXACTLY
TWO satisfy `σ = 0` (constant amplitude): `α_Poincaré = 1` and `α_RH = 3/2`.
The other seven all have `σ ≠ 0` (envelope-carrying).

Each conjunct is a direct application of r212's per-alpha theorems — this file
bundles the r212/r221 corpus reading as one theorem over the
`SubstrateOscillator` structure. -/
theorem corpus_constant_amplitude_dichotomy (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αPoincare A φ₀ hA).sigma = 0
      ∧ (SO_αRH A φ₀ hA).sigma = 0
      ∧ (SO_αYM A φ₀ hA).sigma ≠ 0
      ∧ (SO_αHodge A φ₀ hA).sigma ≠ 0
      ∧ (SO_αP A φ₀ hA).sigma ≠ 0
      ∧ (SO_αNP A φ₀ hA).sigma ≠ 0
      ∧ (SO_αQG A φ₀ hA).sigma ≠ 0
      ∧ (SO_αBSD A φ₀ hA).sigma ≠ 0
      ∧ (SO_αNS A φ₀ hA).sigma ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact SigmaAbscissa.sigma_one
  · exact SigmaAbscissa.sigma_three_halves
  · show PrincipiaTractalis.SigmaAbscissa.sigma 2 ≠ 0
    rw [SigmaAbscissa.sigma_two]; norm_num
  · exact SigmaAbscissa.sigma_alphaHodge_ne_zero_one.1
  · exact SigmaAbscissa.sigma_alphaP_ne_zero_one.1
  · exact SigmaAbscissa.sigma_alphaNP_ne_zero_one.1
  · exact SigmaAbscissa.sigma_alphaQG_ne_zero_one.1
  · exact SigmaAbscissa.sigma_alphaBSD_ne_zero_one.1
  · exact SigmaAbscissa.sigma_alphaNS_ne_zero_one.1

/-! ## §6 Axiom check. -/

#print axioms PrincipiaTractalis.SubstrateOscillator.sigma
#print axioms PrincipiaTractalis.SubstrateOscillator.g
#print axioms PrincipiaTractalis.SubstrateOscillator.next_zero_forced
#print axioms PrincipiaTractalis.SubstrateOscillator.zero_at_sqrt_three_pow_up
#print axioms PrincipiaTractalis.SubstrateOscillator.zero_at_div_sqrt_three_pow
#print axioms PrincipiaTractalis.SubstrateOscillator.constant_amplitude_iff_full
#print axioms PrincipiaTractalis.SubstrateOscillator.constant_amplitude_iff_half_or_odd
#print axioms PrincipiaTractalis.corpus_constant_amplitude_dichotomy

end PrincipiaTractalis
