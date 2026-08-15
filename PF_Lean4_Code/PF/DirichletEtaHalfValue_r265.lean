/-
# r265: `dirichletEtaHalf` AS A CONCRETE REAL NUMBER.

★ 2026-08-13 r265 — packaging brick for the Dirichlet eta path. r264
proved `∃ l : ℝ, Tendsto dirichletEtaHalfPartial atTop (𝓝 l)` and
`0 < l` for every such `l`. r265 uses `Classical.choose` to extract a
SPECIFIC real number `dirichletEtaHalf` whose value is a limit of the
partial sums, then re-derives the positivity as a direct fact about
this real number.

## What r265 adds

- `dirichletEtaHalf : ℝ` — the specific real number extracted from
  the r264 existence statement via `Classical.choose`.

- `dirichletEtaHalf_tendsto`:
  `Tendsto dirichletEtaHalfPartial atTop (𝓝 dirichletEtaHalf)` —
  the defining specification.

- `dirichletEtaHalf_positive`:
  `0 < dirichletEtaHalf` — direct corollary of r264
  `dirichletEtaHalf_pos` applied to the specific limit.

- `dirichletEtaHalf_ge_one_minus_inv_sqrt_two`:
  `1 - 1 / √2 ≤ dirichletEtaHalf` — the explicit lower bound from
  mathlib's `Antitone.alternating_series_le_tendsto` at `k = 1`.

## Route B substrate value

r265 packages r264's existential into a usable real number that
downstream bricks (r266+) will connect to `Complex.riemannZeta (1/2)`
via the classical identity `η(s) = (1 - 2^{1-s}) · ζ(s)`.

## Scope

* NOT novel.
* NOT a Millennium discharge.
* IS a packaging brick making `dirichletEtaHalf` a first-class real
  number in the corpus.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.DirichletEtaHalfPositive_r264

open scoped Real

namespace PrincipiaTractalis.DirichletEtaHalfValue

open PrincipiaTractalis.DirichletEtaHalfPositive
open Filter Topology

/-! ## §1 The specific real number `dirichletEtaHalf`. -/

/-- **`dirichletEtaHalf`** — the specific real number obtained by
`Classical.choose` from r264's `dirichletEtaHalfPartial_tendsto`. -/
noncomputable def dirichletEtaHalf : ℝ :=
  Classical.choose dirichletEtaHalfPartial_tendsto

/-- **`dirichletEtaHalf_tendsto`** — the defining spec:
`dirichletEtaHalfPartial` converges to `dirichletEtaHalf`. -/
theorem dirichletEtaHalf_tendsto :
    Tendsto dirichletEtaHalfPartial atTop (𝓝 dirichletEtaHalf) :=
  Classical.choose_spec dirichletEtaHalfPartial_tendsto

/-! ## §2 Positivity. -/

/-- **`dirichletEtaHalf_positive`** — `0 < dirichletEtaHalf`.
Direct application of r264 `dirichletEtaHalf_pos`. -/
theorem dirichletEtaHalf_positive : 0 < dirichletEtaHalf :=
  dirichletEtaHalf_pos _ dirichletEtaHalf_tendsto

/-! ## §3 Explicit lower bound. -/

/-- **`dirichletEtaHalf_ge_one_minus_inv_sqrt_two`** — the explicit
lower bound `1 - 1/√2 ≤ dirichletEtaHalf`, obtained from mathlib's
`Antitone.alternating_series_le_tendsto` at `k = 1`. -/
theorem dirichletEtaHalf_ge_one_minus_inv_sqrt_two :
    1 - 1 / Real.sqrt 2 ≤ dirichletEtaHalf := by
  have h_eq : dirichletEtaHalfPartial =
      fun N => ∑ i ∈ Finset.range N, (-1)^i * (1 / Real.sqrt (i + 1)) := by
    funext N
    unfold dirichletEtaHalfPartial
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hl : Tendsto (fun N => ∑ i ∈ Finset.range N, (-1)^i * (1 / Real.sqrt (i + 1)))
      atTop (𝓝 dirichletEtaHalf) := by
    rw [← h_eq]; exact dirichletEtaHalf_tendsto
  have h_bound := Antitone.alternating_series_le_tendsto hl
    inv_sqrt_succ_antitone 1
  -- h_bound : ∑ i ∈ range 2, (-1)^i * (1/√(i+1)) ≤ dirichletEtaHalf
  have h_sum_eq : ∑ i ∈ Finset.range 2, (-1)^i * (1 / Real.sqrt (i + 1))
      = 1 - 1 / Real.sqrt 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
    have e0 : Real.sqrt (((0 : ℕ) : ℝ) + 1) = 1 := by norm_num
    have e1 : Real.sqrt (((1 : ℕ) : ℝ) + 1) = Real.sqrt 2 := by norm_num
    rw [e0, e1]
    ring
  linarith [h_bound, h_sum_eq.le]

/-! ## §4 Axiom check. -/

#print axioms PrincipiaTractalis.DirichletEtaHalfValue.dirichletEtaHalf_tendsto
#print axioms PrincipiaTractalis.DirichletEtaHalfValue.dirichletEtaHalf_positive
#print axioms PrincipiaTractalis.DirichletEtaHalfValue.dirichletEtaHalf_ge_one_minus_inv_sqrt_two

end PrincipiaTractalis.DirichletEtaHalfValue
