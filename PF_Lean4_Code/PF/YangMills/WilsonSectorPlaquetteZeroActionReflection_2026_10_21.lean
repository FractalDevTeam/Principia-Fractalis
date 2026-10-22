/-
# Yang-Mills — `timeReflectionPlaquette` preserves non-diagonality

**Rio's §2 ACER directive, 2026-10-21.** Small lemma: non-diagonality
(`p.2.1 ≠ p.2.2`) is a `timeReflectionPlaquette`-invariant property.
Needed for the sum-level sector reflection in the next landing: after
reindexing via `timeReflectionPlaquette_bijective`, non-diagonal
plaquettes map to non-diagonal plaquettes, so the density-zero diagonal
cases can be dropped on both sides without disturbing the bijection.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-21.
-/
import PF.YangMills.WilsonSectorPlaquetteZeroReflection_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **Non-diagonality is `timeReflectionPlaquette`-invariant.**

Case split on `timeReflectionPlaquette`'s four branches:
* TT (`μ = ν = 0`): image is `(..., 0, 0)` — diagonal both sides.
* TF (`μ = 0, ν ≠ 0`): image is `(..., ν, 0)` — `ν ≠ 0` ⇒ non-diag.
* FT (`μ ≠ 0, ν = 0`): image is `(..., 0, μ)` — `μ ≠ 0` ⇒ non-diag.
* FF (`μ ≠ 0, ν ≠ 0`): image is `(..., μ, ν)` — same as original.
-/
lemma timeReflectionPlaquette_nondiag_iff (p : Plaquette L) :
    (timeReflectionPlaquette p).2.1 ≠ (timeReflectionPlaquette p).2.2
      ↔ p.2.1 ≠ p.2.2 := by
  rcases p with ⟨x, μ, ν⟩
  unfold timeReflectionPlaquette
  by_cases hμ : μ = 0
  · subst hμ
    by_cases hν : ν = 0
    · subst hν; simp
    · simp [hν, Ne.symm hν]
  · by_cases hν : ν = 0
    · subst hν; simp [hμ, Ne.symm hμ]
    · simp [hμ, hν]

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.timeReflectionPlaquette_nondiag_iff
