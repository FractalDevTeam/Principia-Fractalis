/-
Demonstration: the single axiom `concentration_implies_algebraic` of
ARCHIVE/.../Hodge_Conjecture_COMPLETE.lean is INCONSISTENT with that file's
own definitions. Definitions copied VERBATIM from the archive file
(lines 26-109, 339-343); only the names are localised.

Nothing here is imported into PF; this file is a probe.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Defs

namespace HodgeArchiveProbe

-- ===== verbatim from the archive file =====

structure AlgebraicVariety where
  ambient : ℕ
  smooth : Bool
  irreducible : Bool

/-- archive line 33-35: cohomology IS ℚ -/
def SingularCohomology (_X : AlgebraicVariety) (_k : ℕ) : Type := ℚ

/-- archive line 49-52 -/
structure AlgebraicCycle (_X : AlgebraicVariety) where
  codimension : ℕ

/-- archive line 54-56 -/
def ChowGroup (X : AlgebraicVariety) (_p : ℕ) : Type := AlgebraicCycle X

/-- archive line 58-62: the cycle class map is the CONSTANT 0 -/
noncomputable def cycle_class_map
    (X : AlgebraicVariety) (p : ℕ) (_Z : ChowGroup X p) :
    SingularCohomology X (2 * p) := (0 : ℚ)

/-- archive line 64-66 -/
def AlgebraicClasses (X : AlgebraicVariety) (p : ℕ) :
    Set (SingularCohomology X (2 * p)) :=
  { ξ | ∃ Z : ChowGroup X p, cycle_class_map X p Z = ξ }

/-- archive line 95-99: spectral concentration is the CONSTANT 0.95 -/
noncomputable def spectral_concentration
    {_X : AlgebraicVariety} {_p : ℕ}
    (_ξ : SingularCohomology _X (2 * _p)) : ℝ := 0.95

-- ===== the archive file's axiom, verbatim (lines 339-343) =====

axiom concentration_implies_algebraic :
  ∀ (X : AlgebraicVariety) (p : ℕ) (ξ : SingularCohomology X (2 * p)),
    spectral_concentration ξ ≥ 0.95 →
    ξ ∈ AlgebraicClasses X p

-- ===== the demonstration =====

/-- The hypothesis of the axiom is a TAUTOLOGY: `0.95 ≥ 0.95`. -/
theorem hypothesis_is_vacuous
    (X : AlgebraicVariety) (p : ℕ) (ξ : SingularCohomology X (2 * p)) :
    spectral_concentration ξ ≥ 0.95 := le_refl _

/-- `AlgebraicClasses` is exactly `{0}`, because the cycle class map is constant 0. -/
theorem algebraicClasses_eq_zero
    (X : AlgebraicVariety) (p : ℕ) (ξ : SingularCohomology X (2 * p)) :
    ξ ∈ AlgebraicClasses X p ↔ ξ = (0 : ℚ) := by
  constructor
  · rintro ⟨_, h⟩; exact h.symm
  · intro h; exact ⟨⟨0⟩, h.symm⟩

/-- Therefore EVERY element of the "cohomology" is 0. -/
theorem every_class_is_zero
    (X : AlgebraicVariety) (p : ℕ) (ξ : SingularCohomology X (2 * p)) :
    ξ = (0 : ℚ) :=
  (algebraicClasses_eq_zero X p ξ).mp
    (concentration_implies_algebraic X p ξ (hypothesis_is_vacuous X p ξ))

/-- **The axiom is inconsistent: `False` follows.** -/
theorem archive_axiom_is_inconsistent : False := by
  have h : (1 : ℚ) = (0 : ℚ) :=
    every_class_is_zero ⟨0, true, true⟩ 0 (1 : ℚ)
  exact absurd h (by norm_num)

#print axioms archive_axiom_is_inconsistent

end HodgeArchiveProbe
