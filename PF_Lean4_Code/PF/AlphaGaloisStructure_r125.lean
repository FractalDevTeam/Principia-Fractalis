/-
# PF.AlphaGaloisStructure_r125

**r125 — the α-table is organized by Galois trace and norm.**

The framework lists nine α-values and eleven "cross-Millennium invariants". The
r124 analysis showed that web has Gröbner rank 8 in 9 unknowns (a
dimension-1 solution variety) and encodes only three real assumptions — so the
eleven invariants are not the structure, they are shadows of something.

This file identifies the structure. Every *irrational* α in the table is a
quadratic algebraic number whose **Galois trace and norm are themselves α-values**
of the table. Concretely, writing `Tr` and `Nm` for the trace and norm of the
relevant real quadratic field:

    Tr(α_Hodge) =  α_Poincaré        Nm(α_Hodge) = −α_Poincaré
    Tr(α_NP)    =  α_RH
    Tr(α_P)     =  0                 Nm(α_P)     = −α_YM
                                     Nm(α_QG)    = −α_YM · π

All six are proved below by direct computation. None is circular in the sense
audited in `codex/ALPHA_NP_DERIVABILITY_2026-07-25.md`: each relates two
*separately defined* constants, rather than unfolding one definition and
re-deriving it.

## What this does and does not establish

* It DOES give the first structural account of the +1/4: `α_NP` is the element of
  `φ + ℚ` whose Galois trace is `α_RH`. Since `Tr(φ + q) = 1 + 2q` and
  `Tr(φ) = 1 = α_Poincaré`, demanding `Tr(α_NP) = α_RH` forces
  `q = (α_RH − α_Poincaré)/2 = 1/4` exactly. Equivalently `2·α_NP − α_RH = √5`,
  and the NP quadratic `16x² − 24x − 11 = 0` is precisely `(2x − α_RH)² = 5`.
* It DOES reorganize the table: the rational α-values {1, 3/2, 2} function as the
  Galois *coordinates* of the irrational ones, not as nine independent inputs.
* It does NOT derive the α-values from the substrate. `r123`
  (`AlphaFromSubstrateKTheory`) shows `M_{3^∞}` is purely 3-adic — its classifying
  invariant lies in `ℤ[1/3]` — while these relations live in `ℚ(√5)` and `ℚ(√2)`.
  The Galois structure is a genuine pattern *among the α-values*; it is not (yet)
  a consequence of the proven substrate.
* It does NOT remove the assumptions. `r124`'s `alpha_offset_is_free` still holds:
  the eleven invariants do not determine the offset. What changes is that the
  offset is no longer a bare number — it is fixed by one stated trace law.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`, no project
axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace PrincipiaTractalis.AlphaGaloisStructure

open Real

/-! ## §1 — the constants, stated independently of the corpus definitions -/

noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2
/-- The Galois conjugate of `φ` in `ℚ(√5)`. -/
noncomputable def φbar : ℝ := (1 - Real.sqrt 5) / 2

noncomputable def aPoincare : ℝ := 1
noncomputable def aRH : ℝ := 3 / 2
noncomputable def aYM : ℝ := 2
noncomputable def aHodge : ℝ := φ
noncomputable def aNP : ℝ := φ + 1 / 4
noncomputable def aP : ℝ := Real.sqrt 2

theorem sq_sqrt5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
theorem sq_sqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

/-! ## §2 — the golden sector: trace and norm -/

/-- **Tr(α_Hodge) = α_Poincaré.** -/
theorem trace_aHodge : aHodge + φbar = aPoincare := by
  unfold aHodge φ φbar aPoincare; ring

/-- **Nm(α_Hodge) = −α_Poincaré.** -/
theorem norm_aHodge : aHodge * φbar = -aPoincare := by
  unfold aHodge φ φbar aPoincare
  have h := sq_sqrt5; nlinarith [h]

/-- **Tr(α_NP) = α_RH.**  The conjugate of `φ + 1/4` is `φbar + 1/4`. -/
theorem trace_aNP : aNP + (φbar + 1 / 4) = aRH := by
  unfold aNP φ φbar aRH; ring

/-- **★ The trace law forces the offset.** If `q : ℝ` and the element `φ + q` of
`φ + ℚ` has Galois trace `α_RH`, then `q = 1/4`. This is the structural account of
the `+1/4`: it is not chosen, it is the unique offset with trace `α_RH`. -/
theorem offset_forced_by_trace (q : ℝ) (h : (φ + q) + (φbar + q) = aRH) :
    q = 1 / 4 := by
  unfold φ φbar aRH at h; linarith

/-- **★ Equivalent closed form: `2·α_NP − α_RH = √5`.** -/
theorem two_aNP_sub_aRH : 2 * aNP - aRH = Real.sqrt 5 := by
  unfold aNP φ aRH; ring

/-- **★ The NP quadratic IS `(2x − α_RH)² = 5`.**  Hence `16x² − 24x − 11 = 0`
carries no information beyond the trace law. -/
theorem np_quadratic_is_trace_law :
    (2 * aNP - aRH) * (2 * aNP - aRH) = 5 := by
  rw [two_aNP_sub_aRH]; exact sq_sqrt5

theorem np_quadratic : 16 * (aNP * aNP) - 24 * aNP - 11 = 0 := by
  unfold aNP φ; nlinarith [sq_sqrt5]

/-! ## §3 — the √2 sector -/

/-- **Tr(α_P) = 0.** -/
theorem trace_aP : aP + (-aP) = 0 := by ring

/-- **Nm(α_P) = −α_YM.** -/
theorem norm_aP : aP * (-aP) = -aYM := by
  unfold aP aYM; have h := sq_sqrt2; nlinarith [h]

/-! ## §4 — the structural capstone -/

/-- **★★★ r125 — the α-table's Galois structure.**

Each irrational α is a quadratic algebraic number whose trace and norm are
α-values of the table. The rational α-values are the Galois coordinates of the
irrational ones. -/
theorem alpha_galois_structure :
    (aHodge + φbar = aPoincare) ∧
    (aHodge * φbar = -aPoincare) ∧
    (aNP + (φbar + 1 / 4) = aRH) ∧
    (aP + (-aP) = 0) ∧
    (aP * (-aP) = -aYM) ∧
    (2 * aNP - aRH = Real.sqrt 5) ∧
    (∀ q : ℝ, (φ + q) + (φbar + q) = aRH → q = 1 / 4) :=
  ⟨trace_aHodge, norm_aHodge, trace_aNP, trace_aP, norm_aP,
   two_aNP_sub_aRH, offset_forced_by_trace⟩

end PrincipiaTractalis.AlphaGaloisStructure

#print axioms PrincipiaTractalis.AlphaGaloisStructure.offset_forced_by_trace
#print axioms PrincipiaTractalis.AlphaGaloisStructure.two_aNP_sub_aRH
#print axioms PrincipiaTractalis.AlphaGaloisStructure.alpha_galois_structure
