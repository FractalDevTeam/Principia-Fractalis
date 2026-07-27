/-
# PF.AlphaSkeletonUniqueness_r128

★★★★★ 2026-07-27 — THE NINE-TUPLE UNIQUENESS THEOREM ★★★★★

This file proves the statement that `Papers/principia_fractalis_alpha_skeleton_2026-07-13.tex`
makes as its Theorem "Substrate uniqueness", over the object that paper actually
defines: the **nine-tuple**

  (α_Poincaré, α_RH, α_NP, α_NS, α_YM, α_BSD, α_Hodge, α_QG, α_P) ∈ ℝ_{>0}^9.

## Why this file exists

The skeleton paper cites `framework_alpha_unique_under_perelman_anchor`
(`PF/Referee/ClayMasterTheorem.lean`) as the kernel verification of that theorem.
That citation does not hold, for three independent reasons:

1. **Wrong arity.** `AlphaAssignment` has SIX fields (Poincaré, RH, YM, BSD, NS,
   PvNP). The four values `α_NP`, `α_Hodge`, `α_QG`, `α_P` are absent, so the
   theorem cannot pin them.
2. **Wrong P-vs-NP constant.** `framework_alpha.a_PvNP` unfolds to
   `PNPClassSeparationPrecisionBridge.alpha_PvsNP = 5/4`, while the paper's
   α_NP is `φ + 1/4 ≈ 1.868`. The corpus carries two different reals under two
   near-identical names.
3. **α_BSD is assumed, not derived.** `SatisfiesInvariants` contains the clause
   `inv_BSD : a.a_BSD = (3/4) * π`. So the existing theorem pins its values from
   TWO anchors, not one — exactly the free parameter that
   `AlphaWebDegreesOfFreedom_r124` located by Gröbner elimination.

This file fixes all three. `α_BSD` is **derived** here, from the π-scaling law
plus the gauge invariant I6, so the Perelman anchor is the only numerical input.

## The hypothesis set — stated honestly

Nine unknowns, nine constraints, one of which is externally proven:

  (A)  α_Poincaré = 1                       Perelman 2003 — a THEOREM, not a choice
  (L1) α_Hodge² = α_Po·α_Hodge + α_Po       Galois: Tr = α_Po,  Nm = −α_Po
  (I7) α_YM = α_Poincaré + 1                corpus invariant
  (L2) α_P² = α_YM                          Galois: Tr = 0,     Nm = −α_YM
  (I9) α_RH · α_YM = 3                      corpus invariant
  (L3) α_Po + 2(α_NP − α_Hodge) = α_RH      Galois trace law on the coset φ + ℚ
  (L4) α_QG² = α_YM · π                     Galois: Tr = 0,     Nm = −α_YM·π
  (L5) α_NS = α_RH · π                      π-scaling law
  (I6) α_NS = α_YM · α_BSD                  corpus invariant

Five structural laws (L1–L5, two Galois patterns plus one π-scaling), three
corpus invariants (I6, I7, I9), one external anchor (A). The paper's twelve
invariants I1–I12 are then **consequences**, not inputs: I1, I3, I10, I11 are
special cases of L1–L4 at the anchor, and I2, I5, I8, I12 are proved below as
downstream identities. In particular the coefficient `8/3` in I12, which the
paper needs as an independent hypothesis to pin α_BSD, is here derived.

## §5 — the BSD anchor (added at Pablo's direction, 2026-07-27)

The cascade also runs BACKWARD from BSD: `alpha_skeleton_unique_from_BSD`
proves that a positive tuple satisfying the eight LAWS (no Perelman anchor)
with `α_BSD = 3π/4` is the canonical skeleton — including `α_Poincaré = 1`.
So a future kernel-verified derivation of `α_BSD = 3π/4` from literal
L-function data would, by this theorem, force every other α-value. The
Perelman anchor and the BSD anchor are interchangeable rigidity points.

HONEST SCOPE. This is a uniqueness theorem, not a derivation of the α-values
from the substrate. L1–L5 are inputs. `SubstrateForcesWhat` (r123) established
that M_{3^∞} does not force them: the substrate's K-theory is ℤ[1/3], purely
3-adic, while these values are 2-adic and 5-adic. What is proved here is that
the nine-tuple is rigid given the laws and ONE anchor — either end.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`, no project
axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-27.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PrincipiaTractalis.AlphaSkeletonUniqueness

open Real

/-! ## §1 — the nine-tuple -/

/-- The α-skeleton as the paper defines it: a nine-tuple of reals. -/
structure AlphaSkeleton : Type where
  aPoincare : ℝ
  aRH : ℝ
  aNP : ℝ
  aNS : ℝ
  aYM : ℝ
  aBSD : ℝ
  aHodge : ℝ
  aQG : ℝ
  aP : ℝ

/-- Positivity: the paper's skeleton lives in `ℝ_{>0}^9`. -/
structure IsPositive (s : AlphaSkeleton) : Prop where
  pos_Poincare : 0 < s.aPoincare
  pos_RH : 0 < s.aRH
  pos_NP : 0 < s.aNP
  pos_NS : 0 < s.aNS
  pos_YM : 0 < s.aYM
  pos_BSD : 0 < s.aBSD
  pos_Hodge : 0 < s.aHodge
  pos_QG : 0 < s.aQG
  pos_P : 0 < s.aP

/-- The eight structural constraints (five laws + three corpus invariants),
WITHOUT any numerical anchor.  Separating the laws from the anchor is what
lets §3 and §5 anchor the same system at either end. -/
structure StructuralLaws (s : AlphaSkeleton) : Prop where
  /-- (L1) Galois: `Tr(α_Hodge) = α_Po`, `Nm(α_Hodge) = −α_Po`. -/
  hodge_minpoly : s.aHodge * s.aHodge = s.aPoincare * s.aHodge + s.aPoincare
  /-- (I7) corpus invariant. -/
  ym_shift : s.aYM = s.aPoincare + 1
  /-- (L2) Galois: `Tr(α_P) = 0`, `Nm(α_P) = −α_YM`. -/
  p_norm : s.aP * s.aP = s.aYM
  /-- (I9) corpus invariant. -/
  rh_prod : s.aRH * s.aYM = 3
  /-- (L3) Galois trace law on the coset `φ + ℚ`: the offset `q = α_NP − α_Hodge`
      satisfies `Tr(α_Hodge + q) = α_Po + 2q = α_RH`. -/
  np_trace : s.aPoincare + 2 * (s.aNP - s.aHodge) = s.aRH
  /-- (L4) Galois: `Tr(α_QG) = 0`, `Nm(α_QG) = −α_YM·π`. -/
  qg_norm : s.aQG * s.aQG = s.aYM * Real.pi
  /-- (L5) π-scaling law. -/
  ns_scaling : s.aNS = s.aRH * Real.pi
  /-- (I6) corpus invariant. -/
  bsd_gauge : s.aNS = s.aYM * s.aBSD

/-- Laws + the Perelman anchor. -/
structure SkeletonLaws (s : AlphaSkeleton) : Prop extends StructuralLaws s where
  /-- (A) Perelman 2003. -/
  anchor : s.aPoincare = 1

/-- The canonical skeleton of the paper's Definition (nine-class α-skeleton). -/
noncomputable def canonical : AlphaSkeleton where
  aPoincare := 1
  aRH := 3 / 2
  aNP := (1 + Real.sqrt 5) / 2 + 1 / 4
  aNS := 3 * Real.pi / 2
  aYM := 2
  aBSD := 3 * Real.pi / 4
  aHodge := (1 + Real.sqrt 5) / 2
  aQG := Real.sqrt (2 * Real.pi)
  aP := Real.sqrt 2

/-! ## §2 — the forcing lemmas -/

theorem sq_sqrt5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)

theorem sq_sqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

/-- **(L1) at the anchor forces `α_Hodge = φ`.**  `x² = x + 1` with `x > 0`. -/
theorem hodge_forced (x : ℝ) (hpos : 0 < x) (hmin : x * x = 1 * x + 1) :
    x = (1 + Real.sqrt 5) / 2 := by
  have h5 := sq_sqrt5
  have hx1 : 1 < x := by nlinarith
  have hsq : (2 * x - 1) * (2 * x - 1) = 5 := by nlinarith
  have hfac : (2 * x - 1 - Real.sqrt 5) * (2 * x - 1 + Real.sqrt 5) = 0 := by
    nlinarith [h5]
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith

/-- **(L2) at `α_YM = 2` forces `α_P = √2`.** -/
theorem p_forced (x : ℝ) (hpos : 0 < x) (hmin : x * x = 2) : x = Real.sqrt 2 := by
  have h := sq_sqrt2
  have hne : x + Real.sqrt 2 ≠ 0 := by positivity
  have hfac : (x - Real.sqrt 2) * (x + Real.sqrt 2) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp hfac with h' | h'
  · linarith
  · exact absurd h' hne

/-- **(L4) at `α_YM = 2` forces `α_QG = √(2π)`.** -/
theorem qg_forced (x : ℝ) (hpos : 0 < x) (hmin : x * x = 2 * Real.pi) :
    x = Real.sqrt (2 * Real.pi) := by
  have hnn : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h := Real.mul_self_sqrt hnn
  have hne : x + Real.sqrt (2 * Real.pi) ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hfac : (x - Real.sqrt (2 * Real.pi)) * (x + Real.sqrt (2 * Real.pi)) = 0 := by
    nlinarith [h]
  rcases mul_eq_zero.mp hfac with h' | h'
  · linarith
  · exact absurd h' hne

/-- The shared spine: once `α_Poincaré = 1` is in hand (from EITHER anchor),
the laws force every other field. -/
theorem forced_from_poincare (s : AlphaSkeleton) (hp : IsPositive s)
    (hL : StructuralLaws s) (hPo : s.aPoincare = 1) : s = canonical := by
  -- α_YM
  have hYM : s.aYM = 2 := by rw [hL.ym_shift, hPo]; norm_num
  -- α_RH
  have hRH : s.aRH = 3 / 2 := by
    have h := hL.rh_prod; rw [hYM] at h; linarith
  -- α_Hodge
  have hHo : s.aHodge = (1 + Real.sqrt 5) / 2 := by
    refine hodge_forced _ hp.pos_Hodge ?_
    have h := hL.hodge_minpoly; rw [hPo] at h; linarith
  -- α_NP
  have hNP : s.aNP = (1 + Real.sqrt 5) / 2 + 1 / 4 := by
    have h := hL.np_trace; rw [hPo, hRH, hHo] at h; linarith
  -- α_P
  have hP : s.aP = Real.sqrt 2 := by
    refine p_forced _ hp.pos_P ?_
    have h := hL.p_norm; rw [hYM] at h; exact h
  -- α_QG
  have hQG : s.aQG = Real.sqrt (2 * Real.pi) := by
    refine qg_forced _ hp.pos_QG ?_
    have h := hL.qg_norm; rw [hYM] at h; exact h
  -- α_NS
  have hNS : s.aNS = 3 * Real.pi / 2 := by rw [hL.ns_scaling, hRH]; ring
  -- α_BSD — DERIVED, not assumed
  have hBSD : s.aBSD = 3 * Real.pi / 4 := by
    have h := hL.bsd_gauge; rw [hYM, hNS] at h; linarith
  -- assemble
  have hs : s = AlphaSkeleton.mk s.aPoincare s.aRH s.aNP s.aNS s.aYM s.aBSD
      s.aHodge s.aQG s.aP := rfl
  rw [hs, hPo, hRH, hNP, hNS, hYM, hBSD, hHo, hQG, hP]
  rfl

/-! ## §3 — the uniqueness theorem (Perelman anchor) -/

/-- **★★★ r128 — UNIQUENESS OF THE NINE-TUPLE α-SKELETON ★★★**

Any positive nine-tuple satisfying the anchor, the five structural laws and the
three corpus invariants EQUALS the canonical skeleton, field by field.

This is the statement the skeleton paper's Theorem "Substrate uniqueness" makes,
now proved over the nine-tuple it defines, with `α_Poincaré = 1` as the ONLY
numerical input — `α_BSD` is derived, not assumed. -/
theorem alpha_skeleton_unique (s : AlphaSkeleton) (hp : IsPositive s)
    (hL : SkeletonLaws s) : s = canonical :=
  forced_from_poincare s hp hL.toStructuralLaws hL.anchor

/-- **Existence, part 1.** The canonical skeleton is positive. -/
theorem canonical_isPositive : IsPositive canonical := by
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 : ℝ) < 1; norm_num
  · show (0 : ℝ) < 3 / 2; norm_num
  · show (0 : ℝ) < (1 + Real.sqrt 5) / 2 + 1 / 4; positivity
  · show (0 : ℝ) < 3 * Real.pi / 2; positivity
  · show (0 : ℝ) < 2; norm_num
  · show (0 : ℝ) < 3 * Real.pi / 4; positivity
  · show (0 : ℝ) < (1 + Real.sqrt 5) / 2; positivity
  · show (0 : ℝ) < Real.sqrt (2 * Real.pi); exact Real.sqrt_pos.mpr (by positivity)
  · show (0 : ℝ) < Real.sqrt 2; exact Real.sqrt_pos.mpr (by norm_num)

/-- **Existence, part 2.** The canonical skeleton satisfies every structural law. -/
theorem canonical_satisfiesStructural : StructuralLaws canonical := by
  have h5 := sq_sqrt5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ((1 + Real.sqrt 5) / 2) * ((1 + Real.sqrt 5) / 2)
        = 1 * ((1 + Real.sqrt 5) / 2) + 1
    nlinarith [h5]
  · show (2 : ℝ) = 1 + 1; norm_num
  · show Real.sqrt 2 * Real.sqrt 2 = 2; exact sq_sqrt2
  · show (3 / 2 : ℝ) * 2 = 3; norm_num
  · show (1 : ℝ) + 2 * (((1 + Real.sqrt 5) / 2 + 1 / 4) - (1 + Real.sqrt 5) / 2) = 3 / 2
    ring
  · show Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi
    exact Real.mul_self_sqrt (by positivity)
  · show 3 * Real.pi / 2 = (3 / 2 : ℝ) * Real.pi; ring
  · show 3 * Real.pi / 2 = 2 * (3 * Real.pi / 4); ring

/-- **Existence, part 2'.** …and the anchored law set. -/
theorem canonical_satisfiesLaws : SkeletonLaws canonical :=
  { canonical_satisfiesStructural with anchor := rfl }

/-- **★★ Existence and uniqueness in one statement. ★★** -/
theorem alpha_skeleton_exists_unique :
    (IsPositive canonical ∧ SkeletonLaws canonical) ∧
    (∀ s : AlphaSkeleton, IsPositive s → SkeletonLaws s → s = canonical) :=
  ⟨⟨canonical_isPositive, canonical_satisfiesLaws⟩, alpha_skeleton_unique⟩

/-! ## §4 — the paper's remaining invariants are consequences

I1, I3, I10, I11 are the anchored instances of L2, L4, L3, L4 respectively and
are immediate from §3.  The four below are the ones the paper lists as separate
hypotheses; each is proved here from the canonical values, so none of them is
an input.  In particular **I12's coefficient `8/3` is derived**, which is what
removes the second anchor from the existing `ClayMasterTheorem` route. -/

theorem invariant_I2 : canonical.aRH * canonical.aRH = 9 / 4 := by
  show (3 / 2 : ℝ) * (3 / 2) = 9 / 4; norm_num

theorem invariant_I5 : canonical.aNS = 2 * canonical.aBSD := by
  show 3 * Real.pi / 2 = 2 * (3 * Real.pi / 4); ring

theorem invariant_I8 :
    canonical.aRH * canonical.aNS = canonical.aNS + canonical.aBSD := by
  show (3 / 2 : ℝ) * (3 * Real.pi / 2) = 3 * Real.pi / 2 + 3 * Real.pi / 4; ring

theorem invariant_I12 :
    canonical.aQG * canonical.aQG = (8 / 3) * canonical.aBSD := by
  show Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = (8 / 3) * (3 * Real.pi / 4)
  rw [Real.mul_self_sqrt (by positivity)]
  ring

/-- **The four listed invariants hold at the canonical point.**  Together with
§3 this says: the nine constraints pin the tuple, and I2, I5, I8, I12 are then
true — genuine overdetermination, four checks passed rather than four
hypotheses consumed. -/
theorem derived_invariants_hold :
    canonical.aRH * canonical.aRH = 9 / 4 ∧
    canonical.aNS = 2 * canonical.aBSD ∧
    canonical.aRH * canonical.aNS = canonical.aNS + canonical.aBSD ∧
    canonical.aQG * canonical.aQG = (8 / 3) * canonical.aBSD :=
  ⟨invariant_I2, invariant_I5, invariant_I8, invariant_I12⟩

/-! ## §5 — the BSD anchor: the cascade runs backward

If `α_BSD = 3π/4` is ever established from literal L-function data (the
BSD axis), the SAME structural laws force the whole skeleton — including
`α_Poincaré = 1` — with no Perelman input.  The spine: I6 + L5 give
`α_RH = (3/4)·α_YM`; substituting into I9 gives `α_YM² = 4`, and positivity
selects `α_YM = 2`.  A genuine quadratic step, not a rewrite. -/

/-- **★★★ r128 §5 — BSD-ANCHORED UNIQUENESS ★★★**

Any positive nine-tuple satisfying the eight structural laws with
`α_BSD = 3π/4` equals the canonical skeleton.  The Perelman anchor and the
BSD anchor are interchangeable rigidity points of the same system. -/
theorem alpha_skeleton_unique_from_BSD (s : AlphaSkeleton) (hp : IsPositive s)
    (hL : StructuralLaws s) (hBSD : s.aBSD = 3 * Real.pi / 4) : s = canonical := by
  have hpi := Real.pi_pos
  -- I6 + hBSD: aNS = aYM · 3π/4
  have hNS_YM : s.aNS = s.aYM * (3 * Real.pi / 4) := by
    rw [hL.bsd_gauge, hBSD]
  -- L5: aNS = aRH · π  ⟹  aRH · π = aYM · 3π/4  ⟹  aRH = (3/4)·aYM
  have hRH_YM : s.aRH = (3 / 4) * s.aYM := by
    have h := hL.ns_scaling
    rw [hNS_YM] at h
    have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi
    field_simp at h
    nlinarith [h, hpi]
  -- I9: aRH · aYM = 3  ⟹  (3/4)·aYM² = 3  ⟹  aYM² = 4  ⟹  aYM = 2 (positivity)
  have hYM : s.aYM = 2 := by
    have h := hL.rh_prod
    rw [hRH_YM] at h
    have hsq : s.aYM * s.aYM = 4 := by nlinarith
    nlinarith [hp.pos_YM, hsq]
  -- I7 backward: aPoincare = aYM − 1 = 1
  have hPo : s.aPoincare = 1 := by
    have h := hL.ym_shift; rw [hYM] at h; linarith
  exact forced_from_poincare s hp hL hPo

/-- **★★ The two anchors are equivalent over the laws. ★★**
For positive tuples satisfying the structural laws, pinning the Perelman axis
and pinning the BSD axis select the same (unique) point. -/
theorem perelman_anchor_iff_bsd_anchor (s : AlphaSkeleton) (hp : IsPositive s)
    (hL : StructuralLaws s) :
    s.aPoincare = 1 ↔ s.aBSD = 3 * Real.pi / 4 := by
  constructor
  · intro hPo
    have h := forced_from_poincare s hp hL hPo
    rw [h]
    show 3 * Real.pi / 4 = 3 * Real.pi / 4
    rfl
  · intro hBSD
    have h := alpha_skeleton_unique_from_BSD s hp hL hBSD
    rw [h]
    show (1 : ℝ) = 1
    rfl

end PrincipiaTractalis.AlphaSkeletonUniqueness

#print axioms PrincipiaTractalis.AlphaSkeletonUniqueness.alpha_skeleton_unique
#print axioms PrincipiaTractalis.AlphaSkeletonUniqueness.alpha_skeleton_exists_unique
#print axioms PrincipiaTractalis.AlphaSkeletonUniqueness.alpha_skeleton_unique_from_BSD
#print axioms PrincipiaTractalis.AlphaSkeletonUniqueness.perelman_anchor_iff_bsd_anchor
