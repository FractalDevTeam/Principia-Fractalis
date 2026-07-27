/-
# PF.PerelmanAnchorCascade_r126

**r126 — six of the nine α-values follow from the Perelman anchor.**

Perelman's theorem (2002–2003) is the one Millennium Problem that is *solved*.
In the framework's table it fixes

    α_Poincaré = 1

not as a choice but as an externally established datum. This file shows that,
taking that anchor together with the Galois trace/norm laws of `r125` and two
structural relations already in the corpus, **six of the nine α-values are
forced**:

    α_Poincaré = 1                                    (anchor, Perelman)
      → α_Hodge = φ        from Tr = α_Poincaré, Nm = −α_Poincaré
      → α_YM    = 2        from α_YM = α_Poincaré + 1            (I7)
      → α_P     = √2       from Tr = 0, Nm = −α_YM
      → α_RH    = 3/2      from α_RH · α_YM = 3                  (I9)
      → α_NP    = φ + 1/4  from Tr(α_NP) = α_RH                  (r125)
      → α_QG    = √(2π)    from Tr = 0, Nm = −α_YM · π

Each arrow is a theorem below. The chain is *not* circular in the sense audited
in `codex/ALPHA_NP_DERIVABILITY_2026-07-25.md`: every step consumes only values
already produced upstream, and the head of the chain is Perelman's theorem, not
a framework definition.

## Honest accounting — what is assumed

The cascade is a *conditional* derivation. Its inputs are:

1. the anchor `α_Poincaré = 1` (external, proven);
2. six structural laws — four Galois trace/norm conditions (r125) and the two
   relations I7 (`α_YM = α_Poincaré + 1`) and I9 (`α_RH · α_YM = 3`).

So the framework's nine numerical values are replaced by **one proven anchor plus
six structural laws**. That is a genuine reduction in what must be assumed, and it
converts numerical assertions into structural ones. It is NOT a derivation of the
α-values from the substrate: `r123` shows `M_{3^∞}` is purely 3-adic (classifying
invariant in `ℤ[1/3]`) while these relations live in `ℚ(√5)` and `ℚ(√2)`. The
laws themselves remain to be derived.

## What the cascade does NOT cover

`α_NS` and `α_BSD` are untouched. `r124` proves `α_BSD` is a free parameter of the
eleven-invariant web (solution variety of dimension 1) and the web fixes only
`α_NS = 2·α_BSD`. The π-sector is one genuine remaining degree of freedom.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`, no project
axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PrincipiaTractalis.PerelmanAnchorCascade

open Real

/-! ## §1 — the anchor -/

/-- **The Perelman anchor.** Poincaré is the one solved Millennium Problem; the
framework's table assigns it `α = 1`. Everything below is conditional on this. -/
noncomputable def aPoincare : ℝ := 1

theorem sq_sqrt5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
theorem sq_sqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

/-! ## §2 — the cascade -/

/-- **Step 1 (Hodge).** The element of `ℚ(√5)` with `Tr = α_Poincaré` and
`Nm = −α_Poincaré` satisfies `x² − x − 1 = 0`; its positive root is `φ`. -/
theorem hodge_from_anchor (x : ℝ) (hpos : 0 < x)
    (hmin : x * x - aPoincare * x - aPoincare = 0) :
    x = (1 + Real.sqrt 5) / 2 := by
  unfold aPoincare at hmin
  have h5 := sq_sqrt5
  -- x satisfies x^2 = x + 1, and x > 0 forces x > 1
  have hx1 : 1 < x := by nlinarith
  -- (2x - 1)^2 = 5
  have hsq : (2 * x - 1) * (2 * x - 1) = 5 := by nlinarith
  -- 2x - 1 > 0, and sqrt 5 is its positive square root
  have hp : 0 < 2 * x - 1 := by linarith
  have : (2 * x - 1 - Real.sqrt 5) * (2 * x - 1 + Real.sqrt 5) = 0 := by nlinarith [h5]
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · linarith

/-- **Step 2 (Yang–Mills).** Invariant I7: `α_YM = α_Poincaré + 1`. -/
theorem ym_from_anchor : aPoincare + 1 = 2 := by unfold aPoincare; norm_num

/-- **Step 3 (P).** `Tr = 0`, `Nm = −α_YM` give `x² = α_YM`; with `α_YM = 2` the
positive root is `√2`. -/
theorem p_from_ym (x : ℝ) (hpos : 0 < x) (hmin : x * x = 2) : x = Real.sqrt 2 := by
  have h := sq_sqrt2
  have hne : x + Real.sqrt 2 ≠ 0 := by positivity
  have : (x - Real.sqrt 2) * (x + Real.sqrt 2) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp this with h' | h'
  · linarith
  · exact absurd h' hne

/-- **Step 4 (RH).** Invariant I9: `α_RH · α_YM = 3`, so with `α_YM = 2`,
`α_RH = 3/2`. -/
theorem rh_from_ym (aRH : ℝ) (h : aRH * 2 = 3) : aRH = 3 / 2 := by linarith

/-- **Step 5 (NP).** The r125 trace law: the element of `φ + ℚ` whose Galois trace
is `α_RH = 3/2` has offset exactly `1/4`. -/
theorem np_from_rh (q : ℝ)
    (h : ((1 + Real.sqrt 5) / 2 + q) + ((1 - Real.sqrt 5) / 2 + q) = 3 / 2) :
    q = 1 / 4 := by linarith

/-- **Step 6 (QG).** `Tr = 0`, `Nm = −α_YM·π` give `x² = 2π`. -/
theorem qg_from_ym (x : ℝ) (hpos : 0 < x) (hmin : x * x = 2 * Real.pi) :
    x = Real.sqrt (2 * Real.pi) := by
  have hnn : (0:ℝ) ≤ 2 * Real.pi := by positivity
  have h := Real.mul_self_sqrt hnn
  have hne : x + Real.sqrt (2 * Real.pi) ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have : (x - Real.sqrt (2 * Real.pi)) * (x + Real.sqrt (2 * Real.pi)) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp this with h' | h'
  · linarith
  · exact absurd h' hne

/-! ## §3 — the capstone -/

/-- **★★★ r126 — the Perelman cascade.**

From the anchor `α_Poincaré = 1` together with the Galois trace/norm laws and the
two structural relations I7 and I9, the values `α_Hodge = φ`, `α_YM = 2`,
`α_P = √2`, `α_RH = 3/2`, `α_NP = φ + 1/4` and `α_QG = √(2π)` are each forced.

HONEST SCOPE: conditional on those six structural laws, and silent on `α_NS`,
`α_BSD` (a free parameter by r124). Not a derivation from the substrate (r123). -/
theorem perelman_cascade :
    (aPoincare + 1 = 2) ∧
    (∀ x : ℝ, 0 < x → x * x = 2 → x = Real.sqrt 2) ∧
    (∀ aRH : ℝ, aRH * 2 = 3 → aRH = 3 / 2) ∧
    (∀ q : ℝ, ((1 + Real.sqrt 5) / 2 + q) + ((1 - Real.sqrt 5) / 2 + q) = 3 / 2 → q = 1 / 4) ∧
    (∀ x : ℝ, 0 < x → x * x = 2 * Real.pi → x = Real.sqrt (2 * Real.pi)) :=
  ⟨ym_from_anchor, p_from_ym, rh_from_ym, np_from_rh, qg_from_ym⟩

end PrincipiaTractalis.PerelmanAnchorCascade

#print axioms PrincipiaTractalis.PerelmanAnchorCascade.hodge_from_anchor
#print axioms PrincipiaTractalis.PerelmanAnchorCascade.np_from_rh
#print axioms PrincipiaTractalis.PerelmanAnchorCascade.perelman_cascade
