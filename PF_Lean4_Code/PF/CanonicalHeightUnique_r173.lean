/-
# PF.CanonicalHeightUnique_r173

★★★ 2026-07-31 — THE CANONICAL HEIGHT IS UNIQUE ★★★

r171 built the canonical height curve-independently from a doubling window.  It
did not prove the height is the *only* such function, and it kept the abelian
group around throughout.

This stone does two things.

**1. The group was never needed.**  `MathlibCandidates.TateLimit` (our mathlib
upstream candidate) redoes r171's construction over a bare self-map `T : α → α`
with no algebra at all: given `|f (T x) − d·f x| ≤ C` and `d > 1`, the rescaled
iterates `f (T^[n] x)/dⁿ` converge.  Tate's telescoping argument, in the
generality it actually has.  Here we prove r171's `canheight` IS that limit at
`T = (· + ·)`, `d = 4`, `C = log κ`, and re-derive the doubling law, the window,
and the shifted window from the abstract statements.  If this file compiles, the
generalisation is faithful — no silent loss.

**2. Uniqueness, which is new.**  `canheight_unique`: if `g` satisfies
`g(R+R) = 4·g(R)` exactly and stays a *bounded* distance from `lognh`, then
`g = canheight lognh`.  No hypothesis on how large the bound is.  This upgrades
ĥ from "a limit we happened to construct" to "the unique 4-homogeneous function
near the naive height" — the characterisation Néron–Tate theory actually uses,
and the one a referee will ask for.

r171 is left untouched; this file is additive.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-31.
-/
import TateLimit
import PF.CanonicalHeightGeneric_r171

open Filter Topology
open PrincipiaTractalis.CanonicalHeightGeneric

namespace PrincipiaTractalis.CanonicalHeightUnique

variable {G : Type} [AddCommGroup G] {lognh : G → ℝ} {κ : ℝ}

/-- The doubling self-map, which is all of the group structure r171 ever used. -/
def dbl (G : Type) [AddCommGroup G] : G → G := fun R => R + R

/-- r171's `hseq` is the general `tateSeq` at `T = dbl`, `d = 4`. -/
theorem hseq_eq_tateSeq (R : G) (n : ℕ) :
    hseq lognh R n = Function.tateSeq lognh (dbl G) 4 R n := by
  have hiter : ∀ (m : ℕ) (S : G), (dbl G)^[m] S = ((2 : ℤ) ^ m) • S := by
    intro m
    induction m with
    | zero => intro S; simp
    | succ k ih =>
        intro S
        rw [Function.iterate_succ_apply', ih, dbl, ← two_zsmul, ← mul_zsmul,
          ← pow_succ']
  simp only [hseq, Function.tateSeq, hiter]

/-- r171's `canheight` is the general `tateLimit`. -/
theorem canheight_eq_tateLimit (lognh : G → ℝ) :
    canheight lognh = Function.tateLimit lognh (dbl G) 4 := by
  funext R
  simp only [canheight, Function.tateLimit]
  congr 1
  funext n
  exact hseq_eq_tateSeq R n

/-- A `HeightWindow` is exactly the general hypothesis at `d = 4`, `C = log κ`. -/
theorem window_to_general (hw : HeightWindow lognh κ) :
    ∀ R : G, |lognh (dbl G R) - 4 * lognh R| ≤ Real.log κ :=
  fun R => hw.window R

/-! ### The five r171 conclusions, re-derived from the general theorem. -/

theorem dbl' (hw : HeightWindow lognh κ) (R : G) :
    canheight lognh (R + R) = 4 * canheight lognh R := by
  rw [canheight_eq_tateLimit]
  exact Function.tateLimit_comp_self (by norm_num) (window_to_general hw) R

theorem window' (hw : HeightWindow lognh κ) (R : G) :
    |canheight lognh R - lognh R| ≤ Real.log κ / 3 := by
  rw [canheight_eq_tateLimit]
  have := Function.abs_tateLimit_sub_le (d := 4) (by norm_num)
    (window_to_general hw) R
  norm_num at this
  exact this

theorem window_shift' (hw : HeightWindow lognh κ) (R : G) (n : ℕ) :
    |canheight lognh R - hseq lognh R n| ≤ Real.log κ / 3 / 4 ^ n := by
  rw [canheight_eq_tateLimit, hseq_eq_tateSeq]
  have := Function.abs_tateLimit_sub_iterate_le (d := 4) (by norm_num)
    (window_to_general hw) R n
  norm_num at this
  exact this

/-- **Uniqueness — new, r171 never proved this.**  The canonical height is the
*only* exactly-4-homogeneous function at bounded distance from `lognh`. -/
theorem canheight_unique (hw : HeightWindow lognh κ) {g : G → ℝ} {B : ℝ}
    (hg : ∀ R : G, g (R + R) = 4 * g R) (hb : ∀ R, |g R - lognh R| ≤ B) :
    g = canheight lognh := by
  rw [canheight_eq_tateLimit]
  refine Function.eq_of_comp_self_of_abs_sub_le (d := 4) (B := B + Real.log κ / 3)
    (by norm_num) (fun R => hg R) ?_ ?_
  · intro R
    exact Function.tateLimit_comp_self (by norm_num) (window_to_general hw) R
  · intro R
    have h1 := hb R
    have h2 : |Function.tateLimit lognh (dbl G) 4 R - lognh R| ≤ Real.log κ / 3 := by
      have := Function.abs_tateLimit_sub_le (d := 4) (by norm_num)
        (window_to_general hw) R
      norm_num at this
      exact this
    calc |g R - Function.tateLimit lognh (dbl G) 4 R|
        = |(g R - lognh R) + (lognh R - Function.tateLimit lognh (dbl G) 4 R)| := by
          ring_nf
      _ ≤ |g R - lognh R| + |lognh R - Function.tateLimit lognh (dbl G) 4 R| :=
          abs_add _ _
      _ ≤ B + Real.log κ / 3 := by
          rw [abs_sub_comm (lognh R)]; exact add_le_add h1 h2

end PrincipiaTractalis.CanonicalHeightUnique

#print axioms PrincipiaTractalis.CanonicalHeightUnique.canheight_eq_tateLimit
#print axioms PrincipiaTractalis.CanonicalHeightUnique.dbl'
#print axioms PrincipiaTractalis.CanonicalHeightUnique.window'
#print axioms PrincipiaTractalis.CanonicalHeightUnique.window_shift'
#print axioms PrincipiaTractalis.CanonicalHeightUnique.canheight_unique
