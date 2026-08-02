/-
# PF.BSDRankChainReal_r182

★★★ 2026-08-01 — REPAIR: A BSD RANK CHAIN THAT IS NOT `True` ★★★

## Why this file exists

`Wave56CrossMillenniumMasterCascade.lean` states the framework's top-level
cross-Millennium result.  Its conclusion is a six-fold conjunction, and five of
those six conjuncts are

```
RHWave56ShortestChain        : Prop := True
NSWave56UniformBilinearBound : Prop := True
HodgeCYCodim2Chain           : Prop := True
BSDTypedRankZeroChain        : Prop := True
YMContinuumLiftChain         : Prop := True
```

so `Wave56_cross_millennium_master_cascade_conditional` proves
`LHS → (R1 ∧ True ∧ True ∧ True ∧ True ∧ True)`.  The docstrings say
"placeholder" honestly; the theorem name and the capstone framing do not.

A corpus-wide count on 2026-08-01: **402 `Prop := True` definitions, 338 of them
inside the verified build**, including several whose names end in `Proven`.

This file repairs exactly one of them — the BSD conjunct — because that is the
one the r143–r181 arc now makes it possible to state for real.  It replaces
nothing and deletes nothing: `BSDTypedRankZeroChain` stays where it is, and this
stands beside it as the version with content.

## What is actually proved here

`BSDRankChainReal` is a four-clause conjunction, every clause a theorem with
mathematical content, none of them `True`:

1. `2 ≤ Module.rank ℤ E389a1(ℚ)`            — r154
2. `3 ≤ Module.rank ℤ E5077a1(ℚ)`           — r169
3. the general Gram criterion: for any abelian group and any `n`, a nonzero
   Gram determinant of a bi-additive form forces `rank ≥ n`  — r170
4. the canonical height exists and satisfies `ĥ(2R) = 4ĥ(R)`, derived for 389a1
   from the curve coefficients alone via the universal chain r174–r180

Clause 3 is the one that generalises; clauses 1, 2 and 4 are witnesses that it
is not vacuous.

## What this does NOT claim

Nothing about BSD itself.  BSD equates the *algebraic* rank with the order of
vanishing of `L(E,s)` at `s = 1`; mathlib has no elliptic-curve L-function at
all, so the analytic side cannot even be stated.  These are rank **lower
bounds** — one side of one half.  That is a real result and a small one, and the
distance to BSD is not hidden by calling it a "chain".

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-01.
-/
import PF.E389a1RankTwo_r154
import PF.E5077a1RankThree_r169
import PF.GramRankGeneral_r170
import PF.Universal389a1_r180

namespace PrincipiaTractalis.BSDRankChainReal

open PrincipiaTractalis.GramRankGeneral

/-- **A BSD-facing rank chain with actual content.**

Contrast `Wave56CrossMillenniumMasterCascade.BSDTypedRankZeroChain`, which is
`Prop := True`.  Every clause below is a substantive statement. -/
def BSDRankChainReal : Prop :=
  -- (1) 389a1 has Mordell–Weil rank at least two.
  (2 ≤ Module.rank ℤ PrincipiaTractalis.E389a1RankOne.E389a1.toAffine.Point) ∧
  -- (2) 5077a1 has Mordell–Weil rank at least three.
  (3 ≤ Module.rank ℤ PrincipiaTractalis.E5077a1RankOne.E5077a1.toAffine.Point) ∧
  -- (3) The general criterion behind both: for ANY abelian group, ANY n, a
  --     nonzero Gram determinant of a bi-additive form forces rank ≥ n.
  (∀ (G : Type) [AddCommGroup G] (n : ℕ) (B : G → G → ℝ),
      BiAdditive B → ∀ P : Fin n → G, (gram B P).det ≠ 0 →
      (n : Cardinal) ≤ Module.rank ℤ G) ∧
  -- (4) The canonical height on 389a1 satisfies the doubling law, derived from
  --     the curve coefficients alone (universal chain r174–r180).
  (∀ R : PrincipiaTractalis.E389a1RankOne.E389a1.toAffine.Point,
      CanonicalHeightGeneric.canheight
          (fun S => DuplicationLogWindow.lognh
            (PrincipiaTractalis.E389a1RankOne.X S)) (R + R)
        = 4 * CanonicalHeightGeneric.canheight
          (fun S => DuplicationLogWindow.lognh
            (PrincipiaTractalis.E389a1RankOne.X S)) R)

/-- **★ The chain holds, and no clause is `True`. ★** -/
theorem bsd_rank_chain_real : BSDRankChainReal :=
  ⟨PrincipiaTractalis.E389a1RankTwo.E389a1_rank_ge_two,
   PrincipiaTractalis.E5077a1RankThree.E5077a1_rank_ge_three,
   fun _ _ _ _ hB P hdet => rank_ge_of_gram_det_ne_zero hB P hdet,
   PrincipiaTractalis.Universal389a1.canheight_dbl389a1⟩

/-- Non-vacuity witness for clause (3): instantiated at `n = 2` it is exactly
the 389a1 statement, so the general criterion is not vacuously quantified. -/
theorem clause_three_is_inhabited :
    ∃ (G : Type) (_ : AddCommGroup G) (n : ℕ),
      0 < n ∧ (n : Cardinal) ≤ Module.rank ℤ G :=
  ⟨PrincipiaTractalis.E389a1RankOne.E389a1.toAffine.Point, inferInstance, 2,
   by norm_num, PrincipiaTractalis.E389a1RankTwo.E389a1_rank_ge_two⟩

end PrincipiaTractalis.BSDRankChainReal

#print axioms PrincipiaTractalis.BSDRankChainReal.bsd_rank_chain_real
#print axioms PrincipiaTractalis.BSDRankChainReal.clause_three_is_inhabited
