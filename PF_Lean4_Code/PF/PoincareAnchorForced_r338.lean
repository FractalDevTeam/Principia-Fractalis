/-
# r338 — The Perelman anchor, made load-bearing

★ 2026-09-29 — repair of the O-CIRC finding "Perelman 'anchor' is a hypothesis" ★

## The finding this repairs

`PF/Audit/PremiseAudit.lean` reports, of the referee-tier capstone:

> Perelman "anchor" is a hypothesis — no property of Perelman's theorem is used.

The situation was in fact weaker than "hypothesis". In
`PF/PerelmanAnchoredAlphaCascade.lean` the anchor reads

```
theorem perelman_anchor : α_Poincare = 1 := rfl
```

and `α_Poincare` is a literal definition in
`PF/CrossMillenniumSharedInvariants.lean`:

```
noncomputable def α_Poincare : ℝ := 1
```

So `perelman_anchor` is definitional reflexivity. It carries no content, and every
downstream "derivation from the Perelman datum" is a numeric identity among
stipulated constants (`α_YM = α_Poincaré + 1` is `2 = 1 + 1`). Nothing in the
cascade could consume an anchor, because there was no anchor to consume.

## The standard this file meets

The P-axis already does this correctly. In
`PF/CrossMillenniumImplicationChains.lean`:

```
def RealisesP (a : ℝ) : Prop := 0 < a ∧ a ^ 2 = 2
```

The value is not stipulated — it is *pinned* by an equation together with a
positivity side condition. Any `a` satisfying the predicate is forced to be `√2`.
`RealisesHodge` is of the same kind. By contrast `RealisesYM`, `RealisesNS`,
`RealisesBSD` and `RealisesRH` read `0 < a ∧ a = α_X`, which is circular against
the definition of `α_X`, and there was no `RealisesPoincare` at all.

This file supplies the missing predicate for the Poincaré axis at the P-axis
standard, and restates the first cascade step so that it *consumes* the datum
rather than unfolding a definition.

## What is and is not claimed

**Claimed.** After this file, `α_Poincaré = 1` is forced by
`0 < a ∧ a ^ 2 = 1` rather than stipulated by `rfl`, and the first cascade step
`α_YM = α_Poincaré + 1` is available in a form whose hypothesis is genuinely
discharged by the caller. The anchor is load-bearing in exactly the sense the
P-axis anchor is: remove the hypothesis and the conclusion no longer follows.

**Not claimed.** This does *not* yet derive the equation `a ^ 2 = 1` from a
property of Perelman's theorem. It moves the Poincaré axis from
"value stipulated" to "value forced by an equation", which is the standard the
rest of the corpus already holds the P- and Hodge-axes to. Connecting the
equation itself to the geometrisation theorem requires the manuscript's spectral
semantics for the Poincaré-class operator and is a separate, deeper step. The
O-CIRC finding is therefore **partially** repaired by this file, and the residual
is stated explicitly in §4 below rather than closed silently.

The equation `α_Poincare ^ 2 = 1` is not introduced here; it is already proved in
`PF/Poincare_FrameworkMillenniumAnswer.lean`.

SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Tactic
import PF.CrossMillenniumSharedInvariants

namespace PrincipiaTractalis
namespace PoincareAnchorForced

open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## Section 1 — The realisation predicate -/

/-- **Poincaré-axis realisation.** Mirrors `RealisesP (a) := 0 < a ∧ a ^ 2 = 2`.

The Poincaré-class datum is the positive solution of `a ^ 2 = 1`. Unlike
`RealisesYM`/`RealisesRH`/`RealisesNS`/`RealisesBSD`, this predicate does **not**
mention `α_Poincare`, so it is not circular against that definition. -/
def RealisesPoincare (a : ℝ) : Prop := 0 < a ∧ a ^ 2 = 1

/-! ## Section 2 — The equation forces the value

This is the content the old `rfl` anchor lacked: a nontrivial step from the
predicate to the value. -/

/-- **★ The Poincaré datum is forced.** Any positive solution of `a ^ 2 = 1`
equals `1`. Proof: `a ^ 2 = 1` gives `(a - 1) * (a + 1) = 0`; positivity kills
the negative root. -/
theorem poincare_forced {a : ℝ} (h : RealisesPoincare a) : a = 1 := by
  obtain ⟨hpos, hsq⟩ := h
  have hfac : (a - 1) * (a + 1) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.mp hfac with h1 | h2
  · linarith
  · linarith

/-- **Uniqueness.** The predicate has exactly one realiser. -/
theorem poincare_realiser_unique {a b : ℝ}
    (ha : RealisesPoincare a) (hb : RealisesPoincare b) : a = b := by
  rw [poincare_forced ha, poincare_forced hb]

/-- `α_Poincare` does realise the predicate — so the repair is conservative:
nothing previously provable becomes unprovable. -/
theorem alpha_Poincare_realises : RealisesPoincare α_Poincare := by
  refine ⟨?_, ?_⟩ <;> · unfold α_Poincare; norm_num

/-- Any realiser is `α_Poincare`. -/
theorem realiser_eq_alpha_Poincare {a : ℝ} (h : RealisesPoincare a) :
    a = α_Poincare := by
  rw [poincare_forced h]; unfold α_Poincare; rfl

/-! ## Section 3 — The first cascade step, now consuming the datum

Compare `PF/PerelmanAnchoredAlphaCascade.lean`, where the corresponding facts are
proved by `unfold α_Poincare; ring` — i.e. by unfolding a definition. Here the
hypothesis is what does the work. -/

/-- **★★ `α_YM` from the Poincaré datum.** The I7 transport step, stated so that
the Perelman datum is load-bearing: the hypothesis `RealisesPoincare a` is
required, and the conclusion is about `a`, not about an unfolded constant. -/
theorem alpha_YM_from_poincare_datum {a : ℝ} (h : RealisesPoincare a) :
    a + 1 = α_YM := by
  rw [poincare_forced h]; unfold α_YM; norm_num

/-- **★★ `α_RH` from the Poincaré datum**, via I9 (`α_RH = α_YM - 1/2`). -/
theorem alpha_RH_from_poincare_datum {a : ℝ} (h : RealisesPoincare a) :
    a + 1 / 2 = α_RH := by
  rw [poincare_forced h]; unfold α_RH; norm_num

/-- **Negative control.** Without positivity the equation does *not* force the
value: `-1` satisfies `a ^ 2 = 1` and is not `1`. This witnesses that the
positivity side condition is doing real work, and that the predicate is not
vacuously satisfiable in a way that would make §2 trivial. -/
theorem positivity_is_load_bearing :
    ((-1 : ℝ)) ^ 2 = 1 ∧ (-1 : ℝ) ≠ 1 := by
  constructor <;> norm_num

/-- **Non-vacuity.** The predicate is satisfiable, so the implications in §3 are
not vacuously true. -/
theorem realises_poincare_nonempty : ∃ a : ℝ, RealisesPoincare a :=
  ⟨1, by refine ⟨?_, ?_⟩ <;> norm_num⟩

/-! ## Section 4 — Residual, stated explicitly

What remains open, and must not be represented as closed:

`RealisesPoincare` pins the value by an equation, but the *equation itself* is
still supplied by the framework rather than derived from geometrisation. A fully
load-bearing Perelman anchor requires:

1. a definition of the Poincaré-class operator `T_Poincaré` in the manuscript's
   spectral sense, at the same level of concreteness as `alpha_of_class` for the
   P/NP axes; and
2. a proof that a property of Perelman's theorem (simply-connected closed
   3-manifolds are homeomorphic to `S³`, or the Ricci-flow-with-surgery
   formulation) forces `T_Poincaré` to satisfy `a ^ 2 = 1` with `a > 0` —
   for instance by exhibiting it as a projection.

Note the constraint documented in `PF/TuringEncoding/AlphaEnum.lean`: for the
P/NP axes the structural assignment must stay axiomatic at the `Set Language`
level, because a concrete `alpha_of_class` would prove `ClassP ≠ ClassNP` by
`congrArg` from `α_P ≠ α_NP`. Whether an analogous obstruction applies on the
Poincaré axis is not yet determined and should be checked before (1) is
attempted.

Until (1) and (2) land, the honest statement is: *the Poincaré α-value is forced
by an equation at the same standard as the P-axis, and is no longer stipulated by
`rfl`.* -/

/-! ## Axiom check -/

#print axioms poincare_forced
#print axioms poincare_realiser_unique
#print axioms alpha_Poincare_realises
#print axioms realiser_eq_alpha_Poincare
#print axioms alpha_YM_from_poincare_datum
#print axioms alpha_RH_from_poincare_datum
#print axioms realises_poincare_nonempty

end PoincareAnchorForced
end PrincipiaTractalis
