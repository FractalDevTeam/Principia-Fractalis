/-
# r340 — The Navier–Stokes anchor, made load-bearing from H₃ exponent data

★ 2026-09-29 — the SECOND anchor grounded in the same Coxeter data as the first ★

## Why this file exists

`PF/PoincareAlphaFromH3CoxeterHalfArg.lean` grounded the first anchor:

    λ_Poincaré = π / h(H₃) = π/10 ,  α = π/(10·λ)  ⟹  α_Poincaré = 1 .

The second anchor had no such treatment. In
`PF/CrossMillenniumImplicationChains.lean` the NS realisation predicate is

    def RealisesNS (a : ℝ) : Prop := 0 < a ∧ a = α_NS

which is circular against `noncomputable def α_NS : ℝ := 3 * Real.pi / 2` —
it says "a is the NS α-value exactly when a equals the NS α-value". No
equation forces anything.

## The observation this file formalises

`PF/SpectralIsolationSubstrateDischarge.lean` records the substrate λ-skeleton
entry for the NS axis as

    λ_9 = 1/15        (from α_NS = 3π/2)

— note the parenthetical: the λ is obtained *from* the α, the wrong direction for
an anchor. But `15` is not a free constant. It is the **sum of the H₃ exponents**,
and `PF/H3CoxeterOrigin.lean` proves that sum rather than stipulating it:

    H3_exponents = [1, 5, 9]
    H3_exponent_sum_eq : List.sum H3_exponents = H3_exponent_sum   -- = 15, PROVED

Running the universal coupling forward from `λ = 1/Σ(H₃ exponents)` gives

    α = π / (10 · (1/15)) = 15π/10 = 3π/2 = α_NS .

So the two settled anchors come from the same Coxeter datum: the Poincaré axis
from the **Coxeter number** h(H₃) = 10, the NS axis from the **exponent sum**
Σ{1,5,9} = 15.

## What is and is not claimed

**Claimed.** α_NS = 3π/2 follows from the universal coupling together with
`λ_NS = 1/Σ(H₃ exponents)`, with the exponent sum computed from the exponent list
rather than asserted. The NS anchor is now forced by an equation in the same sense
the P-axis is, rather than stipulated by definition. §2 also supplies the
non-circular realisation predicate that `RealisesNS` lacked.

**Not claimed.**

1. That `λ_NS = 1/Σ(H₃ exponents)` is derived from the substrate operator. It is
   supplied here as a hypothesis, exactly as the H₃ identification is supplied as
   a hypothesis on the Poincaré axis. The substrate-operator origin is open on
   both axes — see `PF/H3CoxeterOrigin.lean`, which states plainly that it does
   not prove the framework's H_α operator inherits the H₃ Coxeter structure.
2. That the exponent *list* `[1, 5, 9]` is derived. It is stipulated. It is the
   correct exponent list for the icosahedral Coxeter group H₃ — standard
   mathematics — but it is entered as data, not computed from the Coxeter diagram.
   mathlib carries Coxeter-group theory, so computing it is a bounded, concrete
   improvement rather than open research.
3. Anything about the Navier–Stokes equations themselves. The external NS/Euler
   result is what makes this axis a *settled* anchor; no property of it is
   consumed here. That gap is the same one the O-CIRC audit records for Perelman.

What this buys: both anchors now rest on one visible datum — the H₃ exponent
system — instead of two unrelated stipulated reals.

SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Tactic
import PF.H3CoxeterOrigin

namespace PrincipiaTractalis
namespace NSAlphaFromH3ExponentSum

open PrincipiaFractalis.H3CoxeterOrigin

/-! ## §1 — The exponent-sum λ parameter -/

/-- **The NS λ-parameter as the reciprocal H₃ exponent sum.**

Defined *through* `H3_exponent_sum`, not stipulated as `1/15`. Its numerical value
is a theorem below, and that theorem bottoms out in `H3_exponent_sum_eq`, which
computes `List.sum [1,5,9]`. -/
noncomputable def H3_exponent_sum_reciprocal : ℝ :=
  1 / (H3_exponent_sum : ℝ)

/-- **`1/Σ(H₃ exponents) = 1/15`**, from the computed exponent sum. -/
theorem H3_exponent_sum_reciprocal_eq_one_fifteenth :
    H3_exponent_sum_reciprocal = 1 / 15 := by
  unfold H3_exponent_sum_reciprocal
  have h : (H3_exponent_sum : ℝ) = 15 := by
    unfold H3_exponent_sum; norm_num
  rw [h]

/-- The exponent sum really is computed from the exponent list, not asserted:
`1 + 5 + 9 = 15`. Re-exported so this file's chain is self-contained. -/
theorem exponent_sum_is_computed : List.sum H3_exponents = H3_exponent_sum :=
  H3_exponent_sum_eq

/-! ## §2 — The realisation predicate `RealisesNS` should have had

Compare `RealisesP (a) := 0 < a ∧ a ^ 2 = 2`, which forces `√2`. The existing
`RealisesNS (a) := 0 < a ∧ a = α_NS` forces nothing. This one does not mention
`α_NS`, so it is not circular. -/

/-- **NS-axis realisation.** The positive solution of `2a = 3π`. -/
def RealisesNS_forced (a : ℝ) : Prop := 0 < a ∧ 2 * a = 3 * Real.pi

/-- **The equation forces the value.** -/
theorem NS_forced {a : ℝ} (h : RealisesNS_forced a) : a = 3 * Real.pi / 2 := by
  obtain ⟨_, heq⟩ := h
  linarith

/-- Uniqueness of the realiser. -/
theorem NS_realiser_unique {a b : ℝ}
    (ha : RealisesNS_forced a) (hb : RealisesNS_forced b) : a = b := by
  rw [NS_forced ha, NS_forced hb]

/-- Non-vacuity: the predicate is satisfiable, so §2 is not vacuously true. -/
theorem RealisesNS_forced_nonvacuous : ∃ a : ℝ, RealisesNS_forced a := by
  refine ⟨3 * Real.pi / 2, ?_, ?_⟩
  · positivity
  · ring

/-! ## §3 — ★★★ The NS anchor from H₃ exponent data ★★★ -/

/-- **★★★ `alpha_NS_from_H3_exponent_sum` ★★★**

For any real `aNS` satisfying the universal coupling with the reciprocal H₃
exponent sum as its λ-parameter, `aNS = 3π/2`.

The proof uses only the computed exponent sum and field arithmetic. No reference
to `α_NS`, no reference to the substrate skeleton, and no `rfl` against a
stipulated constant.

Note that `π ≠ 0` is *not* needed: the division is by `10 · (1/15) = 2/3`, a
nonzero rational, not by `π`. -/
theorem alpha_NS_from_H3_exponent_sum
    (aNS : ℝ)
    (h_uc : aNS = Real.pi / (10 * H3_exponent_sum_reciprocal)) :
    aNS = 3 * Real.pi / 2 := by
  rw [h_uc, H3_exponent_sum_reciprocal_eq_one_fifteenth]
  ring

/-- **The forced form.** The H₃ coupling value also satisfies the §2 predicate,
so the two routes to the NS anchor agree. -/
theorem H3_coupling_realises_NS :
    RealisesNS_forced (Real.pi / (10 * H3_exponent_sum_reciprocal)) := by
  have hval : Real.pi / (10 * H3_exponent_sum_reciprocal) = 3 * Real.pi / 2 :=
    alpha_NS_from_H3_exponent_sum _ rfl
  rw [hval]
  refine ⟨by positivity, by ring⟩

/-! ## §4 — Both anchors, one datum

The point of this file. The Poincaré axis uses the H₃ **Coxeter number**; the NS
axis uses the H₃ **exponent sum**. Same root system, two invariants of it. -/

/-- **Both anchors from the H₃ exponent system.**

`h(H₃) = 10` gives the Poincaré λ-parameter `π/10` and hence `α = 1`;
`Σ{1,5,9} = 15` gives the NS λ-parameter `1/15` and hence `α = 3π/2`. -/
theorem both_anchors_from_H3_data :
    (H3_Coxeter_number : ℝ) = 10 ∧
    List.sum H3_exponents = H3_exponent_sum ∧
    Real.pi / (10 * (Real.pi / (H3_Coxeter_number : ℝ))) = 1 ∧
    Real.pi / (10 * H3_exponent_sum_reciprocal) = 3 * Real.pi / 2 := by
  have hc : (H3_Coxeter_number : ℝ) = 10 := by unfold H3_Coxeter_number; norm_num
  refine ⟨hc, H3_exponent_sum_eq, ?_, alpha_NS_from_H3_exponent_sum _ rfl⟩
  rw [hc]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ## §5 — Axiom check -/

#print axioms H3_exponent_sum_reciprocal_eq_one_fifteenth
#print axioms exponent_sum_is_computed
#print axioms NS_forced
#print axioms NS_realiser_unique
#print axioms RealisesNS_forced_nonvacuous
#print axioms alpha_NS_from_H3_exponent_sum
#print axioms H3_coupling_realises_NS
#print axioms both_anchors_from_H3_data

end NSAlphaFromH3ExponentSum
end PrincipiaTractalis
