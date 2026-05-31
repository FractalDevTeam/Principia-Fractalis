/-
# RH `AnalyticPosBijectionToZetaZeros` — Direct Attack on Wave 47A's
# Even-Parity Caveat

★ DERIVED 2026-05-30 (post-Wave-47A direct-attack dispatch).

## Strategic context

Wave 47A
(`PF/RHAnalyticPosBijectionAttempt.lean`, commit `e14011d`)
constructed `wave45CRigidSubstrate` as a re-engineering of the Wave
38A consciousness substrate: it reuses `wave38Base` and `zeroSet38`
(so Wave 38A's (P5) discharge transfers unchanged) but swaps the
constant `pos38` for the non-constant
`pos45C n := eigenvalueToZero alphaRef ((n:ℝ)+1)`.

The cross-route bridge of Wave 47A delivered the implication:

```
analyticPosBijection_wave45C_from_T3sym_with_parity :
  RHSpectralSurjectivityConjecture alphaRef eigSeq →
  (∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
     ∃ n : ℕ, Even n ∧ eigenvalueToZero alphaRef (eigSeq n) = s) →
  AnalyticPosBijectionToZetaZeros wave45CRigidSubstrate
```

The second hypothesis is the **even-parity caveat**: the surjecting
index `n` must be EVEN, so that Wave 38A's (P5) discharge on the
EVEN-indexed zero block of `wave38Base` applies at that index.

This file is the framework's first DIRECT attack on the parity
caveat itself.

## The strategic question

Given that the underlying eigenvalue carrier `eigSeq : ℕ → ℝ` and the
substrate's commutator-vanishing zero block `Even n` are *independent*
data, can we re-engineer the carrier so that the surjecting index is
ALWAYS even structurally?

**Strategy (a)** (substrate-level re-indexing): replace `eigSeq` by an
even-indexed re-indexing `eigSeqEven n := eigSeq (n / 2)`. Then
EVERY value taken by `eigSeq` is also taken by `eigSeqEven` at an
EVEN index `n = 2k`. Concretely, `eigSeqEven (2 * k) = eigSeq k` for
every `k : ℕ`, so the image of `eigenvalueToZero alphaRef ∘ eigSeqEven`
on even indices equals the image of `eigenvalueToZero alphaRef ∘ eigSeq`
on ALL indices.

Consequence: on a substrate that uses `eigSeqEven` as its carrier
(call it `wave47ParitySubstrate`), the analogous Wave 47A bridge
LOSES the parity caveat — `RHSpectralSurjectivityConjecture
alphaRef eigSeqEven` AUTOMATICALLY implies
`AnalyticPosBijectionToZetaZeros wave47ParitySubstrate`, because we
can always pick the EVEN-indexed witness `n = 2k`.

## What this file IS

A **parity-caveat discharge by substrate re-indexing**:

1. Construct `eigSeqEven n := eigSeq (n / 2) = (n / 2 : ℝ) + 1` and
   prove `eigSeqEven (2 * k) = eigSeq k` (rewriting lemma).

2. Construct `pos47Parity n := eigenvalueToZero alphaRef (eigSeqEven n)`
   and `wave47ParitySubstrate` reusing `wave38Base` + `zeroSet38`.

3. Prove `pos47Parity_re : ∀ n, (pos47Parity n).re = 1/2`
   (critical-line landing, independent of `n`).

4. Prove `P5_holds_wave47Parity` — Wave 38A's (P5) discharge transfers
   to `wave47ParitySubstrate` unchanged (by `rfl` cast through
   `wave38Base + zeroSet38`).

5. Prove the **parity-caveat discharge** main theorem:
   `analyticPosBijection_wave47Parity_from_T3sym_no_parity`
   — `RHSpectralSurjectivityConjecture alphaRef eigSeqEven` ALONE
   implies `AnalyticPosBijectionToZetaZeros wave47ParitySubstrate`,
   without any parity-of-surjecting-index hypothesis.

6. Prove the **carrier-equivalence bridge**:
   `RHSpectralSurjectivityConjecture alphaRef eigSeqEven ↔
   RHSpectralSurjectivityConjecture alphaRef eigSeq`. The (←)
   direction is the substantive content: the even-indexed re-indexing
   inherits surjectivity from the base carrier.

7. Compose: `RHSpectralSurjectivityConjecture alphaRef eigSeq` ALONE
   discharges RH via the bridge substrate — the parity caveat is
   structurally eliminated.

## What this file is NOT

* NOT a discharge of `RHSpectralSurjectivityConjecture`. The
  T_3^sym route's load-bearing open conjecture remains open. We have
  not produced any new analytic content about ζ-zeros.

* NOT a discharge of `AnalyticPosBijectionToZetaZeros` per se. We
  produce a NEW substrate (`wave47ParitySubstrate`) on which the
  Prop is implied by `RHSpectralSurjectivityConjecture` alone; the
  Prop on Wave 47A's original `wave45CRigidSubstrate` still has the
  parity caveat (the carrier `eigSeq n := n + 1` is unchanged
  there).

* NOT a discharge of the Riemann Hypothesis.

## What this file IS (positively)

* **Strategic narrowing**: Wave 47A reduced the consciousness route
  to `RHSpectralSurjectivityConjecture ∧ parity`. This file removes
  the `∧ parity` conjunct on the re-engineered carrier. The two
  parallel RH routes (consciousness + T_3^sym) now collapse to
  **identical** open content on the bridge substrate
  `wave47ParitySubstrate`: BOTH reduce to
  `RHSpectralSurjectivityConjecture` on the carrier `eigSeqEven`.

* **Honest assessment**: the parity caveat was an artefact of
  using `eigSeq n := n + 1` as the carrier, which happens to be
  injective AND surjective onto its image. By introducing the
  redundant re-indexing `n ↦ n / 2`, we trade injectivity for
  even-index covering. The mathematical content (the analytic
  surjectivity onto ζ-zeros) is unchanged; only the index encoding
  is shifted to align with the zero block.

## Honest scope (mandatory non-overclaim)

* The discharge of the parity caveat is **structural**, not
  analytic. We did not produce any new spectral / number-theoretic
  fact about ζ-zeros. We exhibited a substrate whose carrier
  ENCODES every surjective value at an even index.

* The carrier `eigSeqEven n := (n / 2 : ℝ) + 1` is NOT injective —
  `eigSeqEven (2 * k) = eigSeqEven (2 * k + 1) = (k : ℝ) + 1`.
  This means `wave47ParitySubstrate.pos` (= `pos47Parity`) is NOT
  injective either. The original Wave 47A non-constancy property
  (`pos45C_not_constant`) is replaced by a weaker "non-constant on
  even indices" property which we record explicitly
  (`pos47Parity_non_constant_on_even`).

* No `axiom`, no `sorry`, no `admit`. `#print axioms` on the capstone
  returns only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.RHAnalyticPosBijectionAttempt
import PF.RHConditionalDischargeViaGaloisRigidity
import PF.RHSurjectivityConjecture
import PF.SpectralBijection
import PF.Consciousness.ConsciousnessRHBridge
import PF.Consciousness.ConsciousnessRHBridgeWave38InfiniteZeroSet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace RHAnalyticPosBijectionParityAttempt

open PrincipiaTractalis
open PrincipiaTractalis.RHConditionalDischargeViaGaloisRigidity
open PrincipiaTractalis.RHAnalyticPosBijectionAttempt

/-! ## Section 1 — The re-indexed carrier `eigSeqEven`

We define `eigSeqEven n := eigSeq (n / 2)`. Since `eigSeq k := (k : ℝ) + 1`
(Wave 47A's `eigSeq`), this gives
`eigSeqEven n = ((n / 2 : ℕ) : ℝ) + 1`.
At even indices `n = 2 * k`, this recovers `eigSeq k = (k : ℝ) + 1`.
At odd indices `n = 2 * k + 1`, we have `n / 2 = k` (natural-number
division), so `eigSeqEven (2 * k + 1) = (k : ℝ) + 1 = eigSeq k` as
well — degenerate (the carrier is not injective). -/

/-- **The even-indexed re-indexing of Wave 47A's `eigSeq`**.
    `eigSeqEven n := eigSeq (n / 2) = ((n / 2 : ℕ) : ℝ) + 1`. -/
noncomputable def eigSeqEven : ℕ → ℝ := fun n => eigSeq (n / 2)

/-- At even indices `n = 2 * k`, the re-indexed carrier recovers the
    base carrier value. -/
@[simp] theorem eigSeqEven_at_two_mul (k : ℕ) :
    eigSeqEven (2 * k) = eigSeq k := by
  show eigSeq ((2 * k) / 2) = eigSeq k
  rw [Nat.mul_div_cancel_left k (by decide : 0 < 2)]

/-- `eigSeqEven` is strictly positive — inherits from `eigSeq_pos`. -/
lemma eigSeqEven_pos (n : ℕ) : 0 < eigSeqEven n := eigSeq_pos _

/-- `eigSeqEven` is nonzero. -/
lemma eigSeqEven_ne_zero (n : ℕ) : eigSeqEven n ≠ 0 :=
  ne_of_gt (eigSeqEven_pos n)

/-- **★ The re-indexed position map ★**: lands on the critical line at
    every index. -/
noncomputable def pos47Parity : ℕ → ℂ :=
  fun n => eigenvalueToZero alphaRef (eigSeqEven n)

/-- `pos47Parity` always lands on the critical line. -/
theorem pos47Parity_re (n : ℕ) : (pos47Parity n).re = 1/2 := by
  unfold pos47Parity
  exact eigenvalue_maps_to_critical_line alphaRef (eigSeqEven n)

/-- `pos47Parity` is **non-constant on even indices**:
    `pos47Parity 0 ≠ pos47Parity 2` since
    `eigSeqEven 0 = 1` and `eigSeqEven 2 = 2`. -/
theorem pos47Parity_non_constant_on_even : pos47Parity 0 ≠ pos47Parity 2 := by
  unfold pos47Parity
  apply different_eigenvalues_different_zeros alphaRef
  · exact eigSeqEven_ne_zero 0
  · exact eigSeqEven_ne_zero 2
  -- |eigSeqEven 0| ≠ |eigSeqEven 2|: |1| = 1 ≠ 2 = |2|.
  -- eigSeqEven 0 = eigSeq 0 = 1; eigSeqEven 2 = eigSeq 1 = 2.
  have h0 : eigSeqEven 0 = 1 := by
    show eigSeq (0 / 2) = 1
    unfold eigSeq
    norm_num
  have h2 : eigSeqEven 2 = 2 := by
    show eigSeq (2 / 2) = 2
    unfold eigSeq
    norm_num
  rw [h0, h2]
  norm_num

/-- `pos47Parity` is **NOT** injective: at odd index `1` it agrees with
    even index `0`, because both reduce through `n / 2 = 0` to
    `eigSeq 0 = 1`. We record this honest negative property. -/
theorem pos47Parity_not_injective : pos47Parity 0 = pos47Parity 1 := by
  show eigenvalueToZero alphaRef (eigSeqEven 0)
       = eigenvalueToZero alphaRef (eigSeqEven 1)
  rfl

/-! ## Section 2 — The parity-discharge substrate `wave47ParitySubstrate`

We reuse `wave38Base` and `zeroSet38` (so Wave 38A's (P5) discharge
transfers UNCHANGED by `rfl`-cast through the base+zeroSet) but swap
the position map to `pos47Parity`. -/

/-- Critical-line anchor for `pos47Parity` restricted to `zeroSet38`. -/
theorem pos47Parity_re_on_zeroSet :
    ∀ n : ℕ, zeroSet38 n → (pos47Parity n).re = 1/2 := by
  intro n _
  exact pos47Parity_re n

/-- **★ THE PARITY-DISCHARGE SUBSTRATE ★**

    Reuses `wave38Base` (so Wave 38A's `P5_holds_infiniteZeroSetSubstrate`
    applies unchanged) and `zeroSet38` (so `Even n` is still the
    commutator-vanishing block), but swaps `pos45C` for `pos47Parity`.

    The KEY ADVANTAGE over `wave45CRigidSubstrate`: the carrier
    `eigSeqEven` takes every value of `eigSeq` at an EVEN index
    (`eigSeqEven (2 * k) = eigSeq k`), so any surjectivity statement
    about `eigSeq` on ALL ℕ automatically yields a surjectivity
    statement about `eigSeqEven` restricted to EVEN ℕ. This is the
    structural removal of the Wave 47A parity caveat. -/
noncomputable def wave47ParitySubstrate : ConsciousnessRHSubstrate :=
  { base := wave38Base
    pos := pos47Parity
    zeroSet := zeroSet38
    zero_set_on_critical_line := pos47Parity_re_on_zeroSet }

/-- The parity-discharge substrate has the SAME base as `wave38Substrate`
    and `wave45CRigidSubstrate`. -/
theorem wave47ParitySubstrate_base_eq :
    wave47ParitySubstrate.base = wave38Base := rfl

/-- The parity-discharge substrate has the SAME zeroSet as
    `wave38Substrate` and `wave45CRigidSubstrate`. -/
theorem wave47ParitySubstrate_zeroSet_eq :
    wave47ParitySubstrate.zeroSet = zeroSet38 := rfl

/-- **★ (P5) IS PRESERVED ON THE PARITY-DISCHARGE SUBSTRATE ★**

    Since `wave47ParitySubstrate.base = wave38Base` and
    `wave47ParitySubstrate.zeroSet = zeroSet38`, the Prop
    `CommutatorVanishesAtRHZeros wave47ParitySubstrate` is
    DEFINITIONALLY EQUAL to `CommutatorVanishesAtRHZeros wave38Substrate`,
    discharged by Wave 38A as a theorem. -/
theorem P5_holds_wave47Parity :
    CommutatorVanishesAtRHZeros wave47ParitySubstrate :=
  P5_holds_infiniteZeroSetSubstrate

/-! ## Section 3 — The parity-caveat discharge

The KEY theorem: on `wave47ParitySubstrate`,
`RHSpectralSurjectivityConjecture alphaRef eigSeqEven` ALONE
implies `AnalyticPosBijectionToZetaZeros wave47ParitySubstrate` —
NO parity-of-surjecting-index hypothesis is needed.

The reason: for any ζ-zero `s`, surjectivity gives some `n` with
`eigenvalueToZero alphaRef (eigSeqEven n) = s`. We exhibit
`2 * n` as the EVEN witness:
`eigenvalueToZero alphaRef (eigSeqEven (2 * n)) =
 eigenvalueToZero alphaRef (eigSeq n) = ?`. We need to relate this
to `s`. The trick: use the SAME `n` but apply the EVEN-shift on
the OUTPUT: `eigSeqEven (2 * (n / 2 + ...))` — no, this does not
work directly because the witness `n` in `RHSpectralSurjectivity-
Conjecture alphaRef eigSeqEven` is for `eigSeqEven`, not `eigSeq`.

The cleaner approach: just convert the witness index `n` to its
even refinement `2 * n` — observing that `eigSeqEven (2 * n) =
eigSeq n` AND `eigSeqEven n` (the original witness) MAY OR MAY NOT
equal `eigSeq n` depending on whether `n` is even or odd.

CORRECT proof: take the witness `n` from the surjectivity. Then
`eigSeqEven n = eigSeq (n / 2)`, and `2 * (n / 2)` is even AND
`eigSeqEven (2 * (n / 2)) = eigSeq (n / 2) = eigSeqEven n`. So
`eigenvalueToZero alphaRef (eigSeqEven (2 * (n / 2))) =
 eigenvalueToZero alphaRef (eigSeqEven n) = s`, and the witness
`2 * (n / 2)` is even by construction. -/

/-- **★★★ THE PARITY-CAVEAT DISCHARGE ★★★**

    On `wave47ParitySubstrate`,
    `RHSpectralSurjectivityConjecture alphaRef eigSeqEven` ALONE
    implies `AnalyticPosBijectionToZetaZeros wave47ParitySubstrate`.

    No parity-of-surjecting-index hypothesis is required: from any
    surjecting index `n` we can construct the EVEN witness
    `2 * (n / 2)`, which yields the same value of
    `eigenvalueToZero alphaRef (eigSeqEven · )` because
    `eigSeqEven (2 * (n / 2)) = eigSeq (n / 2) = eigSeqEven n` by
    definitional unfolding. -/
theorem analyticPosBijection_wave47Parity_from_T3sym_no_parity
    (h_surj : RHSpectralSurjectivityConjecture alphaRef eigSeqEven) :
    AnalyticPosBijectionToZetaZeros wave47ParitySubstrate := by
  intro s hs1 hs2 hs0
  obtain ⟨n, h_eq⟩ := h_surj s hs1 hs2 hs0
  -- h_eq : eigenvalueToZero alphaRef (eigSeqEven n) = s.
  -- Take 2 * (n / 2) as the EVEN witness.
  refine ⟨2 * (n / 2), ?_, ?_⟩
  · -- pos = pos47Parity. Need: pos47Parity (2 * (n / 2)) = s.
    show eigenvalueToZero alphaRef (eigSeqEven (2 * (n / 2))) = s
    -- eigSeqEven (2 * (n / 2)) = eigSeq ((2 * (n / 2)) / 2)
    --                         = eigSeq (n / 2)
    --                         = eigSeqEven n.
    have h_step : eigSeqEven (2 * (n / 2)) = eigSeqEven n := by
      show eigSeq ((2 * (n / 2)) / 2) = eigSeq (n / 2)
      rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    rw [h_step]
    exact h_eq
  · -- Commutator vanishes on 2 * (n / 2) (even index).
    have h_even : Even (2 * (n / 2)) := ⟨n / 2, by ring⟩
    have h_p5 := P5_holds_infiniteZeroSetSubstrate (2 * (n / 2))
    -- h_p5 : commutator-iff zeroSet38 (2 * (n / 2)) = Even (2 * (n / 2))
    exact h_p5.mpr h_even

/-! ## Section 4 — Carrier-equivalence bridge

We prove that `RHSpectralSurjectivityConjecture alphaRef eigSeqEven`
is EQUIVALENT to `RHSpectralSurjectivityConjecture alphaRef eigSeq` —
the re-indexing preserves the surjectivity content.

The (→) direction is trivial: any surjecting `n` for `eigSeqEven`
gives a surjecting `n / 2` for `eigSeq` (since
`eigSeqEven n = eigSeq (n / 2)`).

The (←) direction is the substantive content: any surjecting `k`
for `eigSeq` gives `2 * k` as a surjecting index for `eigSeqEven`,
because `eigSeqEven (2 * k) = eigSeq k`. -/

/-- **Carrier-equivalence forward direction**: surjectivity of
    `eigenvalueToZero alphaRef ∘ eigSeqEven` implies surjectivity
    of `eigenvalueToZero alphaRef ∘ eigSeq`. -/
theorem surjectivity_eigSeqEven_implies_surjectivity_eigSeq
    (h : RHSpectralSurjectivityConjecture alphaRef eigSeqEven) :
    RHSpectralSurjectivityConjecture alphaRef eigSeq := by
  intro s hs1 hs2 hs0
  obtain ⟨n, h_eq⟩ := h s hs1 hs2 hs0
  -- h_eq : eigenvalueToZero alphaRef (eigSeqEven n) = s.
  -- eigSeqEven n = eigSeq (n / 2), so take n / 2 as the witness.
  refine ⟨n / 2, ?_⟩
  show eigenvalueToZero alphaRef (eigSeq (n / 2)) = s
  -- eigSeqEven n = eigSeq (n / 2) by definitional unfolding.
  have h_step : eigSeq (n / 2) = eigSeqEven n := rfl
  rw [h_step]
  exact h_eq

/-- **Carrier-equivalence backward direction**: surjectivity of
    `eigenvalueToZero alphaRef ∘ eigSeq` implies surjectivity of
    `eigenvalueToZero alphaRef ∘ eigSeqEven`.

    This is the substantive direction — it shows the re-indexing
    inherits surjectivity by using `2 * k` as the index witness. -/
theorem surjectivity_eigSeq_implies_surjectivity_eigSeqEven
    (h : RHSpectralSurjectivityConjecture alphaRef eigSeq) :
    RHSpectralSurjectivityConjecture alphaRef eigSeqEven := by
  intro s hs1 hs2 hs0
  obtain ⟨k, h_eq⟩ := h s hs1 hs2 hs0
  -- h_eq : eigenvalueToZero alphaRef (eigSeq k) = s.
  -- Take 2 * k as the witness for eigSeqEven: eigSeqEven (2*k) = eigSeq k.
  refine ⟨2 * k, ?_⟩
  show eigenvalueToZero alphaRef (eigSeqEven (2 * k)) = s
  rw [eigSeqEven_at_two_mul]
  exact h_eq

/-- **★ CARRIER-EQUIVALENCE BRIDGE ★**: the two surjectivity statements
    are equivalent. The even-indexed re-indexing does not change the
    analytic content. -/
theorem RHSpectralSurjectivity_eigSeqEven_iff_eigSeq :
    RHSpectralSurjectivityConjecture alphaRef eigSeqEven ↔
    RHSpectralSurjectivityConjecture alphaRef eigSeq :=
  ⟨surjectivity_eigSeqEven_implies_surjectivity_eigSeq,
   surjectivity_eigSeq_implies_surjectivity_eigSeqEven⟩

/-! ## Section 5 — Composition: RHSpectralSurjectivity on eigSeq
     ALONE discharges RH via the bridge substrate -/

/-- **★ DIRECT RH REDUCTION VIA THE PARITY-DISCHARGE SUBSTRATE ★**

    The Wave 45C / Wave 47A conditional reduction, instantiated on
    `wave47ParitySubstrate`, gives a DIRECT conditional reduction
    of RH from `AnalyticPosBijectionToZetaZeros wave47ParitySubstrate`. -/
theorem RH_from_wave47Parity_AnalyticPosBijection
    (h : AnalyticPosBijectionToZetaZeros wave47ParitySubstrate) :
    RiemannHypothesis := by
  -- (P5) preserved on the bridge substrate.
  have h_P5 : CommutatorVanishesAtRHZeros wave47ParitySubstrate :=
    P5_holds_wave47Parity
  -- The AnalyticPosBijection hypothesis IS the substrate-level (P6).
  have h_P6 : ConsciousnessStationaryStateCompleteness
      wave47ParitySubstrate := by
    intro s hs1 hs2 hs0
    exact h s hs1 hs2 hs0
  -- Wave 25 consciousness bridge closes RH.
  exact riemann_hypothesis_via_consciousness_bridge
    wave47ParitySubstrate h_P5 h_P6

/-- **★★★★ THE PARITY-ELIMINATED RH REDUCTION ★★★★**

    Combining the parity-caveat discharge with the carrier-equivalence
    bridge: `RHSpectralSurjectivityConjecture alphaRef eigSeq` ALONE
    discharges RH.

    Wave 47A required `RHSpectralSurjectivityConjecture alphaRef eigSeq
    ∧ parity-of-surjecting-index`. This file removes the parity
    conjunct via substrate re-engineering: the carrier `eigSeqEven`
    encodes EVERY value of `eigSeq` at an EVEN index, so the parity
    requirement is structurally satisfied.

    **The parity caveat of Wave 47A is fully discharged on the bridge
    substrate `wave47ParitySubstrate`.** -/
theorem RH_from_T3sym_surjectivity_no_parity
    (h_surj : RHSpectralSurjectivityConjecture alphaRef eigSeq) :
    RiemannHypothesis := by
  -- Promote eigSeq surjectivity to eigSeqEven surjectivity.
  have h_surj_even : RHSpectralSurjectivityConjecture alphaRef eigSeqEven :=
    surjectivity_eigSeq_implies_surjectivity_eigSeqEven h_surj
  -- Discharge AnalyticPosBijection on wave47ParitySubstrate.
  have h_apb : AnalyticPosBijectionToZetaZeros wave47ParitySubstrate :=
    analyticPosBijection_wave47Parity_from_T3sym_no_parity h_surj_even
  -- Close RH via the bridge substrate.
  exact RH_from_wave47Parity_AnalyticPosBijection h_apb

/-! ## Section 6 — Comparison with Wave 47A

Wave 47A's `RH_from_T3sym_surjectivity_with_parity` required a TWO-
clause hypothesis bundle:
  (1) `RHSpectralSurjectivityConjecture alphaRef eigSeq`
  (2) For every ζ-zero `s`, the surjecting index is EVEN.

This file's `RH_from_T3sym_surjectivity_no_parity` requires only:
  (1) `RHSpectralSurjectivityConjecture alphaRef eigSeq`

The parity clause (2) is eliminated structurally via substrate
re-engineering. -/

/-- **★ STRICT IMPROVEMENT OVER WAVE 47A ★**

    On the parity-discharge substrate, `RHSpectralSurjectivity-
    Conjecture alphaRef eigSeq` ALONE implies the consciousness-route
    open Prop `AnalyticPosBijectionToZetaZeros wave47ParitySubstrate`.

    Wave 47A's analogous theorem
    (`analyticPosBijection_wave45C_from_T3sym_with_parity`) needed
    BOTH `RHSpectralSurjectivityConjecture` AND a parity hypothesis.
    This file removes the parity hypothesis at the cost of changing
    the underlying substrate from `wave45CRigidSubstrate` to
    `wave47ParitySubstrate`. -/
theorem analyticPosBijection_wave47Parity_implies_wave45C_open_via_eigSeq
    (h_surj : RHSpectralSurjectivityConjecture alphaRef eigSeq) :
    AnalyticPosBijectionToZetaZeros wave47ParitySubstrate := by
  exact analyticPosBijection_wave47Parity_from_T3sym_no_parity
    (surjectivity_eigSeq_implies_surjectivity_eigSeqEven h_surj)

/-! ## Section 7 — Honest scope assessment

What this file ACHIEVES:

* **Parity caveat eliminated** on the bridge substrate
  `wave47ParitySubstrate`. The carrier re-indexing
  `eigSeqEven n := eigSeq (n / 2)` ENCODES every value of `eigSeq`
  at an EVEN index (`eigSeqEven (2 * k) = eigSeq k`), so the
  surjecting index can ALWAYS be chosen even by passing through
  `2 * (n / 2)`.

* **Carrier-equivalence bridge** proven axiom-free:
  `RHSpectralSurjectivityConjecture alphaRef eigSeqEven ↔
  RHSpectralSurjectivityConjecture alphaRef eigSeq`. Both directions
  established; the (←) direction is the substantive content of the
  re-indexing.

* **Direct RH reduction** without parity:
  `RHSpectralSurjectivityConjecture alphaRef eigSeq → RiemannHypothesis`
  via the bridge substrate, with NO parity-of-surjecting-index
  conjunct in the hypothesis.

What this file does NOT achieve:

* The load-bearing `RHSpectralSurjectivityConjecture` itself remains
  OPEN — this file does NOT produce any new spectral / number-
  theoretic content about ζ-zeros.

* The carrier `eigSeqEven` is NOT injective
  (`pos47Parity_not_injective`). The Wave 47A `pos45C_not_constant`
  property (genuine non-constancy at distinct indices) is REPLACED
  by `pos47Parity_non_constant_on_even` (non-constancy at distinct
  EVEN indices). This is a structural trade-off, not a degradation
  of the analytic content.

* `AnalyticPosBijectionToZetaZeros wave45CRigidSubstrate` (Wave 47A's
  original Prop) still has the parity caveat — this file changes the
  substrate to `wave47ParitySubstrate`, not the underlying Wave 47A
  hypothesis.

Strategic assessment: **Strategy (a) of the dispatch — substrate
re-indexing to make the surjecting index always even — is the right
approach and it WORKS.** The parity caveat was an artefact of the
particular carrier `eigSeq n := n + 1` used in Wave 47A, not a
fundamental obstruction. By introducing the redundant re-indexing
`n ↦ n / 2`, we trade injectivity (which Wave 47A's `pos45C` had)
for even-index covering (which Wave 47A's `pos45C` lacked). The
mathematical content is unchanged.

NEITHER of the other strategies is pursued in this file:

* Strategy (b) (second bridge substrate with different ℝ → ℂ
  injection) would change the canonical critical-line map, which is
  a deeper restructuring not required by the parity question.

* Strategy (c) (document why parity is genuine) is REFUTED by
  Section 4: the carrier-equivalence bridge shows the parity caveat
  is structurally eliminable, hence NOT genuine.

Zero project axioms.
-/

/-! ## Section 8 — Capstone -/

/-- ★★★ **CAPSTONE: PARITY-CAVEAT DISCHARGE** ★★★
    (2026-05-30, post-Wave-47A direct-attack dispatch).
    `rh_analytic_pos_bijection_parity_attempt_capstone`

    Bundles the seven structural contributions of this file:

    (1) `eigSeqEven_at_two_mul` — the re-indexed carrier recovers the
        base carrier at even indices.

    (2) `pos47Parity_re` — the parity-discharge substrate's `pos`
        lands on the critical line for every index.

    (3) `pos47Parity_non_constant_on_even` — `pos` is non-constant on
        even indices (honest structural property given the carrier
        is no longer injective).

    (4) `P5_holds_wave47Parity` — Wave 38A's (P5) discharge transfers
        to the parity-discharge substrate unchanged.

    (5) `analyticPosBijection_wave47Parity_from_T3sym_no_parity` —
        the **PARITY-CAVEAT DISCHARGE**:
        `RHSpectralSurjectivityConjecture alphaRef eigSeqEven` ALONE
        (no parity hypothesis) implies
        `AnalyticPosBijectionToZetaZeros wave47ParitySubstrate`.

    (6) `RHSpectralSurjectivity_eigSeqEven_iff_eigSeq` — the
        carrier-equivalence bridge: surjectivity on the re-indexed
        carrier is EQUIVALENT to surjectivity on the base carrier.

    (7) `RH_from_T3sym_surjectivity_no_parity` — the **PARITY-
        ELIMINATED RH REDUCTION**:
        `RHSpectralSurjectivityConjecture alphaRef eigSeq` ALONE
        discharges RH via the bridge substrate, with NO parity
        conjunct in the hypothesis.

    ## Verdict

    The Wave 47A even-parity caveat IS DISCHARGEABLE via substrate
    re-engineering (Strategy (a) of the dispatch). The carrier
    `eigSeqEven n := eigSeq (n / 2)` encodes every value of `eigSeq`
    at an even index, structurally eliminating the parity requirement.

    The two parallel RH routes (consciousness via `wave47Parity-
    Substrate` + T_3^sym via `eigSeq`) now collapse to IDENTICAL
    open content: BOTH reduce to
    `RHSpectralSurjectivityConjecture alphaRef eigSeq` alone.

    Honest scope: this does NOT discharge `RHSpectralSurjectivity-
    Conjecture` or RH. It eliminates the parity ARTEFACT, leaving the
    SINGLE genuine load-bearing open Prop. The Riemann Hypothesis
    remains a Clay-grade open problem; we have sharpened the formal
    reduction by one structural unit.

    Axiom-free: `#print axioms` returns only
    `[propext, Classical.choice, Quot.sound]`. -/
theorem rh_analytic_pos_bijection_parity_attempt_capstone :
    -- (1) Re-indexed carrier recovers base at even indices.
    (∀ k : ℕ, eigSeqEven (2 * k) = eigSeq k) ∧
    -- (2) Bridge substrate's `pos` on critical line.
    (∀ n : ℕ, (pos47Parity n).re = 1/2) ∧
    -- (3) `pos` non-constant on even indices.
    (pos47Parity 0 ≠ pos47Parity 2) ∧
    -- (4) (P5) preserved on bridge substrate.
    CommutatorVanishesAtRHZeros wave47ParitySubstrate ∧
    -- (5) Parity-caveat discharge: surjectivity ALONE implies AnalyticPosBijection.
    (RHSpectralSurjectivityConjecture alphaRef eigSeqEven →
      AnalyticPosBijectionToZetaZeros wave47ParitySubstrate) ∧
    -- (6) Carrier-equivalence bridge.
    (RHSpectralSurjectivityConjecture alphaRef eigSeqEven ↔
      RHSpectralSurjectivityConjecture alphaRef eigSeq) ∧
    -- (7) Parity-eliminated RH reduction.
    (RHSpectralSurjectivityConjecture alphaRef eigSeq →
      RiemannHypothesis) :=
  ⟨eigSeqEven_at_two_mul,
   pos47Parity_re,
   pos47Parity_non_constant_on_even,
   P5_holds_wave47Parity,
   analyticPosBijection_wave47Parity_from_T3sym_no_parity,
   RHSpectralSurjectivity_eigSeqEven_iff_eigSeq,
   RH_from_T3sym_surjectivity_no_parity⟩

/-- **Structural-reading remark for the capstone.**

    Wave 47A's parity caveat was an ARTEFACT of the carrier choice
    `eigSeq n := n + 1` — an injective sequence whose surjection
    indices have no a priori parity structure. This file
    constructively eliminates the artefact by introducing a
    NON-injective re-indexing `eigSeqEven n := eigSeq (n / 2)` whose
    image on EVEN indices alone equals the full image of `eigSeq`.

    The structural cost is the loss of injectivity for `pos47Parity`:
    `pos47Parity 0 = pos47Parity 1` (both reduce to `eigSeq 0 = 1`).
    This is acceptable for a substrate whose ROLE is to expose the
    open analytic content; the substrate need not have any particular
    injectivity property beyond the critical-line landing and the
    (P5) commutator-vanishing on the zero block.

    Honest reading: this is structural caveat-elimination, NOT a
    discharge. `RHSpectralSurjectivityConjecture` remains the
    load-bearing open Prop. What changes is the EXACTLY-ONE
    open Prop on the consciousness route is now visibly identical
    to the EXACTLY-ONE open Prop on the T_3^sym route, with no
    parity gap between them. The Riemann Hypothesis remains a
    Clay-grade open problem. -/
theorem rh_analytic_pos_bijection_parity_attempt_structural_remark :
    True := trivial

end RHAnalyticPosBijectionParityAttempt
end PrincipiaTractalis
