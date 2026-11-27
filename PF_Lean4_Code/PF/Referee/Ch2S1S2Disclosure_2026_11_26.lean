/-
# S1 and S2 of the ch₂ disambiguation ledger, disclosed in the kernel

## Provenance — this is a finding already made, never landed

`codex/CH2_SEMANTIC_DISAMBIGUATION_LEDGER_2026-09-14.md` (on Acer, branch
`r331b-ch2-disambiguation`) catalogues **seven** distinct objects sharing the
unqualified name `ch_2`, two of which the later 2026-10-05 five-form settlement
does not name:

  * **S1** — `ch_2 (α) := 0.95 + (α − √2)/10`, an affine function of one real
    parameter *with `0.95` baked into the definition*. The ledger's verdict:
    "Target-anchored **definition**. Not a theorem, not a derivation, not a
    topological invariant."
  * **S2** — `SecondChernCharacter`, a `structure` with one field `value : ℝ`
    and a proof `0 ≤ value ≤ 1`. The ledger: "NO bundle, NO connection, NO
    curvature form; NO Chern–Weil construction. **NOT a Chern–Weil
    characteristic class.**"
  * **S7** — the genuine second Chern character. The ledger: "**No Lean file at
    base SHA supplies a bundle-connection-curvature construction.** The Lean
    `SecondChernCharacter` (S2) shares only the name."

Phase B (canonical names) and Phase C (manuscript corrections) were planned in
that ledger and **never merged**: its commits are on `origin` but are not
ancestors of the working branch, and S1, S2 and the S7 absence are all still
live in the import closure today, unchanged (measured 2026-11-26). S7's absence
is the same gap independently measured in
`ChernWeilDegree4SignIndefinite_2026_11_26` --- `F_nabla` and `HermitianBundle`
are still 0 files.

This file does not merge that branch. It turns the ledger's prose verdicts into
theorems in the current tree, using today's pinned degree-4 invariant to make
the S2/S7 separation **provable** rather than asserted. Nothing is renamed and
nothing is withdrawn, exactly as in the other disclosure files.

## The sharp instruments

**S1 is target-anchored, and here is the proof that its headline evaluation
carries no information.** `MillenniumSix.ch_2_at_alpha_P` proves
`ch_2 (√2) = 0.95` and its docstring reads "evaluates to 0.95 at α = √2". But
`evaluation_returns_whatever_constant_is_supplied` shows the *same computation*
returns `c` for **every** `c` — the evaluation is a property of the constant
term, not a fact about `0.95`. (`ch_2_at_alpha_NP` upstream is proved by `rfl`,
which says the same thing more bluntly.)

**S1 is not a bounded or probability-like quantity at all:** `ch_2_surjective`
shows it attains *every* real value, so it cannot be a normalised invariant in
`[0,1]`, and in particular it is not S2.

**S2 is exactly the unit interval.** `secondChernCharacterEquiv` is an
equivalence `SecondChernCharacter ≃ {x : ℝ // 0 ≤ x ∧ x ≤ 1}`. There is nothing
else in it — no bundle, no connection, no curvature — and that is now a
theorem, not a reading of the source.

**S2 provably cannot carry the degree-4 invariant.** `pf` attains `-1`
(`pf_thetaMinus`), and every `SecondChernCharacter` has `value ≥ 0`. So
`secondChernCharacter_cannot_carry_degree4_invariant` proves no inhabitant can
hold that value. The ledger said S2 "shares only the name"; this is why, as a
proof.

**And the named `is_conscious` predicate is definitional.**
`crystallization_is_definitional` shows the upstream "phase transition theorem"
is `Iff.rfl` after unfolding --- `value ≥ 0.95 ↔ value ≥ 0.95`. It is true, and
it says nothing.

## Scope

These are theorems about the Lean objects as they stand. Nothing here claims
consciousness is or is not measured by any of them, nothing asserts the
Chern–Weil form is the physically correct `ch_2`, and nothing revives or refutes
the `0.95` threshold --- ch06's settlement assigns that threshold to the
entanglement form, not to S1 or S2. The degree-4 comparison inherits its scope
from the sign file: component level, two-plane family, with the wedge
identification still unformalized for the measured reason recorded there.
-/

import PF.ChernWeil
import PF.MillenniumSixReductions
import PF.ChernWeilDegree4SignIndefinite_2026_11_26

set_option autoImplicit false

namespace PF.Referee.Ch2S1S2Disclosure

open PrincipiaTractalis
open PrincipiaTractalis.ChernWeilDegree4Sign

/-! ## §1 S1 — the affine `ch_2` is target-anchored -/

/-- The definition, restated so the constant term is visible. -/
theorem ch_2_eq (α : ℝ) :
    MillenniumSix.ch_2 α = 0.95 + (α - Real.sqrt 2) / 10 := rfl

/-- **★ The headline evaluation carries no information about `0.95`. ★**
    The *same* computation returns `c` for every constant `c`, so
    "`ch_2` evaluates to `0.95` at `α = √2`" is a property of the constant term
    that was supplied, not a derivation of `0.95`. -/
theorem evaluation_returns_whatever_constant_is_supplied (c : ℝ) :
    c + (Real.sqrt 2 - Real.sqrt 2) / 10 = c := by
  ring

/-- Instantiated at the value the corpus uses, for the direct comparison. -/
theorem ch_2_at_sqrt_two : MillenniumSix.ch_2 (Real.sqrt 2) = 0.95 := by
  rw [ch_2_eq]
  ring

/-- **★ S1 attains every real value. ★** So it is not valued in `[0,1]`, is not
    a normalised invariant, and is not S2. -/
theorem ch_2_surjective (y : ℝ) :
    ∃ α : ℝ, MillenniumSix.ch_2 α = y := by
  refine ⟨Real.sqrt 2 + 10 * (y - 0.95), ?_⟩
  rw [ch_2_eq]
  ring

/-- In particular it takes negative values, which no `SecondChernCharacter`
    can. -/
theorem ch_2_takes_a_negative_value :
    ∃ α : ℝ, MillenniumSix.ch_2 α = -1 := ch_2_surjective (-1)

/-! ## §2 S2 — `SecondChernCharacter` is exactly the unit interval -/

/-- **★ There is nothing in S2 but a number in `[0,1]`. ★** No bundle, no
    connection, no curvature --- as an equivalence, not as a reading of the
    source. -/
def secondChernCharacterEquiv :
    SecondChernCharacter ≃ {x : ℝ // 0 ≤ x ∧ x ≤ 1} where
  toFun c := ⟨c.value, c.bounded⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every admissible value is attained, so S2 constrains nothing. -/
theorem secondChernCharacter_attains_every_admissible_value
    {x : ℝ} (h : 0 ≤ x ∧ x ≤ 1) :
    ∃ c : SecondChernCharacter, c.value = x :=
  ⟨⟨x, h⟩, rfl⟩

/-- **The named ``phase transition theorem'' is definitional.** After unfolding
    the threshold, `is_conscious c` *is* `c.value ≥ 0.95`; the equivalence is
    `Iff.rfl`. True, and without content. -/
theorem crystallization_is_definitional (c : SecondChernCharacter) :
    is_conscious c ↔ c.value ≥ (0.95 : ℝ) := by
  unfold is_conscious consciousness_threshold
  exact Iff.rfl

/-! ## §3 S2 cannot be the degree-4 invariant — the ledger's verdict, proved -/

/-- Every inhabitant of S2 is nonnegative, by its own field. -/
theorem secondChernCharacter_value_nonneg (c : SecondChernCharacter) :
    0 ≤ c.value := c.bounded.1

/-- **★ No `SecondChernCharacter` can hold the degree-4 invariant's value. ★**
    `pf thetaMinus = -1` and every S2 value is `≥ 0`. So S2 is not a carrier for
    the Chern–Weil degree-4 invariant --- which is the ledger's "shares only the
    name", as a proof rather than a reading. -/
theorem secondChernCharacter_cannot_carry_degree4_invariant :
    ¬ ∃ c : SecondChernCharacter, c.value = pf thetaMinus := by
  rintro ⟨c, hc⟩
  have h0 : 0 ≤ c.value := secondChernCharacter_value_nonneg c
  rw [hc, pf_thetaMinus] at h0
  norm_num at h0

/-- The same for S1, from the other side: S1 takes values no S2 can hold. -/
theorem s1_escapes_s2 :
    ∃ α : ℝ, ¬ ∃ c : SecondChernCharacter, c.value = MillenniumSix.ch_2 α := by
  obtain ⟨α, hα⟩ := ch_2_takes_a_negative_value
  refine ⟨α, ?_⟩
  rintro ⟨c, hc⟩
  have h0 : 0 ≤ c.value := secondChernCharacter_value_nonneg c
  rw [hc, hα] at h0
  norm_num at h0

/-! ## §4 Capstone -/

/-- **★ S1 AND S2 ARE NOT THE SECOND CHERN CHARACTER. ★**

    S1's headline evaluation is a property of its own constant term; S1 attains
    every real; S2 is equivalent to the unit interval and attains every value in
    it; its `is_conscious` predicate is definitional; and neither can carry the
    degree-4 invariant, which takes the value `-1`. Every conjunct proved above;
    none is a hypothesis. -/
theorem s1_s2_are_not_the_second_chern_character :
    (∀ c : ℝ, c + (Real.sqrt 2 - Real.sqrt 2) / 10 = c)
      ∧ (∀ y : ℝ, ∃ α : ℝ, MillenniumSix.ch_2 α = y)
      ∧ (∀ c : SecondChernCharacter, is_conscious c ↔ c.value ≥ (0.95 : ℝ))
      ∧ (¬ ∃ c : SecondChernCharacter, c.value = pf thetaMinus)
      ∧ (∃ α : ℝ, ¬ ∃ c : SecondChernCharacter, c.value = MillenniumSix.ch_2 α) :=
  ⟨evaluation_returns_whatever_constant_is_supplied,
   ch_2_surjective,
   crystallization_is_definitional,
   secondChernCharacter_cannot_carry_degree4_invariant,
   s1_escapes_s2⟩

end PF.Referee.Ch2S1S2Disclosure
