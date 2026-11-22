/-
# Refutation: two "eliminated axioms" in `PF/AxiomElimination_Definitions.lean`
  are false statements, and a third has no proof

Author: Pablo Cohen
Date: November 22, 2026

`PF/AxiomElimination_Definitions.lean` declares itself an axiom-elimination
file -- "These are NOT true axioms - they're lazily axiomatized definitions!"
-- and replaces six axioms with theorems. It has **0 `axiom`** and **0
`sorry`**, so every grep-based gate in the repository reports it clean.

It has also never been compiled. Its module sat outside the `lean_lib PF`
target, which until 2026-11-21 carried no `globs`, so only the root module's
transitive imports were ever built. Nothing imports this file either. Compiling
it for the first time produces 19 errors, and three of its six theorems do not
survive contact with the kernel:

* `encodeConfig_tape_eq` ends with the tactic `by_decidability_instances`,
  which **does not exist**, under a comment reading "For simplicity, use
  decidability of equality on lists of finite type". The statement is true --
  the prime encoding is injective in the tape -- but it is not proved.
* `encodeConfig_polynomial_time` ends with `exact le_refl _` under a comment
  reading "Apply prime_bound axiom". Its statement is **FALSE**.
* `encodeConfig_growth_bound` ends with `exact le_refl _` under a comment
  reading "Apply log_conversion axiom for change of base". Its statement is
  **FALSE**.

This file proves the last two false, by exhibiting one configuration. Both
claimed bounds multiply their right-hand side by the tape length, so both
right-hand sides vanish on an empty tape while the left-hand sides do not --
the encoding of a configuration still carries its state and head position.
`Real.log 1 = 0` makes the growth bound fail on every length-one tape as well,
so this is not a lone edge case at zero.

The three definitions below mirror `PF/AxiomElimination_Definitions.lean`
verbatim (lines 57, 79 and 90 of that file). They are duplicated rather than
imported precisely because that module does not compile; when it is repaired,
these should be replaced by imports of the originals.

Scope: this refutes the two statements as written. It says nothing against the
*intent* -- that the encoding is polynomially bounded -- which is true with an
additive term for the state and head contributions, or under a nonempty-tape
hypothesis. Supplying the corrected bounds, and a real proof of
`encodeConfig_tape_eq`, is formalisation work and is not done here.
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PF.Referee.AxiomEliminationDefinitionsRefutation

/-! ## §1 — Mirrors of the three declarations under test -/

/-- Mirror of `PrincipiaTractalis.nat_log`
    (`PF/AxiomElimination_Definitions.lean:57`). -/
def nat_log (b : ℕ) (n : ℕ) : ℕ :=
  if b > 1 ∧ n > 0 then Nat.log b n else 0

/-- Mirror of `PrincipiaTractalis.TMConfig`
    (`PF/AxiomElimination_Definitions.lean:79`). Note that no field carries an
    invariant: `state` and `head` are unconstrained naturals and `tape` is an
    arbitrary list, so a configuration with a nonzero state and an empty tape
    is well-formed. That is the whole content of the refutations below. -/
structure TMConfig where
  state : ℕ
  head : ℕ
  tape : List (Fin 2)

/-- Mirror of `PrincipiaTractalis.encodeConfig`
    (`PF/AxiomElimination_Definitions.lean:90`). -/
noncomputable def encodeConfig (c : TMConfig) : ℕ :=
  2 ^ (c.state) * 3 ^ (c.head) *
    (c.tape.mapIdx (fun j sym => (Nat.nth Nat.Prime (j + 2)) ^ (sym.val + 1))).prod

/-! ## §2 — The witness -/

/-- State 1, head 0, empty tape. A legal `TMConfig`. -/
def witness : TMConfig := ⟨1, 0, []⟩

/-- `encodeConfig witness = 2 ^ 1 * 3 ^ 0 * (empty product) = 2`. -/
theorem encode_witness : encodeConfig witness = 2 := by
  unfold encodeConfig witness
  norm_num

/-- `nat_log 2 2 = Nat.log 2 2 = 1`: the guard `2 > 1 ∧ 2 > 0` holds. -/
theorem natLog_two_two : nat_log 2 2 = 1 := by
  unfold nat_log
  norm_num
  -- `norm_num` discharges the `2 > 1 ∧ 2 > 0` guard and leaves `Nat.log 2 2 = 1`.
  -- `Nat.log` is defined by well-founded recursion, so it does not reduce by
  -- `decide`; use the characterisation `2 ^ 1 ≤ 2 < 2 ^ 2`
  -- (`Mathlib/Data/Nat/Log.lean:142`).
  exact Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)

/-- The witness has an empty tape. -/
theorem witness_tape_length : witness.tape.length = 0 := rfl

/-! ## §3 — The two refutations -/

/-- **`encodeConfig_polynomial_time` is false.**

    The claim is `∀ c, ∃ k, ∀ n, n = c.tape.length →
    nat_log 2 (encodeConfig c) ≤ n * nat_log 2 n * k`.

    At `witness` the right-hand side is `0 * nat_log 2 0 * k = 0` for every
    `k`, while the left-hand side is `nat_log 2 2 = 1`. No choice of `k`
    rescues it: the claim reduces to `1 ≤ 0`. -/
theorem polynomial_time_claim_is_false :
    ¬ (∀ c : TMConfig, ∃ k : ℕ, ∀ n : ℕ, n = c.tape.length →
        nat_log 2 (encodeConfig c) ≤ n * nat_log 2 n * k) := by
  intro h
  obtain ⟨k, hk⟩ := h witness
  have hone : nat_log 2 (encodeConfig witness) ≤ 0 * nat_log 2 0 * k :=
    hk 0 witness_tape_length.symm
  rw [encode_witness, natLog_two_two] at hone
  simp at hone

/-- **`encodeConfig_growth_bound` is false.**

    The claim is `∀ c, ∃ C > 0,
    Real.log (encodeConfig c) ≤ C * c.tape.length * Real.log c.tape.length`.

    At `witness` the right-hand side is `C * 0 * Real.log 0 = 0`, while the
    left-hand side is `Real.log 2 > 0`. Since `Real.log 1 = 0` as well, the
    same failure occurs for every configuration with a length-one tape and a
    nonzero state -- the bound is not merely wrong at the empty tape. -/
theorem growth_bound_claim_is_false :
    ¬ (∀ c : TMConfig, ∃ C : ℝ, C > 0 ∧
        Real.log (encodeConfig c : ℝ) ≤
          C * c.tape.length * Real.log c.tape.length) := by
  intro h
  obtain ⟨C, _hC, hle⟩ := h witness
  rw [encode_witness, witness_tape_length] at hle
  norm_num at hle
  exact absurd hle (not_le.mpr (Real.log_pos (by norm_num)))

/-- Both refutations together, as one citable fact. -/
theorem axiom_elimination_definitions_has_two_false_claims :
    (¬ (∀ c : TMConfig, ∃ k : ℕ, ∀ n : ℕ, n = c.tape.length →
          nat_log 2 (encodeConfig c) ≤ n * nat_log 2 n * k))
    ∧ (¬ (∀ c : TMConfig, ∃ C : ℝ, C > 0 ∧
          Real.log (encodeConfig c : ℝ) ≤
            C * c.tape.length * Real.log c.tape.length)) :=
  ⟨polynomial_time_claim_is_false, growth_bound_claim_is_false⟩

end PF.Referee.AxiomEliminationDefinitionsRefutation
