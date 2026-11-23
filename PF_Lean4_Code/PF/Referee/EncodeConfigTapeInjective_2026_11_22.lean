/-
# `encodeConfig_tape_eq`, proved

Author: Pablo Cohen
Date: November 22, 2026

`PF/AxiomElimination_Definitions.lean:221` states that the prime encoding is
injective in the tape, and ends its proof with `by_decidability_instances` — a
tactic that a whole-repo sweep (sources, mathlib, every `syntax`/`macro`/`elab`
form) finds declared nowhere. The statement is TRUE; it was simply never
proved.

Here it is, for the mirrors in
`PF/Referee/AxiomEliminationDefinitionsRefutation_2026_11_22.lean`.

## The argument

Write `n = l.length` and `P l = ∏_{i<n} p_{i+2}^(t_i + 1)`, where `p_j = nth
Prime j` and `t_i = (l.get i).val ∈ {0,1}`. Every exponent is `≥ 1`, so each
`p_{i+2}` genuinely occurs.

Read the exponents back off the factorisation. Since `Nat.factorization` turns
a product into a sum of `Finsupp.single`s, and the tape primes `p_{i+2}` are
pairwise distinct (`Nat.nth` is injective on an infinite predicate),

    (P l).factorization (p_{k+2})  =  if k < n then t_k + 1 else 0.

Two consequences, and they are the whole proof:

* **the length is determined** — if `l₁.length < l₂.length`, evaluate at
  `k = l₁.length`: the left side gives `0` and the right side gives `t_k + 1 ≥ 1`;
* **each entry is determined** — for `k < n`, `t_k + 1` is read off directly,
  and `Fin 2` is determined by its `val`.

`List.ext_getElem` then closes it.
-/

import PF.Referee.AxiomEliminationDefinitionsRefutation_2026_11_22
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.List.Indexes

namespace PF.Referee.AxiomEliminationDefinitionsRefutation

open scoped BigOperators

/-! ## §1 — the tape primes -/

/-- Every tape prime `p_{j+2}` is prime. -/
theorem tapePrime_prime (j : ℕ) : Nat.Prime (Nat.nth Nat.Prime (j + 2)) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (j + 2)

/-- Distinct indices give distinct tape primes. -/
theorem tapePrime_inj {a b : ℕ}
    (h : Nat.nth Nat.Prime (a + 2) = Nat.nth Nat.Prime (b + 2)) : a = b := by
  have := Nat.nth_injective Nat.infinite_setOf_prime h
  omega

/-- Tape primes are nonzero. -/
theorem tapePrime_ne_zero (j : ℕ) : Nat.nth Nat.Prime (j + 2) ≠ 0 :=
  (tapePrime_prime j).ne_zero

/-! ## §2 — the tape product as a `Finset.prod`, and its factorisation -/

/-- The tape encoding of a list, as a product over `Fin l.length`. -/
noncomputable def tapeProd (l : List (Fin 2)) : ℕ :=
  ∏ i : Fin l.length, (Nat.nth Nat.Prime (i.val + 2)) ^ ((l.get i).val + 1)

/-- `tapeProd` is exactly the `mapIdx` product used by `encodeConfig`. -/
theorem tapeProd_eq_mapIdx (l : List (Fin 2)) :
    (l.mapIdx (fun j sym => (Nat.nth Nat.Prime (j + 2)) ^ (sym.val + 1))).prod
      = tapeProd l := by
  rw [List.mapIdx_eq_ofFn, List.prod_ofFn]
  rfl

/-- Each factor is nonzero. -/
theorem tapeProd_factor_ne_zero (l : List (Fin 2)) (i : Fin l.length) :
    (Nat.nth Nat.Prime (i.val + 2)) ^ ((l.get i).val + 1) ≠ 0 :=
  pow_ne_zero _ (tapePrime_ne_zero _)

/-- **The exponents read back off the factorisation.** -/
theorem tapeProd_factorization (l : List (Fin 2)) (k : ℕ) :
    (tapeProd l).factorization (Nat.nth Nat.Prime (k + 2))
      = if h : k < l.length then (l.get ⟨k, h⟩).val + 1 else 0 := by
  unfold tapeProd
  rw [Nat.factorization_prod (fun i _ => tapeProd_factor_ne_zero l i)]
  rw [Finsupp.finset_sum_apply]
  have hterm : ∀ i : Fin l.length,
      ((Nat.nth Nat.Prime (i.val + 2)) ^ ((l.get i).val + 1)).factorization
          (Nat.nth Nat.Prime (k + 2))
        = if i.val = k then (l.get i).val + 1 else 0 := by
    intro i
    rw [Nat.Prime.factorization_pow (tapePrime_prime i.val), Finsupp.single_apply]
    by_cases hik : i.val = k
    · subst hik; simp
    · have : Nat.nth Nat.Prime (i.val + 2) ≠ Nat.nth Nat.Prime (k + 2) := by
        intro hEq; exact hik (tapePrime_inj hEq)
      simp [this, hik]
  simp_rw [hterm]
  by_cases hk : k < l.length
  · -- the single surviving index is ⟨k, hk⟩
    rw [dif_pos hk, Finset.sum_eq_single (⟨k, hk⟩ : Fin l.length)]
    · simp
    · intro b _ hb
      have hbk : (b : ℕ) ≠ k := fun h => hb (Fin.ext h)
      simp [hbk]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- k is past the end, so no index matches
    rw [dif_neg hk]
    refine Finset.sum_eq_zero ?_
    intro i _
    have hik : (i : ℕ) ≠ k := fun h => hk (h ▸ i.isLt)
    simp [hik]

/-! ## §3 — the length, then the entries -/

/-- Equal tape products force equal lengths (one direction; symmetry gives the
    other). Evaluate the factorisation at `k = l₂.length`: on the right the
    index is past the end and contributes `0`, on the left it contributes
    `t_k + 1 ≥ 1`. -/
theorem tapeProd_length_le (l₁ l₂ : List (Fin 2))
    (h : tapeProd l₁ = tapeProd l₂) : l₁.length ≤ l₂.length := by
  by_contra hlt
  push_neg at hlt
  have e₁ := tapeProd_factorization l₁ l₂.length
  have e₂ := tapeProd_factorization l₂ l₂.length
  rw [h, e₂, dif_neg (lt_irrefl _)] at e₁
  rw [dif_pos hlt] at e₁
  -- e₁ : 0 = (l₁.get ⟨l₂.length, hlt⟩).val + 1
  omega

/-- Equal tape products force equal lengths. -/
theorem tapeProd_length_eq (l₁ l₂ : List (Fin 2))
    (h : tapeProd l₁ = tapeProd l₂) : l₁.length = l₂.length :=
  le_antisymm (tapeProd_length_le l₁ l₂ h) (tapeProd_length_le l₂ l₁ h.symm)

/-- **The tape encoding is injective.** -/
theorem tapeProd_injective {l₁ l₂ : List (Fin 2)}
    (h : tapeProd l₁ = tapeProd l₂) : l₁ = l₂ := by
  have hlen := tapeProd_length_eq l₁ l₂ h
  refine List.ext_getElem hlen ?_
  intro k hk₁ hk₂
  have e₁ := tapeProd_factorization l₁ k
  have e₂ := tapeProd_factorization l₂ k
  rw [h, e₂, dif_pos hk₂] at e₁
  rw [dif_pos hk₁] at e₁
  -- e₁ : (l₁.get ⟨k,_⟩).val + 1 = (l₂.get ⟨k,_⟩).val + 1
  have hval : (l₁.get ⟨k, hk₁⟩).val = (l₂.get ⟨k, hk₂⟩).val := by omega
  simpa [List.get_eq_getElem] using Fin.ext hval

/-! ## §4 — `encodeConfig_tape_eq`, the statement the original file could not prove -/

/-- **`encodeConfig_tape_eq`.** Given equal encodings, equal states and equal
    head positions, the tapes are equal.

    This is the statement at `PF/AxiomElimination_Definitions.lean:221`, whose
    proof there ends in `by_decidability_instances` — a tactic declared nowhere
    in this repository or in mathlib. The statement is true; here is the
    proof. -/
theorem encodeConfig_tape_eq (c₁ c₂ : TMConfig)
    (hEnc : encodeConfig c₁ = encodeConfig c₂)
    (hState : c₁.state = c₂.state) (hHead : c₁.head = c₂.head) :
    c₁.tape = c₂.tape := by
  refine tapeProd_injective ?_
  rw [← tapeProd_eq_mapIdx, ← tapeProd_eq_mapIdx]
  unfold encodeConfig at hEnc
  rw [hState, hHead] at hEnc
  have hpos : 0 < 2 ^ c₂.state * 3 ^ c₂.head :=
    Nat.mul_pos (Nat.pow_pos (by norm_num)) (Nat.pow_pos (by norm_num))
  exact Nat.eq_of_mul_eq_mul_left hpos hEnc

end PF.Referee.AxiomEliminationDefinitionsRefutation
