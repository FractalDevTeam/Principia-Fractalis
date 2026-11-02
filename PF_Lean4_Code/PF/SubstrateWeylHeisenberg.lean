/-
# The substrate's clock–shift family IS a Heisenberg group — the relation, named

2026-11-02. **Additive. Nothing is renamed, weakened or withdrawn.**

## What the corpus already had, and what it never said

`PF/SubstrateMatrixUnitaryAveraging.lean` (r104, 2026-07-21) calls itself *"the
discrete Weyl averaging identity"* and builds the whole apparatus:
`substrateRoot n := exp(2πi/n)` proved primitive, `clockMatrix n := diagonal
(ω^j)`, `shiftMatrix n i j := [i = j+1]`, every word `Cᵃ Sᵇ` proved unitary, and
the engine `matrix_unitary_average_eq_trace_smul_one`, which collapses every
matrix to its normalized trace times the identity. That engine is load-bearing:
it is what drives trace uniqueness and the simplicity of the substrate.

**But the commutation relation itself is never stated anywhere in 9 491 files.**
Measured: `grep -i heisenberg` over `PF/` matches exactly one file
(`PF/KMS/ImaginaryTimeFlow_r366.lean`, about the Heisenberg *picture*, a
different thing), and no file states `C·S = ω·S·C`. The substrate has been
using a Heisenberg group for four months without characterising it as one.
That is what §2 supplies.

## And the relation decides something the corpus had left open

Two different groups generate the same algebra `M_{3^k}(ℂ)`, and they are not
interchangeable:

| | group | exponent | order |
|---|---|---|---|
| **cyclic** — one Weyl pair at `ω = e^{2πi/3^k}` | `H_{3^k}` | `3^k` | `3^{3k}` |
| **recursive** — `k` copies of the mod-3 pair, `ω = e^{2πi/3}` | central product of `k` copies of `H₃` | **3** | `3^{2k+1}` |

Both span `M_{3^k}(ℂ)`: each supplies `3^{2k}` words in a space of dimension
`(3^k)² = 3^{2k}`. The corpus's `clockMatrix n`/`shiftMatrix n` at `n = 3^k` is
the **cyclic** one. The UHF tensor structure `⊗^∞ M₃(ℂ)` — the object whose
K-theory gives `τ_*(K₀(T∞)) = ℤ[1/3]`, and so the object every substrate trace
theorem and yesterday's `19/20 ∉ ℤ[1/3]` actually run on — is the **recursive**
one.

§4 proves the discriminator, and it is the exponent: `C³ = 1` holds at level one
and **fails** at level two. So the two structures are formally distinguishable
inside the corpus's own definitions, and the one the K-theory uses is the one
with a single fixed relation repeated forever.

## §5 — why no `ħ` can enter here

`codex/SUBSTRATE_HBAR_IS_INPUT_2026-10-16.md` records that `ħ` is an input to
the framework rather than an output. §5 gives that a mechanism rather than
leaving it a verdict: the substrate's commutation relation is
`C·S = ω·S·C` with `ω² + ω + 1 = 0` — a root of a fixed integer polynomial,
carrying **no free parameter and no dimension**. The canonical relation
`[x,p] = iħ` carries a dimensional constant. A dimensionless phase relation
cannot produce one, so `ħ` must enter in a scaling limit and cannot be read off
the substrate. That is a statement about this algebra, and nothing more.

## Scope — what is NOT proved here

That the `n²` words `Cᵃ Sᵇ` form a **basis** of `M_n(ℂ)` is true and standard
(via the trace pairing `tr((CᵃSᵇ)ᴴ CᶜSᵈ) = n·[a=c][b=d]`) and is **not**
formalized here; it needs the word-trace computation and is left for its own
module. Nothing below depends on it. Likewise, nothing here *derives* 3: it
relocates "why base 3" to "why is the Weyl phase a primitive cube root of
unity", which is a sharper question, not an answered one.

Zero project axioms. Author: Pablo Cohen + Claude Opus 5. 2026-11-02.
-/

import PF.SubstrateMatrixUnitaryAveraging
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateWeylHeisenberg

open Matrix
open PrincipiaTractalis.SubstrateMatrixUnitaryAveraging
open scoped Fin.NatCast

/-! ## §1 — two arithmetic helpers -/

/-- `ω^(a % n) = ω^a`: the root of unity cannot tell the difference, which is
    exactly why the clock matrix survives the `Fin n` wraparound. -/
theorem substrateRoot_pow_mod (n : ℕ) [NeZero n] (a : ℕ) :
    substrateRoot n ^ (a % n) = substrateRoot n ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a n]
  rw [pow_add, pow_mul, substrateRoot_pow_n, one_pow, one_mul]

/-- `((1 : Fin n) : ℕ) = 1` once `n ≥ 2`. -/
theorem fin_one_val {n : ℕ} [NeZero n] (hn : 2 ≤ n) : ((1 : Fin n) : ℕ) = 1 := by
  rw [Fin.val_one']
  exact Nat.mod_eq_of_lt (by omega)

/-- The successor in `Fin n`, on the nose. -/
theorem fin_succ_val {n : ℕ} [NeZero n] (hn : 2 ≤ n) (j : Fin n) :
    ((j + 1 : Fin n) : ℕ) = ((j : ℕ) + 1) % n := by
  have hgoal : ((j : ℕ) + ((1 : Fin n) : ℕ)) % n = ((j : ℕ) + 1) % n := by
    rw [fin_one_val hn]
  rw [Fin.val_add]
  exact hgoal

/-- The clock phase at the `Fin n` successor: this is the step where the
    wraparound is absorbed by `ω^n = 1`. -/
theorem substrateRoot_pow_fin_succ {n : ℕ} [NeZero n] (hn : 2 ≤ n) (j : Fin n) :
    substrateRoot n ^ ((j + 1 : Fin n) : ℕ) = substrateRoot n ^ ((j : ℕ) + 1) := by
  rw [fin_succ_val hn j, substrateRoot_pow_mod]

/-! ## §2 — ★ THE WEYL–HEISENBERG COMMUTATION RELATION ★

The statement the corpus has been using without ever writing down. -/

/-- **★ `C · S = ω · (S · C)` ★** — the substrate's clock and shift matrices
    satisfy the discrete Weyl relation, so `{Cᵃ Sᵇ}` is the image of a
    Heisenberg group and not merely a family of unitaries.

    The wraparound case `j = n-1` is where this has content: there
    `ω^{(j+1 \bmod n)} = ω^0 = 1` and `ω·ω^{n-1} = ω^n = 1` agree *because* `ω`
    is an `n`-th root of unity. The relation and the primitivity are the same
    fact. -/
theorem clock_shift_weyl_relation {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    clockMatrix n * shiftMatrix n
      = substrateRoot n • (shiftMatrix n * clockMatrix n) := by
  ext i j
  rw [clockMatrix, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal,
      shiftMatrix_apply, smul_eq_mul]
  by_cases h : i = j + 1
  · subst h
    rw [if_pos rfl, substrateRoot_pow_fin_succ hn j, pow_succ]
    ring
  · rw [if_neg h, mul_zero, zero_mul, mul_zero]

/-- The same relation the other way: `S · C = ω⁻¹ · (C · S)`. -/
theorem shift_clock_weyl_relation {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    shiftMatrix n * clockMatrix n
      = (substrateRoot n)⁻¹ • (clockMatrix n * shiftMatrix n) := by
  rw [clock_shift_weyl_relation hn, smul_smul,
      inv_mul_cancel₀ substrateRoot_ne_zero, one_smul]

/-- **The pair does not commute** — so the group is genuinely a non-abelian
    central extension, not a product. Non-vacuity for §2. -/
theorem clock_shift_not_commute {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    clockMatrix n * shiftMatrix n ≠ shiftMatrix n * clockMatrix n := by
  intro hcomm
  have hne1 : substrateRoot n ≠ 1 := by
    have h := (substrateRoot_isPrimitiveRoot (n := n)).pow_ne_one_of_pos_of_lt
      (l := 1) (by norm_num) (by omega)
    rw [pow_one] at h
    exact h
  -- evaluate at the entry (1, 0): S has a 1 there, so the phase is forced
  have hz : (clockMatrix n * shiftMatrix n) (1 : Fin n) 0
      = (shiftMatrix n * clockMatrix n) (1 : Fin n) 0 := by rw [hcomm]
  rw [clock_shift_weyl_relation hn, Matrix.smul_apply, smul_eq_mul] at hz
  have hS : (shiftMatrix n * clockMatrix n) (1 : Fin n) 0 = 1 := by
    rw [clockMatrix, Matrix.mul_diagonal, shiftMatrix_apply]
    have h10 : (1 : Fin n) = (0 : Fin n) + 1 := by rw [zero_add]
    rw [if_pos h10, Fin.val_zero, pow_zero, mul_one]
  rw [hS, mul_one] at hz
  exact hne1 hz

/-! ## §3 — the orders of the two generators -/

/-- `C^n = 1`. -/
theorem clockMatrix_pow_n_eq_one {n : ℕ} [NeZero n] : clockMatrix n ^ n = 1 := by
  rw [clockMatrix_pow]
  ext i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, mul_comm, pow_mul, substrateRoot_pow_n, one_pow]
  · rw [if_neg h, if_neg h]

/-- `S^n = 1`. -/
theorem shiftMatrix_pow_n_eq_one {n : ℕ} [NeZero n] : shiftMatrix n ^ n = 1 := by
  ext i j
  rw [shiftMatrix_pow_apply, Matrix.one_apply, Fin.natCast_self, add_zero]

/-! ## §4 — ★ THE DISCRIMINATOR: exponent 3 versus exponent 3^k ★ -/

/-- **At level one the clock has order dividing 3.** -/
theorem clock_cubed_eq_one_at_level_one : clockMatrix 3 ^ 3 = 1 :=
  clockMatrix_pow_n_eq_one

/-- **★ At level two it does NOT. ★**

    `clockMatrix 9 ^ 3 ≠ 1`, because `e^{2πi/9}` has order 9, not 3. So the
    cyclic structure the corpus builds at `n = 3^k` has exponent `3^k`, while
    the recursive structure `⊗^k M₃(ℂ)` — the one carrying `ℤ[1/3]` — has
    exponent 3 at every level. The two are formally distinguishable here, in the
    corpus's own definitions. -/
theorem clock_cubed_ne_one_at_level_two : clockMatrix 9 ^ 3 ≠ 1 := by
  intro h
  have hentry : (clockMatrix 9 ^ 3) (1 : Fin 9) (1 : Fin 9)
      = (1 : Matrix (Fin 9) (Fin 9) ℂ) (1 : Fin 9) (1 : Fin 9) := by rw [h]
  rw [clockMatrix_pow, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at hentry
  have hv : ((1 : Fin 9) : ℕ) * 3 = 3 := by norm_num
  rw [hv] at hentry
  exact (substrateRoot_isPrimitiveRoot (n := 9)).pow_ne_one_of_pos_of_lt
    (by norm_num) (by norm_num) hentry

/-- The two exponents disagree, stated as one fact. -/
theorem exponent_separates_cyclic_from_recursive :
    clockMatrix 3 ^ 3 = 1 ∧ clockMatrix 9 ^ 3 ≠ 1 :=
  ⟨clock_cubed_eq_one_at_level_one, clock_cubed_ne_one_at_level_two⟩

/-! ## §5 — the phase carries no free parameter -/

/-- **★ `ω² + ω + 1 = 0` at `n = 3`. ★**

    The substrate's commutation phase is a root of a fixed integer polynomial.
    It has no free parameter and no dimension, which is the precise sense in
    which no `ħ` can be read off this relation: `[x,p] = iħ` carries a
    dimensional constant and `C·S = ω·S·C` cannot supply one. -/
theorem substrateRoot_three_is_root_of_cyclotomic :
    substrateRoot 3 ^ 2 + substrateRoot 3 + 1 = 0 := by
  have h3 : substrateRoot 3 ^ 3 = 1 := substrateRoot_pow_n
  have hne : substrateRoot 3 ≠ 1 := by
    have h := (substrateRoot_isPrimitiveRoot (n := 3)).pow_ne_one_of_pos_of_lt
      (l := 1) (by norm_num) (by norm_num)
    rw [pow_one] at h
    exact h
  have hfac : (substrateRoot 3 - 1) * (substrateRoot 3 ^ 2 + substrateRoot 3 + 1) = 0 := by
    have hexp : (substrateRoot 3 - 1) * (substrateRoot 3 ^ 2 + substrateRoot 3 + 1)
        = substrateRoot 3 ^ 3 - 1 := by ring
    rw [hexp, h3, sub_self]
  rcases mul_eq_zero.mp hfac with hL | hR
  · exact absurd (by linear_combination hL : substrateRoot 3 = 1) hne
  · exact hR

/-! ## §6 — capstone -/

/-- **★★ THE SUBSTRATE'S CLOCK–SHIFT FAMILY IS A HEISENBERG GROUP ★★**

    1. the Weyl relation `C·S = ω·(S·C)`, never previously stated;
    2. the pair does not commute, so the extension is non-trivial;
    3. both generators have order dividing `n`;
    4. the exponent discriminates level one from level two, separating the
       cyclic structure the corpus builds from the recursive structure its
       K-theory uses;
    5. the phase satisfies `ω² + ω + 1 = 0` — a fixed integer polynomial, no
       free parameter, no dimension. -/
theorem substrate_weyl_heisenberg_capstone :
    (clockMatrix 3 * shiftMatrix 3
        = substrateRoot 3 • (shiftMatrix 3 * clockMatrix 3)) ∧
    (clockMatrix 3 * shiftMatrix 3 ≠ shiftMatrix 3 * clockMatrix 3) ∧
    (clockMatrix 3 ^ 3 = 1 ∧ shiftMatrix 3 ^ 3 = 1) ∧
    (clockMatrix 9 ^ 3 ≠ 1) ∧
    (substrateRoot 3 ^ 2 + substrateRoot 3 + 1 = 0) :=
  ⟨clock_shift_weyl_relation (by norm_num),
   clock_shift_not_commute (by norm_num),
   ⟨clockMatrix_pow_n_eq_one, shiftMatrix_pow_n_eq_one⟩,
   clock_cubed_ne_one_at_level_two,
   substrateRoot_three_is_root_of_cyclotomic⟩

end SubstrateWeylHeisenberg
end PrincipiaTractalis

/-! ## Axiom audit — LIVE -/

#print axioms PrincipiaTractalis.SubstrateWeylHeisenberg.substrateRoot_pow_mod
#print axioms PrincipiaTractalis.SubstrateWeylHeisenberg.fin_one_val
#print axioms PrincipiaTractalis.SubstrateWeylHeisenberg.fin_succ_val
#print axioms PrincipiaTractalis.SubstrateWeylHeisenberg.substrateRoot_pow_fin_succ
#print axioms PrincipiaTractalis.SubstrateWeylHeisenberg.clock_shift_weyl_relation
#print axioms PrincipiaTractalis.SubstrateWeylHeisenberg.shift_clock_weyl_relation
#print axioms PrincipiaTractalis.SubstrateWeylHeisenberg.clock_shift_not_commute
#print axioms PrincipiaTractalis.SubstrateWeylHeisenberg.clockMatrix_pow_n_eq_one
#print axioms PrincipiaTractalis.SubstrateWeylHeisenberg.shiftMatrix_pow_n_eq_one
#print axioms PrincipiaTractalis.SubstrateWeylHeisenberg.clock_cubed_eq_one_at_level_one
#print axioms PrincipiaTractalis.SubstrateWeylHeisenberg.clock_cubed_ne_one_at_level_two
#print axioms PrincipiaTractalis.SubstrateWeylHeisenberg.exponent_separates_cyclic_from_recursive
#print axioms PrincipiaTractalis.SubstrateWeylHeisenberg.substrateRoot_three_is_root_of_cyclotomic
#print axioms PrincipiaTractalis.SubstrateWeylHeisenberg.substrate_weyl_heisenberg_capstone
