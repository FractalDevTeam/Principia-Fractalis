/-
# r104: Substrate matrix-level UNITARY AVERAGING ENGINE —
#       the discrete Weyl (clock-and-shift) family averages every
#       matrix to (trace/n) • 1

★ 2026-07-21 r104 — Milestone M3.1 of the Glimm-simplicity program
(the route to unconditional completion-tier faithfulness of the
substrate UHF trace, continuing r102/r103) ★

## The framework-first content

r103 reduced completion-tier faithfulness of τ_UHF to a single honest
hypothesis: algebraic simplicity of the substrate UHF C*-algebra
completion (Glimm 1960). The engine of Glimm's simplicity argument is
PURE FINITE-DIMENSIONAL LINEAR ALGEBRA: a concrete finite family of
unitaries in M_n(ℂ) whose conjugation average sends EVERY matrix to
the scalar matrix (trace/n)•1. Since two-sided ideals absorb
conjugation, sums, and scalars, the average of any ideal element
stays in the ideal — so a nonzero ideal element with nonzero trace
forces the identity into the ideal. r104 builds that engine.

**M3.1 — the discrete Weyl averaging identity**:
  * `substrateRoot n := exp(2πi/n)` — the substrate primitive n-th
    root of unity (`Complex.isPrimitiveRoot_exp`), with
    `substrateRoot_pow_star : star(ω^m) = (ω^m)⁻¹`.
  * `substrate_clock_character_sum` — the character orthogonality
    Σ_{a<n} (ω^i·conj(ω^j))^a = n·[i=j] (geometric sum of roots of
    unity via `geom_sum_mul` + `IsPrimitiveRoot.pow_inj`).
  * `clockMatrix n := diagonal (ω^j)` — the clock matrix C, with
    `clockMatrix_mem_unitaryGroup` and the closed form
    `clockMatrix_pow : C^m = diagonal (ω^(j·m))`.
  * `shiftMatrix n := [i = j+1]` — the cyclic shift matrix S, with
    `shiftMatrix_mem_unitaryGroup` and the closed form
    `shiftMatrix_pow_apply : (S^m) i j = [i = j + m]`.
  * `clockShiftWord_mem_unitaryGroup` — every word C^a·S^b is
    unitary (powers and products of unitaries via `pow_mem`/`mul_mem`).
  * Stage A `clock_average_eq_diagonalPart` — conjugation-averaging
    over {C^a} KILLS the off-diagonal:
    (1/n)·Σ_a C^a x (C^a)ᴴ = diagonal (diag x).
  * Stage B `shift_average_diagonal_eq_trace_smul_one` — conjugation-
    averaging over {S^b} EQUALIZES the diagonal:
    (1/n)·Σ_b S^b D (S^b)ᴴ = (trace D / n)•1 for diagonal D.
  * **★ `matrix_unitary_average_eq_trace_smul_one`** — THE ENGINE:
    for every x ∈ M_n(ℂ),
    (1/n²)·Σ_{a,b} (C^a S^b) x (C^a S^b)ᴴ = (trace x / n)•1.
  * **`trace_smul_one_mem_of_two_sided_absorbing`** — the M3.2
    plug-in: any set S ⊆ M_n(ℂ) closed under addition, left/right
    multiplication by arbitrary matrices, and ℂ-smul satisfies
    x ∈ S → (trace x / n)•1 ∈ S.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-21 r104 — the substrate matrix-level unitary averaging
engine: the discrete Weyl family averages every matrix to its
normalized trace times the identity.
-/

import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateMatrixUnitaryAveraging

open Matrix

/- The `ℕ → Fin n` mod-n cast (`Fin.instAddMonoidWithOne`) is a scoped
instance in mathlib; the shift-power closed forms below use it to state
`(S^m) i j = [i = j + (m : Fin n)]`. -/
open scoped Fin.NatCast

/-! ## §1 — the substrate primitive root of unity and its character sum -/

/-- **r104.a: the substrate primitive n-th root of unity**
    `ω := exp(2πi/n)`. -/
noncomputable def substrateRoot (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / n)

theorem substrateRoot_def (n : ℕ) :
    substrateRoot n = Complex.exp (2 * Real.pi * Complex.I / n) := rfl

variable {n : ℕ} [NeZero n]

/-- **r104.b: `ω` is a primitive n-th root of unity**
    (`Complex.isPrimitiveRoot_exp`). -/
theorem substrateRoot_isPrimitiveRoot : IsPrimitiveRoot (substrateRoot n) n := by
  rw [substrateRoot_def]
  exact Complex.isPrimitiveRoot_exp n (NeZero.ne n)

/-- **r104.c: `ω^n = 1`**. -/
theorem substrateRoot_pow_n : substrateRoot n ^ n = 1 :=
  substrateRoot_isPrimitiveRoot.pow_eq_one

omit [NeZero n] in
/-- **r104.d: `ω ≠ 0`** — a value of the complex exponential. -/
theorem substrateRoot_ne_zero : substrateRoot n ≠ 0 := by
  rw [substrateRoot_def]
  exact Complex.exp_ne_zero _

/-- **r104.e: `ω` lies on the unit circle** — `‖ω‖ = 1`, from
    `ω^n = 1` via `Complex.norm_eq_one_of_pow_eq_one`. -/
theorem substrateRoot_norm : ‖(substrateRoot n : ℂ)‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one substrateRoot_pow_n (NeZero.ne n)

/-- **r104.f: on the unit circle, star is inverse**:
    `star ω = ω⁻¹` (`Complex.inv_eq_conj`). -/
theorem substrateRoot_star : star (substrateRoot n) = (substrateRoot n)⁻¹ := by
  rw [Complex.star_def]
  exact (Complex.inv_eq_conj substrateRoot_norm).symm

/-- **r104.g: `star (ω^m) = (ω^m)⁻¹`** for every natural power. -/
theorem substrateRoot_pow_star (m : ℕ) :
    star (substrateRoot n ^ m) = (substrateRoot n ^ m)⁻¹ := by
  rw [star_pow, substrateRoot_star, inv_pow]

/-- **★ r104.h: CHARACTER ORTHOGONALITY — the root-of-unity
    geometric sum ★**

    `Σ_{a : Fin n} (ω^i · star(ω^j))^a = n·[i = j]`.

    For i = j the base is 1 and the sum is n; for i ≠ j the base ζ
    satisfies ζ^n = 1 and ζ ≠ 1 (by `IsPrimitiveRoot.pow_inj`), so
    the geometric sum vanishes by `geom_sum_mul`:
    (Σ ζ^a)·(ζ − 1) = ζ^n − 1 = 0. -/
theorem substrate_clock_character_sum (i j : Fin n) :
    ∑ a : Fin n,
      (substrateRoot n ^ (i : ℕ) * star (substrateRoot n ^ (j : ℕ))) ^ (a : ℕ)
      = if i = j then (n : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (substrateRoot n ^ (i : ℕ) * star (substrateRoot n ^ (j : ℕ))) ^ k) n]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, substrateRoot_pow_star,
        mul_inv_cancel₀ (pow_ne_zero _ substrateRoot_ne_zero)]
    simp
  · rw [if_neg h, substrateRoot_pow_star]
    set ζ : ℂ := substrateRoot n ^ (i : ℕ) * (substrateRoot n ^ (j : ℕ))⁻¹ with hζ
    have hζn : ζ ^ n = 1 := by
      rw [hζ, mul_pow, inv_pow, ← pow_mul, ← pow_mul,
          mul_comm (i : ℕ) n, mul_comm (j : ℕ) n, pow_mul, pow_mul,
          substrateRoot_pow_n, one_pow, one_pow, inv_one, mul_one]
    have hζ1 : ζ ≠ 1 := by
      rw [hζ, Ne, mul_inv_eq_one₀ (pow_ne_zero _ substrateRoot_ne_zero)]
      intro hone
      exact h (Fin.ext
        (substrateRoot_isPrimitiveRoot.pow_inj i.isLt j.isLt hone))
    have hgeom := geom_sum_mul ζ n
    rw [hζn, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hζ1)

/-! ## §2 — the clock matrix -/

/-- **r104.i: the substrate CLOCK MATRIX** `C := diagonal (ω^j)`. -/
noncomputable def clockMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun j : Fin n => substrateRoot n ^ (j : ℕ))

omit [NeZero n] in
/-- **r104.j: closed form for clock powers**:
    `C^m = diagonal (ω^(j·m))` — via `Matrix.diagonal_pow`. -/
theorem clockMatrix_pow (m : ℕ) :
    clockMatrix n ^ m
      = Matrix.diagonal (fun j : Fin n => substrateRoot n ^ ((j : ℕ) * m)) := by
  rw [clockMatrix, Matrix.diagonal_pow]
  congr 1
  funext j
  rw [Pi.pow_apply, ← pow_mul]

/-- **r104.k: THE CLOCK MATRIX IS UNITARY** —
    `C ∈ Matrix.unitaryGroup (Fin n) ℂ`, since
    `C·Cᴴ = diagonal (ω^j · (ω^j)⁻¹) = 1`. -/
theorem clockMatrix_mem_unitaryGroup :
    clockMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, clockMatrix,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
  congr 1
  funext j
  rw [Pi.star_apply, substrateRoot_pow_star,
      mul_inv_cancel₀ (pow_ne_zero _ substrateRoot_ne_zero)]

omit [NeZero n] in
/-- **r104.l: clock conjugation entrywise**:
    `(C^m · y · (C^m)ᴴ) i j = ω^(i·m) · y i j · star(ω^(j·m))`. -/
theorem clockMatrix_pow_conj_apply (m : ℕ) (y : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    (clockMatrix n ^ m * y * (clockMatrix n ^ m)ᴴ) i j
      = substrateRoot n ^ ((i : ℕ) * m) * y i j
          * star (substrateRoot n ^ ((j : ℕ) * m)) := by
  rw [clockMatrix_pow, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Pi.star_apply]

/-! ## §3 — the shift matrix -/

/-- **r104.m: the substrate cyclic SHIFT MATRIX**
    `S i j := [i = j + 1]` (indices in `Fin n`, addition mod n) —
    the permutation matrix of the n-cycle. -/
def shiftMatrix (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j : Fin n => if i = j + 1 then 1 else 0

theorem shiftMatrix_apply (i j : Fin n) :
    shiftMatrix n i j = if i = j + 1 then 1 else 0 := rfl

/-- **r104.n: closed form for shift powers**:
    `(S^m) i j = [i = j + m]` — by induction on m. -/
theorem shiftMatrix_pow_apply (m : ℕ) (i j : Fin n) :
    (shiftMatrix n ^ m) i j = if i = j + (m : Fin n) then 1 else 0 := by
  induction m generalizing i j with
  | zero =>
      rw [pow_zero, Matrix.one_apply, Nat.cast_zero, add_zero]
  | succ m ih =>
      rw [pow_succ, Matrix.mul_apply]
      have hsummand : ∀ k : Fin n,
          (shiftMatrix n ^ m) i k * shiftMatrix n k j
            = if k = j + 1 then (if i = k + (m : Fin n) then (1 : ℂ) else 0)
              else 0 := by
        intro k
        rw [ih, shiftMatrix_apply]
        by_cases hk : k = j + 1
        · simp only [if_pos hk, mul_one]
        · simp only [if_neg hk, mul_zero]
      rw [Finset.sum_congr rfl fun k _ => hsummand k,
          Finset.sum_ite_eq' Finset.univ (j + 1)
            (fun k => if i = k + (m : Fin n) then (1 : ℂ) else 0),
          if_pos (Finset.mem_univ _)]
      have hcast : (j + 1) + (m : Fin n) = j + ((m + 1 : ℕ) : Fin n) := by
        push_cast
        abel
      rw [hcast]

/-- **r104.o: closed form for conjugate-transposed shift powers**:
    `((S^m)ᴴ) i j = [j = i + m]` (real 0/1 entries). -/
theorem shiftMatrix_pow_conjTranspose_apply (m : ℕ) (i j : Fin n) :
    ((shiftMatrix n ^ m)ᴴ) i j = if j = i + (m : Fin n) then 1 else 0 := by
  rw [Matrix.conjTranspose_apply, shiftMatrix_pow_apply]
  by_cases h : j = i + (m : Fin n)
  · rw [if_pos h, star_one]
  · rw [if_neg h, star_zero]

/-- **r104.p: THE SHIFT MATRIX IS UNITARY** —
    `S ∈ Matrix.unitaryGroup (Fin n) ℂ`. -/
theorem shiftMatrix_mem_unitaryGroup :
    shiftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hsummand : ∀ k : Fin n,
      shiftMatrix n i k * (shiftMatrix n)ᴴ k j
        = if k = i - 1 then (if j = k + 1 then (1 : ℂ) else 0) else 0 := by
    intro k
    rw [Matrix.conjTranspose_apply, shiftMatrix_apply, shiftMatrix_apply,
        apply_ite (star : ℂ → ℂ), star_one, star_zero]
    by_cases hk : k = i - 1
    · have hik : i = k + 1 := by rw [hk, sub_add_cancel]
      rw [if_pos hik, one_mul, if_pos hk]
    · have hik : ¬(i = k + 1) := fun hc => hk (by rw [hc, add_sub_cancel_right])
      rw [if_neg hik, zero_mul, if_neg hk]
  rw [Finset.sum_congr rfl fun k _ => hsummand k,
      Finset.sum_ite_eq' Finset.univ (i - 1)
        (fun k => if j = k + 1 then (1 : ℂ) else 0),
      if_pos (Finset.mem_univ _), sub_add_cancel]
  by_cases h : i = j
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun hc => h hc.symm), if_neg h]

/-- **r104.q: every clock-shift word `C^a · S^b` is unitary** —
    powers of unitaries are unitary (`pow_mem`), products of
    unitaries are unitary (`mul_mem`). -/
theorem clockShiftWord_mem_unitaryGroup (a b : ℕ) :
    clockMatrix n ^ a * shiftMatrix n ^ b ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  mul_mem (pow_mem clockMatrix_mem_unitaryGroup a)
    (pow_mem shiftMatrix_mem_unitaryGroup b)

/-- **r104.r: shift conjugation entrywise**:
    `(S^b · x · (S^b)ᴴ) i j = x (i−b) (j−b)` — conjugation by the
    b-th shift power translates both indices. -/
theorem shiftMatrix_pow_conj_apply (b : Fin n) (x : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    (shiftMatrix n ^ (b : ℕ) * x * (shiftMatrix n ^ (b : ℕ))ᴴ) i j
      = x (i - b) (j - b) := by
  rw [Matrix.mul_apply]
  have h1 : ∀ k : Fin n,
      (shiftMatrix n ^ (b : ℕ) * x) i k * ((shiftMatrix n ^ (b : ℕ))ᴴ) k j
        = if k = j - b then (shiftMatrix n ^ (b : ℕ) * x) i k else 0 := by
    intro k
    rw [shiftMatrix_pow_conjTranspose_apply, Fin.cast_val_eq_self]
    by_cases hk : k = j - b
    · have hjk : j = k + b := by rw [hk, sub_add_cancel]
      rw [if_pos hjk, mul_one, if_pos hk]
    · have hjk : ¬(j = k + b) := fun hc => hk (by rw [hc, add_sub_cancel_right])
      rw [if_neg hjk, mul_zero, if_neg hk]
  rw [Finset.sum_congr rfl fun k _ => h1 k,
      Finset.sum_ite_eq' Finset.univ (j - b)
        (fun k => (shiftMatrix n ^ (b : ℕ) * x) i k),
      if_pos (Finset.mem_univ _), Matrix.mul_apply]
  have h2 : ∀ l : Fin n,
      (shiftMatrix n ^ (b : ℕ)) i l * x l (j - b)
        = if l = i - b then x l (j - b) else 0 := by
    intro l
    rw [shiftMatrix_pow_apply, Fin.cast_val_eq_self]
    by_cases hl : l = i - b
    · have hil : i = l + b := by rw [hl, sub_add_cancel]
      rw [if_pos hil, one_mul, if_pos hl]
    · have hil : ¬(i = l + b) := fun hc => hl (by rw [hc, add_sub_cancel_right])
      rw [if_neg hil, zero_mul, if_neg hl]
  rw [Finset.sum_congr rfl fun l _ => h2 l,
      Finset.sum_ite_eq' Finset.univ (i - b) (fun l => x l (j - b)),
      if_pos (Finset.mem_univ _)]

/-! ## §4 — Stage A: the clock average kills the off-diagonal -/

/-- **★★★ r104.s: STAGE A — CLOCK AVERAGING EXTRACTS THE DIAGONAL
    PART ★★★**

    `(1/n) • Σ_{a : Fin n} C^a · x · (C^a)ᴴ = diagonal (diag x)`.

    Entrywise, the (i,j) entry of the sum is
    `x i j · Σ_a (ω^i · star(ω^j))^a = x i j · n·[i=j]` by character
    orthogonality (r104.h): conjugating by all clock powers dephases
    and cancels every off-diagonal entry. -/
theorem clock_average_eq_diagonalPart (x : Matrix (Fin n) (Fin n) ℂ) :
    (1 / (n : ℂ)) • ∑ a : Fin n,
        clockMatrix n ^ (a : ℕ) * x * (clockMatrix n ^ (a : ℕ))ᴴ
      = Matrix.diagonal (fun i => x i i) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  ext i j
  rw [Matrix.smul_apply, Matrix.sum_apply]
  have hterm : ∀ a : Fin n,
      (clockMatrix n ^ (a : ℕ) * x * (clockMatrix n ^ (a : ℕ))ᴴ) i j
        = x i j * (substrateRoot n ^ (i : ℕ)
            * star (substrateRoot n ^ (j : ℕ))) ^ (a : ℕ) := by
    intro a
    rw [clockMatrix_pow_conj_apply, pow_mul, pow_mul, star_pow]
    ring
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.mul_sum,
      substrate_clock_character_sum]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    simp only [Matrix.diagonal_apply_eq]
    rw [smul_eq_mul, one_div, mul_comm (x i i) ((n : ℂ)), ← mul_assoc,
        inv_mul_cancel₀ hn, one_mul]
  · rw [if_neg h, mul_zero, smul_zero, Matrix.diagonal_apply_ne _ h]

/-! ## §5 — Stage B: the shift average equalizes the diagonal -/

/-- **★★★ r104.t: STAGE B — SHIFT AVERAGING EQUALIZES THE
    DIAGONAL ★★★**

    `(1/n) • Σ_{b : Fin n} S^b · D · (S^b)ᴴ = (trace D / n) • 1`
    for every diagonal matrix `D = diagonal d`.

    Conjugation by S^b cyclically rotates the diagonal (r104.r), so
    averaging over all n rotations replaces every diagonal entry by
    the uniform average `(Σ d)/n = trace D / n` (reindexing along the
    bijection `b ↦ i − b`, `Equiv.subLeft`). -/
theorem shift_average_diagonal_eq_trace_smul_one (d : Fin n → ℂ) :
    (1 / (n : ℂ)) • ∑ b : Fin n,
        shiftMatrix n ^ (b : ℕ) * Matrix.diagonal d
          * (shiftMatrix n ^ (b : ℕ))ᴴ
      = (Matrix.trace (Matrix.diagonal d) / n) • 1 := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.one_apply,
    Matrix.trace_diagonal, smul_eq_mul]
  rw [Finset.sum_congr rfl fun b _ =>
    shiftMatrix_pow_conj_apply b (Matrix.diagonal d) i j]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, mul_one]
    simp only [Matrix.diagonal_apply_eq]
    have hre : ∑ b : Fin n, d (i - b) = ∑ c : Fin n, d c := by
      have h1 := Equiv.sum_comp (Equiv.subLeft i) d
      simpa [Equiv.subLeft_apply] using h1
    rw [hre, one_div, inv_mul_eq_div]
  · rw [if_neg h, mul_zero]
    have hzero : ∀ b : Fin n,
        Matrix.diagonal d (i - b) (j - b) = 0 := fun b =>
      Matrix.diagonal_apply_ne d (fun hc => h (sub_left_inj.mp hc))
    rw [Finset.sum_congr rfl fun b _ => hzero b, Finset.sum_const_zero,
        mul_zero]

/-! ## §6 — ★ MAIN: the discrete Weyl unitary averaging engine -/

/-- **★★★ r104.u: THE MATRIX UNITARY AVERAGING ENGINE ★★★**

    For EVERY `x ∈ M_n(ℂ)` (n ≥ 1):

    `(1/n²) • Σ_{a b : Fin n} (C^a·S^b) · x · (C^a·S^b)ᴴ
       = (trace x / n) • 1`.

    The n² discrete Weyl (generalized Pauli) unitaries `C^a·S^b`
    average every matrix to its normalized trace times the identity.
    Entrywise: the (i,j) entry of the (a,b) term factors as
    `(ω^i·star(ω^j))^a · x(i−b)(j−b)` (r104.l + r104.r), the a-sum is
    `n·[i=j]` by character orthogonality (r104.h), and on the
    diagonal the b-sum is `trace x` by cyclic reindexing.

    This is the engine of Glimm's 1960 UHF-simplicity argument:
    two-sided ideals absorb conjugation, so averaging maps any ideal
    element with nonzero trace to a nonzero scalar multiple of 1. -/
theorem matrix_unitary_average_eq_trace_smul_one
    (x : Matrix (Fin n) (Fin n) ℂ) :
    (1 / (n : ℂ) ^ 2) • ∑ a : Fin n, ∑ b : Fin n,
        (clockMatrix n ^ (a : ℕ) * shiftMatrix n ^ (b : ℕ)) * x
          * (clockMatrix n ^ (a : ℕ) * shiftMatrix n ^ (b : ℕ))ᴴ
      = (Matrix.trace x / n) • 1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  ext i j
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.one_apply,
    smul_eq_mul]
  have hterm : ∀ a b : Fin n,
      ((clockMatrix n ^ (a : ℕ) * shiftMatrix n ^ (b : ℕ)) * x
          * (clockMatrix n ^ (a : ℕ) * shiftMatrix n ^ (b : ℕ))ᴴ) i j
        = (substrateRoot n ^ (i : ℕ)
              * star (substrateRoot n ^ (j : ℕ))) ^ (a : ℕ)
            * x (i - b) (j - b) := by
    intro a b
    have hsplit : (clockMatrix n ^ (a : ℕ) * shiftMatrix n ^ (b : ℕ)) * x
          * (clockMatrix n ^ (a : ℕ) * shiftMatrix n ^ (b : ℕ))ᴴ
        = clockMatrix n ^ (a : ℕ)
            * (shiftMatrix n ^ (b : ℕ) * x * (shiftMatrix n ^ (b : ℕ))ᴴ)
            * (clockMatrix n ^ (a : ℕ))ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [hsplit, clockMatrix_pow_conj_apply, shiftMatrix_pow_conj_apply,
        pow_mul, pow_mul, star_pow]
    ring
  rw [Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => hterm a b,
      ← Finset.sum_mul_sum Finset.univ Finset.univ
        (fun a : Fin n => (substrateRoot n ^ (i : ℕ)
          * star (substrateRoot n ^ (j : ℕ))) ^ (a : ℕ))
        (fun b : Fin n => x (i - b) (j - b)),
      substrate_clock_character_sum]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, mul_one]
    have hre : ∑ b : Fin n, x (i - b) (i - b) = Matrix.trace x := by
      have h1 := Equiv.sum_comp (Equiv.subLeft i) (fun c : Fin n => x c c)
      simp only [Equiv.subLeft_apply] at h1
      rw [h1]
      rfl
    rw [hre, one_div, pow_two, mul_inv, mul_assoc,
        ← mul_assoc ((n : ℂ))⁻¹ ((n : ℂ)), inv_mul_cancel₀ hn, one_mul,
        div_eq_mul_inv, mul_comm (Matrix.trace x) ((n : ℂ))⁻¹]
  · rw [if_neg h, if_neg h, zero_mul, mul_zero, mul_zero]

/-! ## §7 — the M3.2 plug-in: absorbing sets swallow the averaged trace -/

/-- **★★★ r104.v: THE M3.2 PLUG-IN — TWO-SIDED-ABSORBING SETS
    CONTAIN THE AVERAGED TRACE ★★★**

    If `S ⊆ M_n(ℂ)` is closed under addition, under left and right
    multiplication by ARBITRARY matrices, and under ℂ-scalar
    multiplication (the matrix-level two-sided-ideal axioms), then

    `x ∈ S → (trace x / n) • 1 ∈ S`.

    Pure consequence of the averaging engine (r104.u): every term
    `(C^a S^b)·x·(C^a S^b)ᴴ` lies in S by left/right absorption, the
    (nonempty) double sum lies in S by additive closure, and the
    normalized average — which EQUALS `(trace x / n) • 1` — lies in
    S by scalar closure. This is exactly the step Glimm's simplicity
    argument feeds with a two-sided ideal of a matrix level. -/
theorem trace_smul_one_mem_of_two_sided_absorbing
    (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (h_add : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S)
    (h_left : ∀ (a : Matrix (Fin n) (Fin n) ℂ) (x : Matrix (Fin n) (Fin n) ℂ),
      x ∈ S → a * x ∈ S)
    (h_right : ∀ (a : Matrix (Fin n) (Fin n) ℂ) (x : Matrix (Fin n) (Fin n) ℂ),
      x ∈ S → x * a ∈ S)
    (h_smul : ∀ (c : ℂ) (x : Matrix (Fin n) (Fin n) ℂ), x ∈ S → c • x ∈ S)
    (x : Matrix (Fin n) (Fin n) ℂ) (hx : x ∈ S) :
    (Matrix.trace x / n) • (1 : Matrix (Fin n) (Fin n) ℂ) ∈ S := by
  haveI : Nonempty (Fin n) := ⟨0⟩
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  have hsum : (∑ a : Fin n, ∑ b : Fin n,
      (clockMatrix n ^ (a : ℕ) * shiftMatrix n ^ (b : ℕ)) * x
        * (clockMatrix n ^ (a : ℕ) * shiftMatrix n ^ (b : ℕ))ᴴ) ∈ S := by
    refine Finset.sum_induction_nonempty _ (· ∈ S)
      (fun u v hu hv => h_add u hu v hv) hne (fun a _ => ?_)
    refine Finset.sum_induction_nonempty _ (· ∈ S)
      (fun u v hu hv => h_add u hu v hv) hne (fun b _ => ?_)
    exact h_right _ _ (h_left _ _ hx)
  have hmem := h_smul (1 / (n : ℂ) ^ 2) _ hsum
  rw [matrix_unitary_average_eq_trace_smul_one] at hmem
  exact hmem

/-! ## §8 — r104 capstone -/

/-- **★★★ r104 SUBSTRATE MATRIX UNITARY AVERAGING CAPSTONE ★★★**

    Bundles the r104 substrate content, for every n ≥ 1:

      (W1) `clockMatrix_mem_unitaryGroup` — the clock matrix C is
           unitary.
      (W2) `shiftMatrix_mem_unitaryGroup` — the shift matrix S is
           unitary.
      (W3) `clockShiftWord_mem_unitaryGroup` — every word C^a·S^b is
           unitary.
      (W4) Stage A `clock_average_eq_diagonalPart` — the clock
           average kills the off-diagonal.
      (W5) Stage B `shift_average_diagonal_eq_trace_smul_one` — the
           shift average equalizes the diagonal.
      (W6) **`matrix_unitary_average_eq_trace_smul_one`** — THE
           ENGINE: (1/n²)·Σ_{a,b}(C^aS^b)x(C^aS^b)ᴴ = (trace x/n)•1
           for EVERY x ∈ M_n(ℂ).
      (W7) **`trace_smul_one_mem_of_two_sided_absorbing`** — the
           M3.2 plug-in: matrix-level two-sided-absorbing sets
           contain the averaged trace scalar.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r104 supplies the finite-dimensional
    engine of the Glimm-simplicity route isolated by r103. Milestone
    M3.2 must transport (W7) through the substrate tower embeddings
    ι_k : M_{3^k}(ℂ) → M_{3^(k+1)}(ℂ) and the completion to feed the
    r103 hypothesis `∀ I : TwoSidedIdeal TimelessFieldCompletion,
    I = ⊥ ∨ I = ⊤`. -/
theorem r104_substrate_matrix_unitary_averaging_capstone :
    (∀ (n : ℕ) [NeZero n],
      clockMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
    (∀ (n : ℕ) [NeZero n],
      shiftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
    (∀ (n : ℕ) [NeZero n] (a b : ℕ),
      clockMatrix n ^ a * shiftMatrix n ^ b
        ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
    (∀ (n : ℕ) [NeZero n] (x : Matrix (Fin n) (Fin n) ℂ),
      (1 / (n : ℂ)) • ∑ a : Fin n,
          clockMatrix n ^ (a : ℕ) * x * (clockMatrix n ^ (a : ℕ))ᴴ
        = Matrix.diagonal (fun i => x i i)) ∧
    (∀ (n : ℕ) [NeZero n] (d : Fin n → ℂ),
      (1 / (n : ℂ)) • ∑ b : Fin n,
          shiftMatrix n ^ (b : ℕ) * Matrix.diagonal d
            * (shiftMatrix n ^ (b : ℕ))ᴴ
        = (Matrix.trace (Matrix.diagonal d) / n) • 1) ∧
    (∀ (n : ℕ) [NeZero n] (x : Matrix (Fin n) (Fin n) ℂ),
      (1 / (n : ℂ) ^ 2) • ∑ a : Fin n, ∑ b : Fin n,
          (clockMatrix n ^ (a : ℕ) * shiftMatrix n ^ (b : ℕ)) * x
            * (clockMatrix n ^ (a : ℕ) * shiftMatrix n ^ (b : ℕ))ᴴ
        = (Matrix.trace x / n) • 1) ∧
    (∀ (n : ℕ) [NeZero n] (S : Set (Matrix (Fin n) (Fin n) ℂ)),
      (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) →
      (∀ (a : Matrix (Fin n) (Fin n) ℂ) (x : Matrix (Fin n) (Fin n) ℂ),
        x ∈ S → a * x ∈ S) →
      (∀ (a : Matrix (Fin n) (Fin n) ℂ) (x : Matrix (Fin n) (Fin n) ℂ),
        x ∈ S → x * a ∈ S) →
      (∀ (c : ℂ) (x : Matrix (Fin n) (Fin n) ℂ), x ∈ S → c • x ∈ S) →
      ∀ x ∈ S, (Matrix.trace x / n) • (1 : Matrix (Fin n) (Fin n) ℂ) ∈ S) :=
  ⟨fun _ _ => clockMatrix_mem_unitaryGroup,
   fun _ _ => shiftMatrix_mem_unitaryGroup,
   fun _ _ a b => clockShiftWord_mem_unitaryGroup a b,
   fun _ _ x => clock_average_eq_diagonalPart x,
   fun _ _ d => shift_average_diagonal_eq_trace_smul_one d,
   fun _ _ x => matrix_unitary_average_eq_trace_smul_one x,
   fun _ _ S h_add h_left h_right h_smul x hx =>
     trace_smul_one_mem_of_two_sided_absorbing S h_add h_left h_right
       h_smul x hx⟩

/-! ## §9 — Axiom audit -/

#print axioms substrateRoot_isPrimitiveRoot
#print axioms substrateRoot_pow_n
#print axioms substrateRoot_ne_zero
#print axioms substrateRoot_norm
#print axioms substrateRoot_star
#print axioms substrateRoot_pow_star
#print axioms substrate_clock_character_sum
#print axioms clockMatrix_pow
#print axioms clockMatrix_mem_unitaryGroup
#print axioms clockMatrix_pow_conj_apply
#print axioms shiftMatrix_pow_apply
#print axioms shiftMatrix_pow_conjTranspose_apply
#print axioms shiftMatrix_mem_unitaryGroup
#print axioms clockShiftWord_mem_unitaryGroup
#print axioms shiftMatrix_pow_conj_apply
#print axioms clock_average_eq_diagonalPart
#print axioms shift_average_diagonal_eq_trace_smul_one
#print axioms matrix_unitary_average_eq_trace_smul_one
#print axioms trace_smul_one_mem_of_two_sided_absorbing
#print axioms r104_substrate_matrix_unitary_averaging_capstone

end SubstrateMatrixUnitaryAveraging
end PrincipiaTractalis
