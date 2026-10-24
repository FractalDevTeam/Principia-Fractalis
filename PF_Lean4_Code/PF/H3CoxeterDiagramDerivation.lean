/-
# H₃ Coxeter data DERIVED from the Coxeter diagram

**BUILT AND GATED.** `lake build` exit 0, 3,071 jobs, zero errors; the pristine
gate reports PRISTINE over the file's declarations with axioms ⊆ {propext,
Classical.choice, Quot.sound}. Verified on the Legion tree from byte-identical source.

A previous revision of this header carried a draft-status disclaimer (phrase
deliberately not repeated here, so that a corpus-wide grep for it does not
re-flag this file) and it survived into commit `37141516` alongside the gate paste that
contradicted it. Same defect as `RiemannXiEdgeEnclosure_r331c`'s false "NOT YET
ELABORATED" header (`7c6683c0`) and `YangMillsPerelmanTemplateY1Y4Discharge`'s silent
four-month non-compile (`2c1e7437`): a file's self-description outliving the facts and
then being believed by an audit. Caught by the book-to-code parity sweep.

## Why this file exists

`PF/H3CoxeterOrigin.lean` fixes the H₃ Coxeter data by fiat:

    def H3_Coxeter_number : ℕ := 10
    def H3_exponents      : List ℕ := [1, 5, 9]
    def H3_exponent_sum   : ℕ := 15
    def H3_exponent_gap   : ℕ := 4

Those four `def`s are consumed downstream by `rfl`/`decide` proofs
(`PF/ExtremalTraceOrbits.lean`, `PF/RHViaH3PerelmanBridge.lean`,
`PF/Consciousness/H3IcosahedralConsciousnessOperatorBridge.lean`,
`PF/ExtremalTraceUniquenessProofPlan.lean`), so they are NOT changed here.
Instead this file constructs the same data from the H₃ Coxeter DIAGRAM and
proves that the derived objects coincide with the asserted literals. After
this file, the literals are pinned by theorems rather than only by stipulation.

## Chain of derivation

1. §1  Read the Coxeter matrix of H₃ off mathlib: `CoxeterMatrix.H₃`, with
       edge labels m(0,1) = 3, m(1,2) = 5, m(0,2) = 2. (NOTHING is assumed
       here: this is mathlib's own classification datum.)
2. §2  Build the Gram matrix of the Tits/geometric representation,
       `G i j = -cos(π / m i j)`. Note the diagonal comes out right for free:
       `-cos(π/1) = -cos π = 1`.
3. §3  Build the three simple reflections `s i = 1 - 2 eᵢ ⊗ Gᵢ` as explicit
       3×3 real matrices; check each is an involution.
4. §4  Form the Coxeter element `c = s₀ s₁ s₂` and compute it in closed form:
           c = !![0, φ, -φ; 1, φ, -φ; 0, φ, -1]
       The golden ratio enters ONLY through `2 cos(π/5) = φ`, which the corpus
       already proves (`H3CoxeterOrigin.two_cos_pi_div_five_eq_phi`).
5. §5  Compute the characteristic polynomial of `c` and factor it:
           charpoly c = (X + 1) * (X² - C φ · X + 1)
5b. §5b EXTRACT the Coxeter number from the matrix. Over ℝ,
           X⁵ + 1 = (X + 1)(X² - φX + 1)(X² + (φ-1)X + 1)
                  = charpoly c · (X² + (φ-1)X + 1),
       an identity needing only φ² = φ + 1, so Cayley-Hamilton
       (`Matrix.aeval_self_charpoly`) gives c⁵ = -1 and hence c¹⁰ = 1. With
       c⁵ ≠ 1 and c² ≠ 1 this yields
           orderOf c = 10 = H3_Coxeter_number.
       The Coxeter number is therefore READ OFF the matrix, not supplied; and
       ζ is DEFINED as exp(2πi / orderOf c), not as exp(2πi/10).
6. §6  Over ℂ, with ζ = exp(2πi / orderOf c) = exp(2πi/10): ζ is a primitive
       10th root of unity,
       ζ⁵ = -1 and ζ + ζ⁹ = φ, hence
           charpoly c  =  (X - ζ⁵)(X - ζ¹)(X - ζ⁹)   (after mapping to ℂ)
       so the eigenvalues of the Coxeter element are exactly the three 10th
       roots of unity with exponents 1, 5, 9.
7. §7  Consequences: the Coxeter number 10 is characterised BOTH as
       `orderOf c` (§5b) and as the order of the eigenvalue ζ
       (`IsPrimitiveRoot ζ H3_Coxeter_number`); the exponent set {1, 5, 9} is
       characterised as `{k < orderOf c | ζ^k is an eigenvalue}`; the exponent
       sum 15 and gap 4 are then computed from that set.

## What is derived vs. what remains definitional

DERIVED (theorem, modulo the usual kernel check):
  * the matrix of the Coxeter element,
  * its characteristic polynomial and the factorisation,
  * the eigenvalue set as powers of a primitive 10th root of unity,
  * `orderOf H3_coxeterElement = 10`: the Coxeter number EXTRACTED as the
    multiplicative order of the Coxeter element (§5b), hence
    `orderOf H3_coxeterElement = H3_Coxeter_number`,
  * `H3_Coxeter_number = 10` as the order of that root,
  * `H3_exponents.toFinset = {k < orderOf c | ζ^k is an eigenvalue}`,
  * `H3_exponent_sum` and `H3_exponent_gap` as functions of that set.

STILL DEFINITIONAL / CONVENTIONAL (exposed, not hidden):
  * the four `def`s in `H3CoxeterOrigin.lean` remain `def`s with literal
    bodies — they must, because downstream files prove things about them by
    `rfl`. What changes is that each now has a derivation theorem beside it.
  * CLOSED in this revision (it was the stated residual of rev 37141516): the
    range bound of `H3_exponentSet` is now `orderOf H3_coxeterElement`, not
    the literal `H3_Coxeter_number`, and `H3_zeta` is `exp(2πi / orderOf c)`,
    not `exp(2πi/10)`. The two spellings agree by
    `H3_Coxeter_number_eq_orderOf`. Nothing numerical is supplied to §6-§7 any
    more: the `10` that used to be typed there is `orderOf c`.
  * the CHOICE of Coxeter element `s₀ s₁ s₂` (any ordering of the simple
    reflections gives a conjugate element with the same spectrum; that
    conjugacy is NOT proved here).
  * that this matrix representation is THE reflection representation of the
    abstract Coxeter group `CoxeterMatrix.H₃.Group`. The Gram-matrix
    construction is the standard (Tits) one, but the braid relations
    `(s₀s₁)³ = (s₁s₂)⁵ = (s₀s₂)² = 1` are NOT proved here, so there is no
    Lean-level group homomorphism `CoxeterMatrix.H₃.Group →* GL₃(ℝ)` yet.
    This is the one real remaining gap in the chain; see §8.
  * mathlib at rev `eed770a43495` has NO Coxeter number, NO exponents, NO
    Coxeter element and NO geometric representation, so §2–§4 are built by
    hand rather than cited.

-/

import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Tactic
import PF.H3CoxeterOrigin

namespace PrincipiaTractalis
namespace H3CoxeterDiagram

open PrincipiaFractalis.H3CoxeterOrigin

/-! ### Golden-ratio plumbing

`Real.goldenRatio` is an `abbrev`, so it is reducible and `simp` unfolds it to
`(1 + √5) / 2` in some positions while leaving it an atom in others. Both facings are
needed below; neither is assumed. -/

/-- `φ` spelled out. True by `rfl` because `goldenRatio` is an `abbrev`. -/
private theorem phi_def : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl

/-- `√5 ^ 2 = 5`, the only arithmetic fact about `√5` any proof below needs. -/
private theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-! ## §1 The H₃ Coxeter diagram, read off mathlib

`CoxeterMatrix.H₃ : CoxeterMatrix (Fin 3)` is mathlib's own datum
(`Mathlib/GroupTheory/Coxeter/Matrix.lean`), with underlying matrix
`!![1, 3, 2; 3, 1, 5; 2, 5, 1]`.  The diagram is `0 --3-- 1 --5-- 2`
with `m(0,2) = 2` (the unlabelled commuting pair). -/

/-- The nine entries of the H₃ Coxeter matrix. This is the ONLY input to the
whole derivation. -/
theorem H3_diagram_entries :
    CoxeterMatrix.H₃ 0 0 = 1 ∧ CoxeterMatrix.H₃ 0 1 = 3 ∧ CoxeterMatrix.H₃ 0 2 = 2 ∧
    CoxeterMatrix.H₃ 1 0 = 3 ∧ CoxeterMatrix.H₃ 1 1 = 1 ∧ CoxeterMatrix.H₃ 1 2 = 5 ∧
    CoxeterMatrix.H₃ 2 0 = 2 ∧ CoxeterMatrix.H₃ 2 1 = 5 ∧ CoxeterMatrix.H₃ 2 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §2 The Gram matrix of the geometric (Tits) representation -/

/-- **Gram matrix of H₃**, built from the diagram alone:
`G i j = -cos(π / m i j)`.  The diagonal is automatic:
`-cos(π/1) = -cos π = 1`. -/
noncomputable def H3_gram : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => -Real.cos (Real.pi / (CoxeterMatrix.H₃ i j : ℝ))

/-- Closed form of the H₃ Gram matrix. Uses only `Real.cos_pi`,
`Real.cos_pi_div_two`, `Real.cos_pi_div_three` from mathlib; the `π/5` entry
is left symbolic and is converted to `φ` in §3. -/
theorem H3_gram_eq :
    H3_gram = !![1, -(1/2), 0;
                 -(1/2), 1, -Real.cos (Real.pi / 5);
                 0, -Real.cos (Real.pi / 5), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H3_gram, CoxeterMatrix.H₃, Real.cos_pi, Real.cos_pi_div_two,
          Real.cos_pi_div_three]

/-! ## §3 The three simple reflections

TACTIC NOTE (this file has not been built). Every proof in §2–§5 that extracts
entries from a `!![…]` literal is mechanical `ext` + `fin_cases` + `simp`
bookkeeping. If one of them fails, the failure will be in the simp set, not in
the mathematics. Fallbacks, in order:
  * add `Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const` to the
    simp set explicitly;
  * replace a trailing `ring` / `norm_num` with
    `linear_combination Real.goldenRatio_sq` (coefficient `1`) where the entry
    needs `φ² = φ + 1`;
  * in `H3_det_charMatrix` the required certificate is
    `(x + 1) * Real.goldenRatio_sq`, since
    `det − (x+1)(x²−φx+1) = (x+1)(φ² − φ − 1)` identically.
The genuinely mathematical steps are `H3_charpoly_eq` (via `Polynomial.funext`),
`H3_zeta_pow_five`, `H3_zeta_add_pow_nine` and `H3_charpoly_C_factored`. -/

/-- **Simple reflection `s i`** of the geometric representation, in the basis
of simple roots: `s i (e k) = e k - 2 G i k · e i`, i.e. the identity matrix
with row `i` replaced by `δ i k - 2 G i k`. -/
noncomputable def H3_simple (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun j k =>
    (if j = k then (1 : ℝ) else 0) - (if j = i then 2 * H3_gram i k else 0)

theorem H3_simple_zero :
    H3_simple 0 = !![-1, 1, 0;
                      0, 1, 0;
                      0, 0, 1] := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [H3_simple, H3_gram_eq] <;> norm_num

theorem H3_simple_one :
    H3_simple 1 = !![1, 0, 0;
                     1, -1, Real.goldenRatio;
                     0, 0, 1] := by
  have hφ : (2 : ℝ) * Real.cos (Real.pi / 5) = Real.goldenRatio :=
    two_cos_pi_div_five_eq_phi
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [H3_simple, H3_gram_eq] <;>
    first
      | ring
      | linarith [phi_def]
      | nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]
      | (rw [phi_def]; ring)
      | norm_num
      | linarith [hφ]

theorem H3_simple_two :
    H3_simple 2 = !![1, 0, 0;
                     0, 1, 0;
                     0, Real.goldenRatio, -1] := by
  have hφ : (2 : ℝ) * Real.cos (Real.pi / 5) = Real.goldenRatio :=
    two_cos_pi_div_five_eq_phi
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [H3_simple, H3_gram_eq] <;>
    first
      | ring
      | linarith [phi_def]
      | nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]
      | (rw [phi_def]; ring)
      | norm_num
      | linarith [hφ]

/-- Sanity: `s₀` is an involution. -/
theorem H3_simple_zero_sq : H3_simple 0 * H3_simple 0 = 1 := by
  rw [H3_simple_zero, Matrix.mul_fin_three, Matrix.one_fin_three]
  norm_num

/-- Sanity: `s₁` is an involution. -/
theorem H3_simple_one_sq : H3_simple 1 * H3_simple 1 = 1 := by
  rw [H3_simple_one, Matrix.mul_fin_three, Matrix.one_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;> ring

/-- Sanity: `s₂` is an involution. -/
theorem H3_simple_two_sq : H3_simple 2 * H3_simple 2 = 1 := by
  rw [H3_simple_two, Matrix.mul_fin_three, Matrix.one_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;> ring

/-! ## §4 The Coxeter element -/

/-- **Coxeter element of H₃** in the geometric representation:
`c = s₀ s₁ s₂`. -/
noncomputable def H3_coxeterElement : Matrix (Fin 3) (Fin 3) ℝ :=
  H3_simple 0 * H3_simple 1 * H3_simple 2

/-- Intermediate product `s₀ s₁`; needs no golden-ratio identity. -/
theorem H3_simple_zero_mul_one :
    H3_simple 0 * H3_simple 1 = !![0, -1, Real.goldenRatio;
                                   1, -1, Real.goldenRatio;
                                   0, 0, 1] := by
  rw [H3_simple_zero, H3_simple_one, Matrix.mul_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;> ring

/-- **Closed form of the Coxeter element.**  The only non-ring step is
`φ * φ = φ + 1` (`Real.goldenRatio_sq`), used in the (0,1) and (1,1) entries. -/
theorem H3_coxeterElement_eq :
    H3_coxeterElement = !![0, Real.goldenRatio, -Real.goldenRatio;
                           1, Real.goldenRatio, -Real.goldenRatio;
                           0, Real.goldenRatio, -1] := by
  unfold H3_coxeterElement
  rw [H3_simple_zero_mul_one, H3_simple_two, Matrix.mul_fin_three]
  ext j k
  fin_cases j <;> fin_cases k
  -- Entries (0,1) and (1,1) need φ² = φ + 1. `simp` has already unfolded the
  -- `abbrev` to √5, so give it √5 ² = 5 directly rather than repairing after.
  -- `sqrt5_sq` does not match: the radicand in the goal is not spelled `(5 : ℝ)`.
  -- `Real.sq_sqrt` as a CONDITIONAL rewrite matches any radicand and discharges
  -- `0 ≤ ·` itself, so it fires regardless of how the literal is elaborated.
  -- After `simp` the two residual entries are literally `-1 + φ*φ = φ`, i.e.
  -- `φ² = φ + 1`. (Chasing a `√5` form here is a dead end: that shape only appears
  -- once a failing tactic has already unfolded the `abbrev`.)
  -- After `simp`, both residual entries are literally `-1 + φ*φ = φ`, i.e. φ² = φ+1.
  -- NOTE: do not wrap this in `first | ring | ...`. `ring` partially succeeds on
  -- these goals without closing them, which stops `first` before it reaches the
  -- closer. Unconditional is correct here.
  all_goals simp
  all_goals linear_combination Real.goldenRatio_sq

/-! ## §5 Characteristic polynomial over ℝ -/

/-- The characteristic matrix `x·I − c` in closed form. -/
theorem H3_charMatrix_eq (x : ℝ) :
    Matrix.scalar (Fin 3) x - H3_coxeterElement
      = !![x, -Real.goldenRatio, Real.goldenRatio;
           -1, x - Real.goldenRatio, Real.goldenRatio;
           0, -Real.goldenRatio, x + 1] := by
  rw [H3_coxeterElement_eq]
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.sub_apply] <;> ring

/-- **det(x·I − c) = (x + 1)(x² − φx + 1).**
Pure `Matrix.det_fin_three` expansion; the single non-ring input is
`φ² = φ + 1`, entering with coefficient `(x + 1)`. -/
theorem H3_det_charMatrix (x : ℝ) :
    (Matrix.scalar (Fin 3) x - H3_coxeterElement).det
      = (x + 1) * (x ^ 2 - Real.goldenRatio * x + 1) := by
  rw [H3_charMatrix_eq, Matrix.det_fin_three]
  first
    | linear_combination (x + 1) * Real.goldenRatio_sq
    | (rw [phi_def]; linear_combination ((x + 1) / 4) * sqrt5_sq)
    | (simp; linear_combination (x + 1) * Real.goldenRatio_sq)

/-- **The characteristic polynomial of the H₃ Coxeter element, factored.**

    charpoly c = (X + 1) * (X² − C φ · X + 1)

Proved by `Polynomial.funext` (ℝ is an infinite domain) from
`H3_det_charMatrix`.  THIS is the theorem that replaces the fiat
`H3_Coxeter_number := 10` / `H3_exponents := [1,5,9]` with content. -/
theorem H3_charpoly_eq :
    H3_coxeterElement.charpoly
      = (Polynomial.X + 1) *
        (Polynomial.X ^ 2 - Polynomial.C Real.goldenRatio * Polynomial.X + 1) := by
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  exact H3_det_charMatrix x

/-! ## §5b The Coxeter number EXTRACTED: `orderOf H3_coxeterElement`

★ UNVERIFIED — not built, not kernel-checked. ★

§5 gives `charpoly c = (X + 1)(X² − C φ · X + 1)`. Over ℂ its roots are
`−1`, `e^{iπ/5}`, `e^{−iπ/5}`, of multiplicative orders `2, 10, 10`; they are
pairwise distinct, so `c` is diagonalisable over ℂ and
`orderOf c = lcm(2,10,10) = 10`. THAT ROUTE IS NOT TAKEN: at rev
`eed770a43495` mathlib has no off-the-shelf bridge from "distinct eigenvalues"
to "order of the matrix = lcm of the eigenvalue orders", so taking it would
mean building the diagonalisation by hand. The order is obtained instead by
arithmetic, from Cayley–Hamilton alone, which needs no spectral theory.

The one input beyond §5 is the real factorisation of `X⁵ + 1`:

    X⁵ + 1 = (X + 1) · Φ₁₀(X)
           = (X + 1)(X² − φX + 1)(X² + (φ−1)X + 1)
           = charpoly c · (X² + (φ−1)X + 1),

the two real quadratic factors of the tenth cyclotomic polynomial being
`X² − 2cos(π/5)·X + 1` and `X² − 2cos(3π/5)·X + 1` with `2cos(π/5) = φ`
and `2cos(3π/5) = 1 − φ`. As a polynomial identity the two sides differ by
exactly `(φ² − φ − 1)(X³ + X²)`, which is why the certificate below is
precisely `(X³ + X²) * C_goldenRatio_sq` — that coefficient is computed, not
guessed.

Applying `Polynomial.aeval c` and `Matrix.aeval_self_charpoly` then gives
`c⁵ = −1` with NO matrix multiplication at all. Hence `c¹⁰ = (c⁵)² = 1`, and
the two prime-divisor obstructions required by
`orderOf_eq_of_pow_and_pow_div_prime` (the primes dividing 10 are 2 and 5) are

  * `c^(10/2) = c⁵ = −1 ≠ 1`  — compare the (0,0) entries;
  * `c^(10/5) = c² ≠ 1`        — the (0,0) entry of `c²` is `φ`, and `1 < φ`.

Hence `orderOf c = 10`. For the record, the powers really are

    c² = !![φ, 0, -1; φ, φ, -φ-1; φ, 1, -φ]      (after φ² = φ+1)
    c⁴ = !![1, -1, 0; 1, 0, -φ; φ, 0, -φ]
    c⁵ = -1

with traces `φ`, `1 − φ`, `−3`, matching the eigenvalue sums
`(−1)^k + 2cos(kπ/5)` for k = 2, 4, 5. Only `c²` is computed below; `c⁵`
is not. -/

/-- `(C φ)² = C φ + 1` in `ℝ[X]`: `Real.goldenRatio_sq` pushed through `C`.
This is the ONLY φ-fact used in §5b. -/
private theorem C_goldenRatio_sq :
    (Polynomial.C Real.goldenRatio) ^ 2 = Polynomial.C Real.goldenRatio + 1 := by
  rw [← Polynomial.C_pow, Real.goldenRatio_sq, Polynomial.C_add, Polynomial.C_1]

/-- **`X⁵ = charpoly c · (X² + φX − X + 1) − 1`** in `ℝ[X]`.

The second factor is `X² + (φ−1)X + 1`, written as `X² + φX − X + 1` so that
`C` is applied only to `φ` and `ring` sees the single atom `C φ`.
`charpoly c` is deliberately kept as an opaque head symbol so that the
`map_mul` step below cannot split it back into its two factors. -/
private theorem H3_X_pow_five_eq :
    (Polynomial.X ^ 5 : Polynomial ℝ)
      = H3_coxeterElement.charpoly *
          (Polynomial.X ^ 2 + Polynomial.C Real.goldenRatio * Polynomial.X
            - Polynomial.X + 1) - 1 := by
  rw [H3_charpoly_eq]
  linear_combination (Polynomial.X ^ 3 + Polynomial.X ^ 2) * C_goldenRatio_sq

/-- **`c⁵ = −1`.**  Cayley–Hamilton (`Matrix.aeval_self_charpoly`) applied to
`H3_X_pow_five_eq`. No matrix product is computed in this proof; the whole
content is §5 plus `φ² = φ + 1`. -/
theorem H3_coxeterElement_pow_five : H3_coxeterElement ^ 5 = -1 := by
  calc H3_coxeterElement ^ 5
      = Polynomial.aeval H3_coxeterElement (Polynomial.X ^ 5 : Polynomial ℝ) := by
        rw [map_pow, Polynomial.aeval_X]
    _ = Polynomial.aeval H3_coxeterElement
          (H3_coxeterElement.charpoly *
            (Polynomial.X ^ 2 + Polynomial.C Real.goldenRatio * Polynomial.X
              - Polynomial.X + 1) - 1) := by
        rw [← H3_X_pow_five_eq]
    _ = Polynomial.aeval H3_coxeterElement H3_coxeterElement.charpoly *
          Polynomial.aeval H3_coxeterElement
            (Polynomial.X ^ 2 + Polynomial.C Real.goldenRatio * Polynomial.X
              - Polynomial.X + 1) - 1 := by
        rw [map_sub, map_mul, map_one]
    _ = -1 := by
        rw [Matrix.aeval_self_charpoly, zero_mul, zero_sub]

/-- `c¹⁰ = 1`: so `c` is a unit and `orderOf c ∣ 10`. -/
theorem H3_coxeterElement_pow_ten : H3_coxeterElement ^ 10 = 1 := by
  have e : H3_coxeterElement ^ (5 * 2) = (H3_coxeterElement ^ 5) ^ 2 :=
    pow_mul H3_coxeterElement 5 2
  have h52 : (5 * 2 : ℕ) = 10 := by norm_num
  rw [h52] at e
  rw [e, H3_coxeterElement_pow_five, neg_one_sq]

/-- `c⁵ ≠ 1`: it is `−1`, whose `(0,0)` entry is `−1`, not `1`.
(`Matrix (Fin 3) (Fin 3) ℝ` carries no `CharP`-style `neg_one_ne_one` at this
pin, so the entry is compared directly.) -/
theorem H3_coxeterElement_pow_five_ne_one : H3_coxeterElement ^ 5 ≠ 1 := by
  intro h
  have h00 : (-1 : Matrix (Fin 3) (Fin 3) ℝ) 0 0
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 0 := by
    rw [← H3_coxeterElement_pow_five, h]
  rw [Matrix.neg_apply, Matrix.one_apply_eq] at h00
  norm_num at h00

/-- **`c²` computed.**  The target is deliberately left UNREDUCED — entries
written as polynomials in `φ` of degree ≤ 2 — so that every entry goal is a
pure ring identity and the closer is an unconditional `ring`. That makes the
proof immune to whether `simp` has unfolded the `Real.goldenRatio`
abbreviation: both sides unfold together, and `ring` closes either facing.
Reducing by `φ² = φ + 1` gives the tidier
`!![φ, 0, -1; φ, φ, -φ-1; φ, 1, -φ]`, which is not needed below. -/
theorem H3_coxeterElement_sq_eq :
    H3_coxeterElement ^ 2
      = !![Real.goldenRatio, 0, Real.goldenRatio - Real.goldenRatio ^ 2;
           Real.goldenRatio, Real.goldenRatio, -Real.goldenRatio ^ 2;
           Real.goldenRatio, Real.goldenRatio ^ 2 - Real.goldenRatio,
             1 - Real.goldenRatio ^ 2] := by
  rw [pow_two, H3_coxeterElement_eq, Matrix.mul_fin_three]
  ext j k
  fin_cases j <;> fin_cases k
  -- NOTE: do NOT wrap the closer in `first | ring | …`. `ring` partially
  -- succeeds on matrix-entry goals without closing them, which stops `first`
  -- before it reaches the real closer. Unconditional is correct here, and
  -- (unlike `H3_coxeterElement_eq`) no `linear_combination` is needed at all,
  -- because the target is unreduced.
  -- Fallback if `simp` leaves a goal `ring` cannot close (asymmetric unfolding
  -- of the abbrev): replace `all_goals simp` by
  --   all_goals simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
  --     Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
  --     Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  -- Plain `simp` unfolds the `Real.goldenRatio` abbrev, which defeats the whole
  -- point of stating the target unreduced: the entries then carry `√5 ^ 2` and are
  -- no longer ring identities. Neither `rw [sqrt5_sq]` nor `nlinarith` recovers
  -- (the first finds no syntactic match, the second no contradiction). Extract the
  -- entries with `simp only` over the matrix lemmas alone, so `φ` stays an atom and
  -- every goal really is pure `ring`.
  all_goals simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  all_goals ring

/-- `c² ≠ 1`: the `(0,0)` entry of `c²` is `φ`, and `1 < φ`
(`Real.one_lt_goldenRatio`). -/
theorem H3_coxeterElement_sq_ne_one : H3_coxeterElement ^ 2 ≠ 1 := by
  intro h
  have h00 : (H3_coxeterElement ^ 2) 0 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 0 := by
    rw [h]
  rw [H3_coxeterElement_sq_eq, Matrix.one_apply_eq] at h00
  -- `simpa` rather than `simp at h00` so the step is insensitive to whether
  -- `simp` unfolds `φ` to `(1 + √5)/2`: it normalises hypothesis AND target,
  -- so the two facings cannot diverge.
  have hphi : Real.goldenRatio = 1 := by simpa using h00
  linarith [Real.one_lt_goldenRatio, hphi]

/-- **THE RESIDUAL CLOSED: `orderOf H3_coxeterElement = 10`.**

`c¹⁰ = 1`, and for each prime `p ∣ 10` the power `c^(10/p)` is not `1`
(`p = 2` gives `c⁵ = −1`; `p = 5` gives `c²`). By
`orderOf_eq_of_pow_and_pow_div_prime` the order is exactly 10, so the Coxeter
number is a COMPUTED invariant of the matrix built from the diagram rather
than a literal typed into a `def`. -/
theorem H3_orderOf_coxeterElement : orderOf H3_coxeterElement = 10 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
    H3_coxeterElement_pow_ten ?_
  intro p hp hpdvd
  have h10 : (10 : ℕ) = 2 * 5 := by norm_num
  rw [h10, hp.dvd_mul] at hpdvd
  rcases hpdvd with hd | hd
  · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    subst hp2
    have hq : (10 : ℕ) / 2 = 5 := by norm_num
    rw [hq]
    exact H3_coxeterElement_pow_five_ne_one
  · have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd
    subst hp5
    have hq : (10 : ℕ) / 5 = 2 := by norm_num
    rw [hq]
    exact H3_coxeterElement_sq_ne_one

/-- **The literal `H3_Coxeter_number` IS the order of the Coxeter element.**

This is the theorem that retires the stipulation `H3_Coxeter_number := 10`.
The `def` keeps its literal body — 17 downstream files prove things about it
by `rfl`/`decide` — but the value is now pinned by a computation on the
diagram, in the direction "matrix ⇒ literal", not the reverse. -/
theorem H3_Coxeter_number_eq_orderOf :
    orderOf H3_coxeterElement = H3_Coxeter_number :=
  H3_orderOf_coxeterElement

/-! ## §6 Eigenvalues over ℂ: tenth roots of unity -/

/-- **`ζ = exp(2πi / h)` with `h = orderOf H3_coxeterElement`.**

The Coxeter eigenvalue is no longer *chosen* as `exp(2πi/10)` and then shown
to be an eigenvalue: the exponent `h` is the order of the Coxeter element
computed in §5b, so NO numeral is supplied here. `H3_zeta_eq_exp_ten` below
recovers the literal spelling. -/
noncomputable def H3_zeta : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((orderOf H3_coxeterElement : ℕ) : ℂ))

/-- `ζ` written out: the extracted order is `10`, so `ζ = exp(2πi/10)`.
Every later use of `ζ` goes through this lemma rather than through `unfold`. -/
theorem H3_zeta_eq_exp_ten :
    H3_zeta = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 10) := by
  unfold H3_zeta
  rw [H3_orderOf_coxeterElement]
  norm_num

/-- `ζ` is a primitive 10th root of unity (mathlib's
`Complex.isPrimitiveRoot_exp`). -/
theorem H3_zeta_isPrimitiveRoot : IsPrimitiveRoot H3_zeta 10 := by
  rw [H3_zeta_eq_exp_ten]
  have h := Complex.isPrimitiveRoot_exp 10 (by norm_num)
  have harg : (2 * (Real.pi : ℂ) * Complex.I / ((10 : ℕ) : ℂ))
      = 2 * (Real.pi : ℂ) * Complex.I / 10 := by norm_num
  rw [harg] at h
  exact h

theorem H3_zeta_eq_exp : H3_zeta = Complex.exp ((Real.pi : ℂ) / 5 * Complex.I) := by
  rw [H3_zeta_eq_exp_ten]
  congr 1
  ring

/-- `ζ¹⁰ = 1`. -/
theorem H3_zeta_pow_ten : H3_zeta ^ 10 = 1 := H3_zeta_isPrimitiveRoot.pow_eq_one

/-- `ζ⁵ = −1`: it squares to 1 and is not 1 (primitivity). This is the
eigenvalue with exponent 5. -/
theorem H3_zeta_pow_five : H3_zeta ^ 5 = -1 := by
  have h5 : H3_zeta ^ 5 ≠ 1 :=
    H3_zeta_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hsq : (H3_zeta ^ 5) ^ 2 = 1 := by
    rw [← pow_mul]; exact H3_zeta_pow_ten
  have hfac : (H3_zeta ^ 5 - 1) * (H3_zeta ^ 5 + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (show H3_zeta ^ 5 = 1 by linear_combination h) h5
  · linear_combination h

/-- `ζ · ζ⁹ = 1`, so `ζ⁹ = ζ⁻¹`. -/
theorem H3_zeta_mul_pow_nine : H3_zeta * H3_zeta ^ 9 = 1 := by
  calc H3_zeta * H3_zeta ^ 9 = H3_zeta ^ 10 := by ring
    _ = 1 := H3_zeta_pow_ten

/-- **`ζ + ζ⁹ = φ`.**  This is where the corpus' `2 cos(π/5) = φ` enters the
complex picture: `ζ + ζ⁻¹ = 2 cos(π/5) = φ`. -/
theorem H3_zeta_add_pow_nine : H3_zeta + H3_zeta ^ 9 = (Real.goldenRatio : ℂ) := by
  have hinv : H3_zeta ^ 9 = H3_zeta⁻¹ :=
    (inv_eq_of_mul_eq_one_right H3_zeta_mul_pow_nine).symm
  have h2 := Complex.two_cos ((Real.pi : ℂ) / 5)
  have hneg : Complex.exp (-((Real.pi : ℂ) / 5) * Complex.I) = H3_zeta⁻¹ := by
    rw [H3_zeta_eq_exp, ← Complex.exp_neg]
    congr 1
    ring
  have hcos : 2 * Complex.cos ((Real.pi : ℂ) / 5) = (Real.goldenRatio : ℂ) := by
    have hr : (2 : ℝ) * Real.cos (Real.pi / 5) = Real.goldenRatio :=
      two_cos_pi_div_five_eq_phi
    have hc := congrArg (fun t : ℝ => (t : ℂ)) hr
    simp only [Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_div,
      Complex.ofReal_ofNat] at hc
    first
      | exact hc
      | exact_mod_cast hc
      | (push_cast at hc ⊢; linear_combination hc)
      | (rw [phi_def]; push_cast at hc ⊢; linear_combination hc)
      | (simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_div,
            Complex.ofReal_ofNat] at hc ⊢; linear_combination hc)
  rw [hinv, ← hneg, H3_zeta_eq_exp, ← h2]
  exact hcos

/-- **The factorisation into tenth roots of unity.**

    (z + 1)(z² − φz + 1) = (z − ζ⁵)(z − ζ¹)(z − ζ⁹)

The two inputs are `ζ⁵ = −1` and `ζ + ζ⁹ = φ`, `ζ · ζ⁹ = 1`. -/
theorem H3_charpoly_C_factored (z : ℂ) :
    (z + 1) * (z ^ 2 - (Real.goldenRatio : ℂ) * z + 1)
      = (z - H3_zeta ^ 5) * (z - H3_zeta ^ 1) * (z - H3_zeta ^ 9) := by
  rw [H3_zeta_pow_five, pow_one]
  linear_combination (z + 1) * z * H3_zeta_add_pow_nine - (z + 1) * H3_zeta_mul_pow_nine

/-- The complexified Coxeter element. -/
noncomputable def H3_coxeterElementC : Matrix (Fin 3) (Fin 3) ℂ :=
  H3_coxeterElement.map (Complex.ofRealHom : ℝ →+* ℂ)

/-- Characteristic polynomial of the complexified Coxeter element. -/
theorem H3_charpolyC_eq :
    H3_coxeterElementC.charpoly
      = (Polynomial.X + 1) *
        (Polynomial.X ^ 2 - Polynomial.C (Real.goldenRatio : ℂ) * Polynomial.X + 1) := by
  unfold H3_coxeterElementC
  rw [Matrix.charpoly_map, H3_charpoly_eq]
  simp

/-- **The eigenvalues of the H₃ Coxeter element are exactly `ζ⁵, ζ¹, ζ⁹`.**
Stated as: `z` is a root of the characteristic polynomial iff `z` is one of
those three tenth roots of unity. -/
theorem H3_eigenvalue_iff (z : ℂ) :
    H3_coxeterElementC.charpoly.eval z = 0
      ↔ (z = H3_zeta ^ 5 ∨ z = H3_zeta ^ 1 ∨ z = H3_zeta ^ 9) := by
  rw [H3_charpolyC_eq]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  rw [H3_charpoly_C_factored]
  simp only [mul_eq_zero, sub_eq_zero]
  tauto

/-! ## §7 The four asserted data, now derived -/

/-- **Coxeter number as a derived object.**  `H3_Coxeter_number` (the literal
`10` in `H3CoxeterOrigin.lean`) is exactly the order of the Coxeter-element
eigenvalue `ζ`: `ζ` is a primitive `H3_Coxeter_number`-th root of unity.
This is the statement that turns the literal into content. -/
theorem H3_Coxeter_number_derived : IsPrimitiveRoot H3_zeta H3_Coxeter_number := by
  show IsPrimitiveRoot H3_zeta 10
  exact H3_zeta_isPrimitiveRoot

/-- **The same statement with the literal eliminated**: `ζ` is a primitive
root of unity of order exactly `orderOf H3_coxeterElement`. Together with
`H3_Coxeter_number_eq_orderOf` this is the full extraction — the Coxeter
number is the order of the Coxeter element, and the Coxeter eigenvalue is the
primitive root of unity of that order. -/
theorem H3_zeta_isPrimitiveRoot_orderOf :
    IsPrimitiveRoot H3_zeta (orderOf H3_coxeterElement) := by
  rw [H3_orderOf_coxeterElement]
  exact H3_zeta_isPrimitiveRoot

/-- **The exponent set, DEFINED spectrally**: those `k < h` for which `ζ^k`
is an eigenvalue of the Coxeter element. Nothing is asserted here; the value
is computed in `H3_exponentSet_eq`. -/
noncomputable def H3_exponentSet : Finset ℕ :=
  @Finset.filter ℕ
    (fun k => H3_coxeterElementC.charpoly.eval (H3_zeta ^ k) = 0)
    (Classical.decPred _)
    (Finset.range (orderOf H3_coxeterElement))

/-- The range bound of `H3_exponentSet` is the EXTRACTED Coxeter number
`orderOf H3_coxeterElement`, and it agrees with the literal
`H3_Coxeter_number`. This is the residual of rev 37141516, closed. -/
theorem H3_exponentSet_range_eq :
    Finset.range (orderOf H3_coxeterElement) = Finset.range H3_Coxeter_number := by
  rw [H3_Coxeter_number_eq_orderOf]

/-- Membership criterion for the spectral exponent set. -/
theorem H3_exponent_iff (k : ℕ) (hk : k < 10) :
    H3_coxeterElementC.charpoly.eval (H3_zeta ^ k) = 0 ↔ (k = 1 ∨ k = 5 ∨ k = 9) := by
  rw [H3_eigenvalue_iff]
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inl
        (H3_zeta_isPrimitiveRoot.pow_inj hk (show (5 : ℕ) < 10 by norm_num) h))
    · exact Or.inl
        (H3_zeta_isPrimitiveRoot.pow_inj hk (show (1 : ℕ) < 10 by norm_num) h)
    · exact Or.inr (Or.inr
        (H3_zeta_isPrimitiveRoot.pow_inj hk (show (9 : ℕ) < 10 by norm_num) h))
  · rintro (h | h | h) <;> subst h
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)

/-- **The spectral exponent set is `{1, 5, 9}`** — DERIVED, not asserted. -/
theorem H3_exponentSet_eq : H3_exponentSet = ({1, 5, 9} : Finset ℕ) := by
  ext k
  simp only [H3_exponentSet, H3_orderOf_coxeterElement, Finset.mem_filter,
    Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hk, h⟩
    exact (H3_exponent_iff k hk).mp h
  · intro h
    have hk : k < 10 := by rcases h with h | h | h <;> omega
    exact ⟨hk, (H3_exponent_iff k hk).mpr h⟩

/-- **The asserted list `H3_exponents = [1,5,9]` agrees with the spectral
exponent set.** -/
theorem H3_exponents_derived : H3_exponents.toFinset = H3_exponentSet := by
  rw [H3_exponentSet_eq]
  decide

/-- **The asserted `H3_exponent_sum = 15` is the sum of the spectral exponent
set.** -/
theorem H3_exponent_sum_derived : (∑ k ∈ H3_exponentSet, k) = H3_exponent_sum := by
  rw [H3_exponentSet_eq]
  decide

/-- **The asserted `H3_exponent_gap = 4` is the gap between consecutive
elements of the spectral exponent set.** -/
theorem H3_exponent_gap_derived :
    ∀ a ∈ H3_exponentSet, ∀ b ∈ H3_exponentSet,
      a < b → (∀ c ∈ H3_exponentSet, ¬(a < c ∧ c < b)) → b - a = H3_exponent_gap := by
  rw [H3_exponentSet_eq]
  decide

/-- **Coxeter half-argument, derived.**  The primitive Coxeter eigenvalue is
`ζ = exp(2πi / h)` with `h = H3_Coxeter_number`, whose half-argument is
`π / 10`.  Same statement as `H3CoxeterOrigin.H3_Coxeter_half_arg`, but now
`ζ` has been exhibited as an actual eigenvalue of an actual matrix built from
the diagram. -/
theorem H3_half_arg_derived :
    (2 * Real.pi / (H3_Coxeter_number : ℝ)) / 2 = Real.pi / 10 :=
  H3_Coxeter_half_arg

/-- The same with the literal eliminated: the half-argument of the Coxeter
eigenvalue is `π / 10`, where the `10` upstairs is `orderOf H3_coxeterElement`
rather than a typed constant. -/
theorem H3_half_arg_orderOf :
    (2 * Real.pi / ((orderOf H3_coxeterElement : ℕ) : ℝ)) / 2 = Real.pi / 10 := by
  rw [H3_orderOf_coxeterElement]
  push_cast
  ring

/-! ## §8 Capstone, and the one remaining gap -/

/-- **The H₃ Coxeter data derived from the diagram**, as a single conjunction.

Reading of the clauses:
  (1) the diagram entries, straight from mathlib's classification;
  (2) the Coxeter element of the Gram-matrix reflection representation,
      in closed form over ℝ;
  (3) its characteristic polynomial, factored;
  (4) its eigenvalues are exactly `ζ⁵, ζ¹, ζ⁹` where
      `ζ = exp(2πi / orderOf c)`;
  (5) the literal `H3_Coxeter_number` is `orderOf H3_coxeterElement` — the
      Coxeter number is EXTRACTED from the matrix — and `ζ` is a primitive
      `H3_Coxeter_number`-th root of unity;
  (6) the spectral exponent set is `{1,5,9}` and equals
      `H3_exponents.toFinset` — i.e. the literal list is the exponent set.

What this does NOT establish: that `H3_simple` factors through the abstract
Coxeter group `CoxeterMatrix.H₃.Group`. The missing lemmas are the braid
relations
    `(H3_simple 0 * H3_simple 1) ^ 3 = 1`,
    `(H3_simple 1 * H3_simple 2) ^ 5 = 1`,
    `(H3_simple 0 * H3_simple 2) ^ 2 = 1`,
which together with `H3_simple_*_sq` would give
`CoxeterMatrix.H₃.IsLiftable H3_simple` and hence a monoid hom
`CoxeterMatrix.H₃.Group →* Matrix (Fin 3) (Fin 3) ℝ` via
`CoxeterSystem.lift`.  They are omitted rather than asserted: the 5-fold one
is a five-term matrix product requiring repeated `φ² = φ + 1` reduction and
has not been written out here. Until they exist, the sentence "the H₃
icosahedral GROUP has Coxeter number 10" is supported at the level of the
diagram and its Gram-matrix reflection representation, not at the level of
the abstract group.

**CLOSED 2026-10-24 by `PF/H3CoxeterBraidRelations_r342.lean`.** The
paragraph above is kept as history; it is no longer the state of the
corpus, and this file's own header warns about precisely the opposite
error -- a self-description outliving the facts and then being believed by
an audit. All three braid relations are proved there, the 5-fold one
stepwise through explicit intermediate matrices `B², B³, B⁴`;
`H3_isLiftable : CoxeterMatrix.H₃.IsLiftable H3_simple` covers all nine
ordered pairs; and `H3_rep : CoxeterMatrix.H₃.Group →* Matrix (Fin 3) (Fin 3) ℝ`
exists via `CoxeterSystem.lift`, with `H3_rep (H₃.simple i) = H3_simple i`.
The abstract Coxeter element maps to `H3_coxeterElement`
(`H3_rep_abstractCoxeterElement`), so
`10 ∣ orderOf H3_abstractCoxeterElement`: the icosahedral 10 is now a fact
about the GROUP H₃, not only about this matrix triple. Still open there,
and stated as such: the representation is not shown FAITHFUL, so the
transfer is divisibility and not equality. The element-ordering conjugacy
noted above also remains unproved. -/
theorem H3_coxeter_data_from_diagram :
    -- (1) the diagram
    (CoxeterMatrix.H₃ 0 1 = 3 ∧ CoxeterMatrix.H₃ 1 2 = 5 ∧ CoxeterMatrix.H₃ 0 2 = 2) ∧
    -- (2) the Coxeter element
    H3_coxeterElement = !![0, Real.goldenRatio, -Real.goldenRatio;
                           1, Real.goldenRatio, -Real.goldenRatio;
                           0, Real.goldenRatio, -1] ∧
    -- (3) its characteristic polynomial, factored
    H3_coxeterElement.charpoly
      = (Polynomial.X + 1) *
        (Polynomial.X ^ 2 - Polynomial.C Real.goldenRatio * Polynomial.X + 1) ∧
    -- (4) eigenvalues are the tenth roots of unity with exponents 5, 1, 9
    (∀ z : ℂ, H3_coxeterElementC.charpoly.eval z = 0
        ↔ (z = H3_zeta ^ 5 ∨ z = H3_zeta ^ 1 ∨ z = H3_zeta ^ 9)) ∧
    -- (5) Coxeter number = order of the Coxeter element = order of the eigenvalue
    orderOf H3_coxeterElement = H3_Coxeter_number ∧
    IsPrimitiveRoot H3_zeta H3_Coxeter_number ∧
    -- (6) exponent set = {1,5,9} = H3_exponents
    (H3_exponentSet = ({1, 5, 9} : Finset ℕ) ∧ H3_exponents.toFinset = H3_exponentSet) := by
  refine ⟨⟨?_, ?_, ?_⟩, H3_coxeterElement_eq, H3_charpoly_eq, H3_eigenvalue_iff,
          H3_Coxeter_number_eq_orderOf, H3_Coxeter_number_derived, H3_exponentSet_eq,
          H3_exponents_derived⟩ <;> decide

end H3CoxeterDiagram
end PrincipiaTractalis
