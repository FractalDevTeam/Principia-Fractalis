/-
# r123: WHAT THE PROVEN SUBSTRATE FORCES — and what it provably cannot force.

★ 2026-07-26 r123 — the first file to compose the r112/r113 substrate theorems
with the framework's α-table. The result is NEGATIVE and SHARP. ★

## Context

r112 (`PF/SubstrateCompletionFaithful.lean`) and r113
(`PF/SubstrateTraceUniqueness.lean`) establish, unconditionally and kernel-only,
that `T∞ = TimelessFieldCompletion` is the Glimm `3^∞` UHF algebra: faithful
trace, C*-simple, UNIQUE tracial state. The corpus reads that as evidence that
the substrate "forces" the nine α-values. This file tests that reading against
the substrate's actual invariants and finds it false in both directions.

## What is established here

**(A) The substrate's trace range on projections is `ℤ[1/3]`, and the nine
α-values are almost entirely outside it.**
  * `substrate_level_projection_trace` — an honest projection at level `k` has
    normalized trace `card/3^k`, hence in `ℤ[1/3]`; and every such value is
    attained (`substrate_attains_every_Z13_trace`).
  * `not_memZ13_of_irrational`, `not_memZ13_three_halves` — the exclusions.
  * `alpha_table_memZ13_verdict` — of the nine α-values, exactly TWO
    (`α_Poincaré = 1`, `α_YM = 2`) lie in `ℤ[1/3]`; the other seven do not.
    Note `α_RH = 3/2` fails for a *2-adic* reason and `α_Hodge = φ` for a
    *5-adic* one: the α-table lives at the primes 2 and 5, and the substrate's
    supernatural number is `3^∞`, in which neither 2 nor 5 occurs.

**(B) If α is spectral data instead, the substrate constrains NOTHING.**
  * `substrate_level_realizes_arbitrary_spectrum` — for every real vector there
    is a self-adjoint element of a finite substrate level whose spectrum is
    exactly that vector's range.
  * `two_distinct_alpha_assignments_both_realized` — the framework's α-table and
    a perturbation of it are both realized inside `M_9 = M_{3^2} ⊆ T∞`.
  So the "α is an eigenvalue of a substrate operator" reading is vacuous.

  (A) + (B) is a genuine dichotomy: the substrate either EXCLUDES an α-value
  (K-theoretic reading) or says nothing at all about it (spectral reading).
  There is no reading on which it selects one.

**(C) The framework's only substrate-intrinsic definition of the α's is
REFUTED by r113.** Conjecture 8.X.2 (`OPEN_PROBLEMS.md` Priority 1a;
`Papers/principia_fractalis_millennium_problems_2026-07-09.tex:518-519`) asserts
that the nine α's are the nine normal extremal tracial states of `π(T∞)''`.
  * `substrate_tracial_state_unique_pairwise` — any two tracial states on `T∞`
    are EQUAL (immediate from r113).
  * `no_nine_distinct_tracial_states` — there is no injective 9-family of
    tracial states on `T∞`. One ≠ nine.
  (The von Neumann corollary is classical, not formalized here: a normal state
  on `π(T∞)''` is determined by its restriction to the σ-weakly dense `π(T∞)`,
  and a normal tracial state restricts to a tracial state; so `π(T∞)''` carries
  AT MOST ONE normal tracial state, in every representation. See the r123 note.)

**(D) The π/10 ↔ H₃ thread carries zero information about α.**
  * `coupling_H3_identity_holds_for_every_alpha` — under the framework's own
    universal coupling `λ₀(α) = π/(10α)`, the H₃ identity
    `sin(λ₀(α)·α) = 1/(2φ)` holds for EVERY nonzero α. A statement true of all
    α constrains none.

**(E) α is only defined mod 2, so the α-skeleton is not well-posed.**
  * `resonance_phase_two_periodic` — the framework's primary definition of α
    (`R_f(α,s) = Σ e^{iπαD₃(n)}/n^s`, ch03 Def. 3.x) is invariant under
    `α ↦ α + 2`, because `D₃(n) ∈ ℕ`.
  * `alpha_P_sq_eq_alpha_YM_not_mod_two_invariant` — but the skeleton's
    invariant `α_P² = α_YM` is NOT invariant under that shift. So the α-table's
    algebraic skeleton is not a statement about the objects α indexes.

**(F) The one POSITIVE convergence.**
  * `bare_route_alpha_memZ13` — every α admitted by the corpus's own
    machine-checked ternary reality condition (`bare_route_structural_finding`,
    `PF/TuringEncoding/WeightedDigitalSumGeneratingFunction.lean:131`) lies in
    `ℤ[1/3]` — the SAME set the substrate's K-theory produces, reached by a
    completely independent route. Two independent substrate-side computations
    agree, and both exclude `√2` and `φ + 1/4`.

## Honest scope

Nothing here derives an α-value; the file's content is that no such derivation
can come from the substrate. `MemZ13` is an elementary predicate on ℝ, not
mathlib operator K-theory (which does not exist); the identification
`τ_*(K_0(T∞)) = ℤ[1/3]` is classical (Glimm) and is used as motivation. What is
formalized is the level-projection trace computation, which is the concrete
content of that identification, plus the arithmetic exclusions.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project axioms.
Zero sorries.

Stage 2026-07-26 r123.
-/

import PF.SubstrateTraceUniqueness
import PF.CrossMillenniumSharedInvariants
import PF.TuringEncoding.WeightedDigitalSumGeneratingFunction
import PF.H3CoxeterOrigin
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Data.Real.GoldenRatio
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace AlphaFromSubstrateKTheory

open Real
open PrincipiaTractalis
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.SubstrateUHFBoundedTrace
open PrincipiaTractalis.SubstrateUHFPreTraceDirectLimit
open PrincipiaTractalis.SubstrateTraceUniqueness
open PrincipiaTractalis.SubstrateTimelessFieldCompletion

/-! ## §0 — `phi` and mathlib's `goldenRatio` agree -/

/-- The corpus's `phi` is mathlib's `Real.goldenRatio`. -/
theorem phi_eq_goldenRatio : phi = Real.goldenRatio := by
  unfold phi Real.goldenRatio
  norm_num

/-! ## §1 — `ℤ[1/3]`: the substrate's K-theoretic number system

`K_0(M_{3^∞}) = ℤ[1/3]` as an ordered group with order unit `1`, and the unique
trace carries `K_0` isomorphically onto `ℤ[1/3] ⊂ ℝ` (Glimm/Elliott). We work
with the concrete image. -/

/-- **`x ∈ ℤ[1/3]`** — the range of the substrate's unique trace on `K_0`. -/
def MemZ13 (x : ℝ) : Prop := ∃ (m : ℤ) (k : ℕ), x = (m : ℝ) / 3 ^ k

theorem memZ13_intCast (m : ℤ) : MemZ13 (m : ℝ) := ⟨m, 0, by norm_num⟩

theorem memZ13_one : MemZ13 1 := by
  have := memZ13_intCast 1; simpa using this

theorem memZ13_two : MemZ13 2 := by
  have := memZ13_intCast 2; simpa using this

/-- Every element of `ℤ[1/3]` is rational. This is the whole obstruction: the
    substrate's complete classifying invariant produces only rationals. -/
theorem memZ13_isRat {x : ℝ} (h : MemZ13 x) : ∃ q : ℚ, (q : ℝ) = x := by
  obtain ⟨m, k, rfl⟩ := h
  refine ⟨(m : ℚ) / 3 ^ k, ?_⟩
  push_cast
  ring

/-- **Exclusion 1 — irrationality.** No irrational number is in `ℤ[1/3]`. -/
theorem not_memZ13_of_irrational {x : ℝ} (hx : Irrational x) : ¬ MemZ13 x := by
  intro h
  obtain ⟨q, hq⟩ := memZ13_isRat h
  exact hx ⟨q, hq⟩

/-- **Exclusion 2 — the prime 2.** `3/2 ∉ ℤ[1/3]`: the α-table's dyadic
    denominators are invisible to a `3^∞` substrate. -/
theorem not_memZ13_three_halves : ¬ MemZ13 (3 / 2 : ℝ) := by
  rintro ⟨m, k, hmk⟩
  have h3 : (3 : ℝ) ^ k ≠ 0 := by positivity
  have hZ : (2 : ℤ) * m = 3 ^ (k + 1) := by
    have : (2 : ℝ) * m = 3 ^ (k + 1) := by
      field_simp at hmk
      ring_nf
      ring_nf at hmk
      linarith [hmk]
    exact_mod_cast this
  have hodd : Odd ((3 : ℤ) ^ (k + 1)) := Odd.pow ⟨1, by norm_num⟩
  rw [← hZ] at hodd
  have heven : Even ((2 : ℤ) * m) := ⟨m, by ring⟩
  exact (Int.not_even_iff_odd.mpr hodd) heven

/-- **Exclusion 3 — the prime 5.** `1/5 ∉ ℤ[1/3]`. The substrate therefore
    admits no projection of trace `1/5`, hence no unital copy of `M₅(ℂ)` and no
    decomposition of `1` into five equivalent projections: the icosahedral
    5-fold structure that supplies `φ` cannot live inside `T∞` K-theoretically. -/
theorem not_memZ13_one_fifth : ¬ MemZ13 (1 / 5 : ℝ) := by
  rintro ⟨m, k, hmk⟩
  have h3 : (3 : ℝ) ^ k ≠ 0 := by positivity
  have hZ : (5 : ℤ) * m = 3 ^ k := by
    have : (5 : ℝ) * m = 3 ^ k := by
      field_simp at hmk
      linarith [hmk]
    exact_mod_cast this
  have hdvd : (5 : ℤ) ∣ (3 : ℤ) ^ k := ⟨m, hZ.symm⟩
  have hp : Prime (5 : ℤ) := by norm_num
  have h5 : (5 : ℤ) ∣ (3 : ℤ) := hp.dvd_of_dvd_pow hdvd
  norm_num at h5

/-! ## §2 — What the substrate DOES force: the level-projection trace -/

/-- The characteristic function of `S ⊆ Fin (3^k)`, as a ℂ-valued diagonal. -/
noncomputable def charDiag {k : ℕ} (S : Finset (Fin (3 ^ k))) :
    Fin (3 ^ k) → ℂ :=
  fun i => if i ∈ S then (1 : ℂ) else 0

/-- `diagonal (charDiag S)` is an honest projection: idempotent and
    self-adjoint. -/
theorem charDiag_isProjection {k : ℕ} (S : Finset (Fin (3 ^ k))) :
    (Matrix.diagonal (charDiag S)) * (Matrix.diagonal (charDiag S))
        = Matrix.diagonal (charDiag S)
      ∧ (Matrix.diagonal (charDiag S)).IsHermitian := by
  constructor
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : i ∈ S <;> simp [charDiag, h]
  · refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
    funext i
    by_cases h : i ∈ S <;> simp [charDiag, h]

/-- **★ The substrate's trace on a level-`k` projection is `card/3^k` ★** —
    the concrete content of `τ_*(K_0(T∞)) = ℤ[1/3]`. -/
theorem substrate_level_projection_trace {k : ℕ} (S : Finset (Fin (3 ^ k))) :
    haveI : NeZero (3 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
    normalized_matrix_trace (Matrix.diagonal (charDiag S))
      = (S.card : ℂ) / ((3 : ℂ) ^ k) := by
  haveI : NeZero (3 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  unfold normalized_matrix_trace
  rw [Matrix.trace_diagonal]
  have hsum : (∑ i, charDiag S i) = (S.card : ℂ) := by
    unfold charDiag
    rw [Finset.sum_ite_mem]
    simp
  rw [hsum]
  norm_num

/-- **Every value of `ℤ[1/3] ∩ [0,1]` with denominator `3^k` is attained** by a
    substrate projection at level `k`. The trace range is exactly `ℤ[1/3]`, not
    merely contained in it. -/
theorem substrate_attains_every_Z13_trace (k m : ℕ) (hm : m ≤ 3 ^ k) :
    haveI : NeZero (3 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
    ∃ P : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ,
      (P * P = P ∧ P.IsHermitian) ∧
      normalized_matrix_trace P = (m : ℂ) / ((3 : ℂ) ^ k) := by
  haveI : NeZero (3 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  classical
  obtain ⟨S, -, hcard⟩ :=
    Finset.exists_subset_card_eq
      (show m ≤ (Finset.univ : Finset (Fin (3 ^ k))).card by simpa using hm)
  exact ⟨Matrix.diagonal (charDiag S), charDiag_isProjection S,
         by rw [substrate_level_projection_trace S, hcard]⟩

/-! ## §3 — The nine α-values against `ℤ[1/3]` -/

theorem irrational_alpha_P : Irrational α_P := by
  unfold α_P; exact irrational_sqrt_two

theorem irrational_alpha_Hodge : Irrational α_Hodge := by
  unfold α_Hodge
  rw [phi_eq_goldenRatio]
  exact Real.goldenRatio_irrational

theorem irrational_alpha_NP : Irrational α_NP := by
  unfold α_NP
  rw [phi_eq_goldenRatio]
  have := Real.goldenRatio_irrational.ratCast_add (q := (1 / 4 : ℚ))
  convert this using 1
  push_cast
  ring

theorem irrational_alpha_NS : Irrational α_NS := by
  unfold α_NS
  have := irrational_pi.ratCast_mul (q := (3 / 2 : ℚ)) (by norm_num)
  convert this using 1
  push_cast
  ring

theorem irrational_alpha_BSD : Irrational α_BSD := by
  unfold α_BSD
  have := irrational_pi.ratCast_mul (q := (3 / 4 : ℚ)) (by norm_num)
  convert this using 1
  push_cast
  ring

theorem irrational_alpha_QG : Irrational α_QG := by
  unfold α_QG
  rintro ⟨q, hq⟩
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hsq : ((q : ℝ)) ^ 2 = 2 * Real.pi := by
    rw [hq]; exact Real.sq_sqrt h2pi
  refine irrational_pi ⟨q ^ 2 / 2, ?_⟩
  push_cast
  linarith [hsq]

/-- **★★★ r123.A — THE α-TABLE AGAINST THE SUBSTRATE'S TRACE RANGE ★★★**

    Of the nine framework α-values, exactly two lie in `ℤ[1/3] = τ_*(K_0(T∞))`,
    and they are the two integers. The other seven are excluded — five by
    irrationality, `α_RH = 3/2` by the prime 2. -/
theorem alpha_table_memZ13_verdict :
    -- IN the substrate's K-theoretic number system:
    MemZ13 α_Poincare ∧ MemZ13 α_YM
    -- OUT of it:
    ∧ ¬ MemZ13 α_P ∧ ¬ MemZ13 α_Hodge ∧ ¬ MemZ13 α_NP
    ∧ ¬ MemZ13 α_NS ∧ ¬ MemZ13 α_BSD ∧ ¬ MemZ13 α_QG
    ∧ ¬ MemZ13 α_RH := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold α_Poincare; exact memZ13_one
  · unfold α_YM; exact memZ13_two
  · exact not_memZ13_of_irrational irrational_alpha_P
  · exact not_memZ13_of_irrational irrational_alpha_Hodge
  · exact not_memZ13_of_irrational irrational_alpha_NP
  · exact not_memZ13_of_irrational irrational_alpha_NS
  · exact not_memZ13_of_irrational irrational_alpha_BSD
  · exact not_memZ13_of_irrational irrational_alpha_QG
  · unfold α_RH; exact not_memZ13_three_halves

/-! ## §4 — The other horn: substrate spectra constrain nothing -/

/-- **★★★ r123.B — EVERY real vector is the spectrum of a substrate element ★★★**

    At any finite level `k` of the substrate tower, and for any assignment of
    reals to the `3^k` basis states, there is a self-adjoint matrix whose
    spectrum is exactly that assignment's range. Hence "α is an eigenvalue of an
    operator affiliated to `T∞`" imposes NO constraint on α whatsoever. -/
theorem substrate_level_realizes_arbitrary_spectrum {k : ℕ}
    (a : Fin (3 ^ k) → ℝ) :
    ∃ A : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ,
      A.IsHermitian ∧ spectrum ℂ A = Set.range (fun i => ((a i : ℝ) : ℂ)) := by
  refine ⟨Matrix.diagonal (fun i => ((a i : ℝ) : ℂ)), ?_, ?_⟩
  · refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
    funext i
    simp [Complex.conj_ofReal]
  · exact spectrum_diagonal _

/-- **★ The impossibility, concretely ★** — the framework's nine α-values and a
    perturbation of them are BOTH the spectrum of a self-adjoint element of the
    level-2 substrate algebra `M₉ = M_{3^2} ⊆ T∞`, and the two spectra are
    different. No invariant of the substrate can prefer one to the other. -/
theorem two_distinct_alpha_assignments_both_realized
    (a b : Fin (3 ^ 2) → ℝ) (hab : Set.range a ≠ Set.range b) :
    (∃ A : Matrix (Fin (3 ^ 2)) (Fin (3 ^ 2)) ℂ,
        A.IsHermitian ∧ spectrum ℂ A = Set.range (fun i => ((a i : ℝ) : ℂ))) ∧
    (∃ B : Matrix (Fin (3 ^ 2)) (Fin (3 ^ 2)) ℂ,
        B.IsHermitian ∧ spectrum ℂ B = Set.range (fun i => ((b i : ℝ) : ℂ))) ∧
    Set.range (fun i => ((a i : ℝ) : ℂ)) ≠ Set.range (fun i => ((b i : ℝ) : ℂ)) := by
  refine ⟨substrate_level_realizes_arbitrary_spectrum a,
          substrate_level_realizes_arbitrary_spectrum b, ?_⟩
  intro h
  apply hab
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    have hx : ((a i : ℝ) : ℂ) ∈ Set.range (fun j => ((b j : ℝ) : ℂ)) := by
      rw [← h]; exact ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, Complex.ofReal_injective hj⟩
  · rintro ⟨i, rfl⟩
    have hx : ((b i : ℝ) : ℂ) ∈ Set.range (fun j => ((a j : ℝ) : ℂ)) := by
      rw [h]; exact ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, Complex.ofReal_injective hj⟩

/-! ## §5 — r113 REFUTES the extremal-trace definition of the α's -/

/-- Any two tracial states on `T∞` are equal (r113). -/
theorem substrate_tracial_state_unique_pairwise
    (φ ψ : TimelessFieldCompletion → ℂ)
    (hφ : IsTracialState φ) (hψ : IsTracialState ψ) : φ = ψ := by
  funext x
  rw [substrate_UHF_trace_unique φ hφ x, substrate_UHF_trace_unique ψ hψ x]

/-- **★★★ r123.C — CONJECTURE 8.X.2 IS FALSE ★★★**

    `OPEN_PROBLEMS.md` Priority 1a and
    `Papers/principia_fractalis_millennium_problems_2026-07-09.tex:518-519`
    assert that the nine α-values are in bijection with a NINE-element set of
    extremal tracial states of the substrate. There is no injective family of
    nine tracial states on `T∞`: by r113 there is exactly one. -/
theorem no_nine_distinct_tracial_states :
    ¬ ∃ f : Fin 9 → (TimelessFieldCompletion → ℂ),
        (∀ i, IsTracialState (f i)) ∧ Function.Injective f := by
  rintro ⟨f, hf, hinj⟩
  have : (0 : Fin 9) = 1 :=
    hinj (substrate_tracial_state_unique_pairwise (f 0) (f 1) (hf 0) (hf 1))
  exact absurd this (by decide)

/-- The tracial state space of `T∞` is a singleton — the positive form of
    r123.C, and the exact negation of a "finite set of nine extremal traces". -/
theorem substrate_tracial_state_space_singleton :
    ∀ φ : TimelessFieldCompletion → ℂ, IsTracialState φ → φ = UHF_trace :=
  fun φ hφ => funext (substrate_UHF_trace_unique φ hφ)

/-! ## §6 — The π/10 ↔ H₃ thread is vacuous -/

/-- The framework's universal coupling, as a definition (which is all it ever
    is in the corpus: `PF/UniversalAlphaOperatorFamily.lean:95`). -/
noncomputable def lambda0 (α : ℝ) : ℝ := Real.pi / (10 * α)

theorem lambda0_mul_alpha (α : ℝ) (hα : α ≠ 0) : lambda0 α * α = Real.pi / 10 := by
  unfold lambda0
  field_simp

/-- **★★★ r123.D — THE π/10 THREAD CARRIES NO INFORMATION ABOUT α ★★★**

    Combining the framework's universal coupling `λ₀(α)·α = π/10` with the
    classical H₃/icosahedral identity `sin(π/10) = 1/(2φ)` yields a statement
    that holds for EVERY nonzero α. It therefore selects no α: not `φ`, not
    `φ + 1/4`, not anything. The "same π/10 appears in both" observation is the
    observation that `π/10` appears on both sides of an identity uniform in α. -/
theorem coupling_H3_identity_holds_for_every_alpha (α : ℝ) (hα : α ≠ 0) :
    Real.sin (lambda0 α * α) = 1 / (2 * Real.goldenRatio) := by
  rw [lambda0_mul_alpha α hα]
  exact PrincipiaFractalis.H3CoxeterOrigin.sin_pi_div_ten_eq_inv_two_phi

/-! ## §7 — α is only defined mod 2; the α-skeleton is not -/

/-- **The framework's primary definition of α is 2-periodic.** In
    `R_f(α,s) = Σ_n e^{iπαD₃(n)} n^{-s}` (ch03 Def. `def:fractal-resonance`) the
    digital sum `D₃(n)` is a natural number, so `α` and `α + 2` give the same
    function. `α` is a point of `ℝ/2ℤ`, not of `ℝ`. -/
theorem resonance_phase_two_periodic (α : ℝ) (d : ℕ) :
    Complex.exp (Real.pi * (α + 2) * d * Complex.I)
      = Complex.exp (Real.pi * α * d * Complex.I) := by
  have h : (Real.pi : ℂ) * (α + 2) * d * Complex.I
      = Real.pi * α * d * Complex.I + (d : ℂ) * (2 * Real.pi * Complex.I) := by
    ring
  rw [h, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- **★ r123.E — the α-skeleton is not invariant under the gauge symmetry of
    its own α ★**

    `α_P² = α_YM` is the skeleton's clause (1)
    (`CrossMillenniumSharedInvariants.lean:95`). Shifting `α_P` by the
    2-periodicity of §7 destroys it: `(√2 + 2)²` is not `2` mod `2ℤ`. So the
    algebraic skeleton is a statement about representatives, not about the
    resonance parameters it claims to constrain. -/
theorem alpha_P_sq_eq_alpha_YM_not_mod_two_invariant :
    ¬ ∃ m : ℤ, (Real.sqrt 2 + 2) ^ 2 = 2 + 2 * (m : ℝ) := by
  rintro ⟨m, hm⟩
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hval : Real.sqrt 2 = ((m : ℝ) - 2) / 2 := by nlinarith [hm, h2]
  refine irrational_sqrt_two ⟨((m : ℚ) - 2) / 2, ?_⟩
  rw [hval]; push_cast; ring

/-! ## §8 — The POSITIVE convergence: the corpus's own ternary route lands in
    `ℤ[1/3]` too -/

/-- **★★★ r123.F — THE BARE TERNARY ROUTE FORCES `α ∈ ℤ[1/3]` ★★★**

    `bare_route_structural_finding`
    (`PF/TuringEncoding/WeightedDigitalSumGeneratingFunction.lean:131`) shows the
    reality condition on the ternary generating function admits only
    `sin(πα) = 0` or `cos(πα) = -1/2`. Both branches land in `ℤ[1/3]`:
    integers, and `±2/3 + 2ℤ`.

    This is an INDEPENDENT confirmation of §1: the substrate's K-theory and the
    substrate's own generating function agree that α is a 3-adic rational.
    Neither `√2` nor `φ + 1/4` is one. -/
theorem bare_route_alpha_memZ13 (α : ℝ) (h : betaIm α = 0) : MemZ13 α := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rcases bare_route_structural_finding α h with hsin | hcos
  · -- sin(πα) = 0 ⟹ α ∈ ℤ
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
    have h' : Real.pi * (n : ℝ) = Real.pi * α := by linarith [hn]
    have hα : α = (n : ℝ) := (mul_left_cancel₀ hpi h').symm
    exact ⟨n, 0, by simpa using hα⟩
  · -- cos(πα) = -1/2 ⟹ α = ±2/3 + 2k
    have hc23 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
      have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
      rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]
      norm_num
    have heq : Real.cos (Real.pi * α) = Real.cos (2 * Real.pi / 3) := by
      rw [hcos, hc23]
    obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp heq
    · -- 2π/3 = 2kπ + πα ⟹ α = 2/3 - 2k
      refine ⟨2 - 6 * k, 1, ?_⟩
      have h' : Real.pi * α = Real.pi * (2 / 3 - 2 * (k : ℝ)) := by linarith [hk]
      have hα : α = 2 / 3 - 2 * (k : ℝ) := mul_left_cancel₀ hpi h'
      rw [hα]; push_cast; ring
    · -- 2π/3 = 2kπ - πα ⟹ α = 2k - 2/3
      refine ⟨6 * k - 2, 1, ?_⟩
      have h' : Real.pi * α = Real.pi * (2 * (k : ℝ) - 2 / 3) := by linarith [hk]
      have hα : α = 2 * (k : ℝ) - 2 / 3 := mul_left_cancel₀ hpi h'
      rw [hα]; push_cast; ring

/-- **The two canonical α-values are excluded by the bare ternary route** —
    a restatement of the corpus's own finding in `ℤ[1/3]` form. -/
theorem canonical_alphas_fail_bare_route :
    betaIm α_P ≠ 0 ∧ betaIm α_NP ≠ 0 := by
  constructor
  · intro h
    exact not_memZ13_of_irrational irrational_alpha_P (bare_route_alpha_memZ13 _ h)
  · intro h
    exact not_memZ13_of_irrational irrational_alpha_NP (bare_route_alpha_memZ13 _ h)

/-! ## §9 — r123 capstone -/

/-- **★★★ r123 CAPSTONE — THE PROVEN SUBSTRATE CANNOT SUPPLY THE α-VALUES ★★★**

    Six independent statements, all kernel-only:

      (A) `ℤ[1/3]` is the substrate's trace range on projections, and it is
          attained exactly; seven of the nine α-values lie outside it.
      (B) Every real vector is the spectrum of a self-adjoint substrate element,
          so the spectral reading of α is vacuous.
      (C) `T∞` has exactly one tracial state, so the corpus's nine-extremal-trace
          definition of the α's (Conjecture 8.X.2 / Priority 1a) is FALSE.
      (D) The π/10 ↔ H₃ coupling identity holds for every α.
      (E) The α-skeleton is not invariant under the 2-periodicity that is the
          gauge symmetry of the framework's own definition of α.
      (F) The corpus's own ternary reality condition independently forces
          `α ∈ ℤ[1/3]`, excluding `√2` and `φ + 1/4`.

    Together: the substrate either EXCLUDES an α-value or is SILENT about it.
    It never selects one. Any construction that produces the α-values must
    therefore import them from outside the substrate — which is exactly what
    `codex/ALPHA_NP_DERIVABILITY_2026-07-25.md` found empirically. That audit's
    "circularity" is not a drafting defect; it is the only possible outcome. -/
theorem r123_substrate_cannot_force_alpha_capstone :
    -- (A)
    (MemZ13 α_Poincare ∧ MemZ13 α_YM ∧ ¬ MemZ13 α_P ∧ ¬ MemZ13 α_NP
      ∧ ¬ MemZ13 α_RH ∧ ¬ MemZ13 α_Hodge)
    -- (B)
    ∧ (∀ a : Fin (3 ^ 2) → ℝ, ∃ A : Matrix (Fin (3 ^ 2)) (Fin (3 ^ 2)) ℂ,
        A.IsHermitian ∧ spectrum ℂ A = Set.range (fun i => ((a i : ℝ) : ℂ)))
    -- (C)
    ∧ (¬ ∃ f : Fin 9 → (TimelessFieldCompletion → ℂ),
        (∀ i, IsTracialState (f i)) ∧ Function.Injective f)
    -- (D)
    ∧ (∀ α : ℝ, α ≠ 0 → Real.sin (lambda0 α * α) = 1 / (2 * Real.goldenRatio))
    -- (E)
    ∧ (¬ ∃ m : ℤ, (Real.sqrt 2 + 2) ^ 2 = 2 + 2 * (m : ℝ))
    -- (F)
    ∧ (∀ α : ℝ, betaIm α = 0 → MemZ13 α) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := alpha_table_memZ13_verdict
  exact ⟨⟨h1, h2, h3, h5, h9, h4⟩,
         fun a => substrate_level_realizes_arbitrary_spectrum a,
         no_nine_distinct_tracial_states,
         coupling_H3_identity_holds_for_every_alpha,
         alpha_P_sq_eq_alpha_YM_not_mod_two_invariant,
         bare_route_alpha_memZ13⟩

/-! ## §10 — Axiom audit -/

#print axioms phi_eq_goldenRatio
#print axioms not_memZ13_of_irrational
#print axioms not_memZ13_three_halves
#print axioms not_memZ13_one_fifth
#print axioms substrate_level_projection_trace
#print axioms substrate_attains_every_Z13_trace
#print axioms alpha_table_memZ13_verdict
#print axioms substrate_level_realizes_arbitrary_spectrum
#print axioms two_distinct_alpha_assignments_both_realized
#print axioms no_nine_distinct_tracial_states
#print axioms substrate_tracial_state_space_singleton
#print axioms coupling_H3_identity_holds_for_every_alpha
#print axioms resonance_phase_two_periodic
#print axioms alpha_P_sq_eq_alpha_YM_not_mod_two_invariant
#print axioms bare_route_alpha_memZ13
#print axioms canonical_alphas_fail_bare_route
#print axioms r123_substrate_cannot_force_alpha_capstone

end AlphaFromSubstrateKTheory
end PrincipiaTractalis
