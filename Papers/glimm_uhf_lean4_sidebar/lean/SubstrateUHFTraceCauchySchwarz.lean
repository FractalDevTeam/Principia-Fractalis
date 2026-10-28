/-
# r102: Substrate UHF trace — completion-tier ℂ-LINEARITY and
#       CAUCHY–SCHWARZ for the trace sesquilinear pairing

★ 2026-07-21 r102 — Milestones M1 + M2 of the completion-tier
faithfulness route (Cauchy–Schwarz → trace-null ideal → simplicity →
faithfulness) ★

## The framework-first content

r87 delivered τ_UHF : TimelessFieldCompletion → ℂ as additive on the
dense image + unital + 1-Lipschitz + UC. r94/r96/r98 upgraded τ_UHF
to a positive Hermitian tracial state. r100 isolated the completion-
tier faithfulness residual. r102 supplies the two missing analytic
layers toward closing that residual:

**M1 — completion-tier ℂ-linearity of τ_UHF**:
  * `substrate_pre_trace_smul` — pre-trace ℂ-homogeneity on
    `TimelessFieldRing` (via `DirectLimit.exists_eq_mk` +
    `substrate_quotient_smul_same_level` + r84 matrix-level smul).
  * `UHF_trace_add` — τ_UHF(x+y) = τ_UHF(x) + τ_UHF(y) on the FULL
    completion, via `UniformSpace.Completion.induction_on₂` on the
    closed equality set (continuous + / UC of τ_UHF) + `coe_add`.
  * `UHF_trace_smul` — τ_UHF(c•x) = c·τ_UHF(x) on the full completion,
    via `Completion.induction_on` + `coe_smul` + continuous const-smul.
  * `UHF_trace_zero`, `UHF_trace_neg`, `UHF_trace_sub` — corollaries.
  * `UHF_trace_linearMap : TimelessFieldCompletion →ₗ[ℂ] ℂ` — the
    bundled ℂ-linear functional.

**M2 — Cauchy–Schwarz for the trace pairing**:
  * `traceInner x y := τ_UHF(y* · x)` — the trace sesquilinear pairing,
    with `traceInner_self_nonneg` / `_re_nonneg` / `_im_zero`
    (re-exports of r98 positivity through `Complex.nonneg_iff`).
  * `UHF_trace_inner_conj` — τ_UHF(x*·y) = conj(τ_UHF(y*·x)) (r96).
  * `UHF_trace_expand` — the sesquilinear expansion of
    τ_UHF((x−c•y)*·(x−c•y)) via M1 linearity + `StarModule ℂ`.
  * `UHF_trace_discriminant` — the positivity of the expansion, in
    real-part form: ∀ c : ℂ,
    0 ≤ Re τ(x*x) − 2·Re(c·conj τ(y*x)) + |c|²·Re τ(y*y).
  * **`UHF_trace_cauchySchwarz`** —
    ‖τ_UHF(y*·x)‖² ≤ Re τ_UHF(x*·x) · Re τ_UHF(y*·y),
    via the real quadratic-discriminant argument (mathlib
    `discrim_le_zero`) applied along real multiples c = t·τ(y*x).
  * **`UHF_trace_null_left_absorption`** — the trace-null cone is a
    LEFT IDEAL in kernel form: τ_UHF(x*·x) = 0 →
    τ_UHF((a·x)*·(a·x)) = 0, directly from Cauchy–Schwarz with
    y := a*·a·x (no operator inequality needed).

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-21 r102 — completion-tier ℂ-linearity + Cauchy–Schwarz
+ trace-null left-ideal absorption for the substrate UHF trace.
-/

import PF.SubstrateUHFTraceIsPositive
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateUHFTraceCauchySchwarz

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open SubstrateUHFBoundedTrace SubstrateUHFTraceLipschitz
open SubstrateUHFCompletionTrace SubstrateUHFPreTraceDirectLimit
open SubstrateUHFTraceIsTracial SubstrateUHFTraceIsStarPreserving
open SubstrateUHFTraceIsPositive
open SubstrateDirectLimit SubstrateTimelessFieldCompletion
open SubstrateTimelessFieldNorm

/-! ## §1 — M1.a: pre-trace ℂ-scalar homogeneity on TimelessFieldRing -/

/-- **r102.a: the substrate pre-trace is ℂ-scalar homogeneous**:
    `substrate_pre_trace (c • x) = c * substrate_pre_trace x`.

    Proved via `DirectLimit.exists_eq_mk` reducing to a single-level
    representative + r51 `substrate_quotient_smul_same_level` + r84
    matrix-level `normalized_matrix_trace_smul`. -/
theorem substrate_pre_trace_smul (c : ℂ) (x : TimelessFieldRing) :
    substrate_pre_trace (c • x) = c * substrate_pre_trace x := by
  obtain ⟨k, A, hxA⟩ :=
    DirectLimit.exists_eq_mk
      (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
  subst hxA
  rw [substrate_quotient_smul_same_level c k A,
      substrate_pre_trace_of_level, substrate_pre_trace_of_level]
  exact normalized_matrix_trace_smul c A

/-! ## §2 — M1.b: completion-tier additivity of the UHF trace -/

/-- **★★★ r102.b: THE SUBSTRATE UHF TRACE IS ADDITIVE ★★★**

    `UHF_trace (x + y) = UHF_trace x + UHF_trace y` for every
    x, y in the FULL completion `TimelessFieldCompletion`.

    Proof: `UniformSpace.Completion.induction_on₂` on the closed
    equality set (both sides continuous: `continuous_add` composed
    with the r87 UC of `UHF_trace`), with dense-image reduction via
    `UniformSpace.Completion.coe_add` + `UHF_trace_coe` + r87's
    pre-trace additivity `substrate_pre_trace_add`. -/
theorem UHF_trace_add (x y : TimelessFieldCompletion) :
    UHF_trace (x + y) = UHF_trace x + UHF_trace y := by
  refine UniformSpace.Completion.induction_on₂ x y
    (p := fun x y => UHF_trace (x + y) = UHF_trace x + UHF_trace y) ?_ ?_
  · refine isClosed_eq ?_ ?_
    · exact UHF_trace_uniformContinuous.continuous.comp continuous_add
    · exact (UHF_trace_uniformContinuous.continuous.comp continuous_fst).add
        (UHF_trace_uniformContinuous.continuous.comp continuous_snd)
  · intro a b
    rw [← UniformSpace.Completion.coe_add,
        UHF_trace_coe, UHF_trace_coe, UHF_trace_coe]
    exact substrate_pre_trace_add a b

/-- **★★★ r102.c: THE SUBSTRATE UHF TRACE IS ℂ-HOMOGENEOUS ★★★**

    `UHF_trace (c • x) = c * UHF_trace x` for every c : ℂ and x in
    the FULL completion.

    Proof: `UniformSpace.Completion.induction_on` on the closed
    equality set (`continuous_const_smul` / `Continuous.mul` composed
    with the r87 UC of `UHF_trace`), with dense-image reduction via
    `UniformSpace.Completion.coe_smul` + `UHF_trace_coe` + r102.a. -/
theorem UHF_trace_smul (c : ℂ) (x : TimelessFieldCompletion) :
    UHF_trace (c • x) = c * UHF_trace x := by
  refine UniformSpace.Completion.induction_on x
    (p := fun x => UHF_trace (c • x) = c * UHF_trace x) ?_ ?_
  · exact isClosed_eq
      (UHF_trace_uniformContinuous.continuous.comp (continuous_const_smul c))
      (continuous_const.mul UHF_trace_uniformContinuous.continuous)
  · intro a
    rw [← UniformSpace.Completion.coe_smul, UHF_trace_coe, UHF_trace_coe]
    exact substrate_pre_trace_smul c a

/-- **r102.d: `UHF_trace 0 = 0`** — from ℂ-homogeneity at c = 0. -/
theorem UHF_trace_zero : UHF_trace (0 : TimelessFieldCompletion) = 0 := by
  have h := UHF_trace_smul 0 (0 : TimelessFieldCompletion)
  rw [zero_smul, zero_mul] at h
  exact h

/-- **r102.e: `UHF_trace (-x) = -UHF_trace x`** — from ℂ-homogeneity
    at c = −1. -/
theorem UHF_trace_neg (x : TimelessFieldCompletion) :
    UHF_trace (-x) = -UHF_trace x := by
  have h := UHF_trace_smul (-1) x
  rw [neg_one_smul] at h
  rw [h]
  ring

/-- **r102.f: `UHF_trace (x - y) = UHF_trace x - UHF_trace y`**. -/
theorem UHF_trace_sub (x y : TimelessFieldCompletion) :
    UHF_trace (x - y) = UHF_trace x - UHF_trace y := by
  rw [sub_eq_add_neg, UHF_trace_add, UHF_trace_neg, ← sub_eq_add_neg]

/-- **★★★ r102.g: the substrate UHF trace as a bundled ℂ-linear
    functional ★★★** `TimelessFieldCompletion →ₗ[ℂ] ℂ`. -/
noncomputable def UHF_trace_linearMap : TimelessFieldCompletion →ₗ[ℂ] ℂ where
  toFun := UHF_trace
  map_add' := UHF_trace_add
  map_smul' := fun c x => by simpa using UHF_trace_smul c x

@[simp] theorem UHF_trace_linearMap_apply (x : TimelessFieldCompletion) :
    UHF_trace_linearMap x = UHF_trace x := rfl

/-! ## §3 — M2.a: the trace sesquilinear pairing -/

/-- **r102.h: the substrate trace sesquilinear pairing**
    `traceInner x y := τ_UHF(y* · x)` — the GNS pre-inner-product
    induced by the substrate UHF trace. -/
noncomputable def traceInner (x y : TimelessFieldCompletion) : ℂ :=
  UHF_trace (star y * x)

/-- **r102.i: the pairing is positive on the diagonal**
    (in the ComplexOrder) — re-export of r98 positivity. -/
theorem traceInner_self_nonneg (x : TimelessFieldCompletion) :
    0 ≤ traceInner x x :=
  UHF_trace_star_mul_self_nonneg x

/-- **r102.j: diagonal values have nonnegative real part**. -/
theorem traceInner_self_re_nonneg (x : TimelessFieldCompletion) :
    0 ≤ (traceInner x x).re :=
  (Complex.nonneg_iff.mp (traceInner_self_nonneg x)).1

/-- **r102.k: diagonal values are real** (vanishing imaginary part). -/
theorem traceInner_self_im_zero (x : TimelessFieldCompletion) :
    (traceInner x x).im = 0 :=
  ((Complex.nonneg_iff.mp (traceInner_self_nonneg x)).2).symm

/-- **r102.l: conjugate symmetry of the trace pairing**:
    `τ_UHF(x* · y) = conj (τ_UHF(y* · x))` — from r96
    star-preservation + `star_mul` + `star_star`. -/
theorem UHF_trace_inner_conj (x y : TimelessFieldCompletion) :
    UHF_trace (star x * y) = star (UHF_trace (star y * x)) := by
  rw [← UHF_trace_star, star_mul, star_star]

/-! ## §4 — M2.b: the sesquilinear expansion and its positivity -/

/-- **r102.m: sesquilinear expansion of the diagonal at `x − c•y`**:

    τ_UHF((x−c•y)*·(x−c•y)) = τ_UHF(x*x) − c·τ_UHF(x*y)
      − conj c·τ_UHF(y*x) + (conj c·c)·τ_UHF(y*y).

    Uses `star_sub`/`star_smul` (r58 `StarModule ℂ`), scalar-mul
    associativity/commutation, and M1 completion-tier linearity. -/
theorem UHF_trace_expand (x y : TimelessFieldCompletion) (c : ℂ) :
    UHF_trace (star (x - c • y) * (x - c • y)) =
      UHF_trace (star x * x) - c * UHF_trace (star x * y) -
        star c * UHF_trace (star y * x) +
        (star c * c) * UHF_trace (star y * y) := by
  have h_alg : star (x - c • y) * (x - c • y) =
      star x * x - c • (star x * y) - star c • (star y * x) +
        (star c * c) • (star y * y) := by
    rw [star_sub, star_smul, sub_mul, mul_sub, mul_sub,
        smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
        smul_smul]
    abel
  rw [h_alg, UHF_trace_add, UHF_trace_sub, UHF_trace_sub,
      UHF_trace_smul, UHF_trace_smul, UHF_trace_smul]

/-- **r102.n: the discriminant inequality** — positivity of the
    sesquilinear expansion, extracted to its real part:

    ∀ c : ℂ, 0 ≤ Re τ(x*x) − 2·Re(c·conj τ(y*x)) + |c|²·Re τ(y*y). -/
theorem UHF_trace_discriminant (x y : TimelessFieldCompletion) (c : ℂ) :
    0 ≤ (UHF_trace (star x * x)).re
          - 2 * (c * star (UHF_trace (star y * x))).re
          + Complex.normSq c * (UHF_trace (star y * y)).re := by
  have hpos := UHF_trace_star_mul_self_nonneg (x - c • y)
  rw [UHF_trace_expand x y c, UHF_trace_inner_conj x y] at hpos
  have hre := (Complex.nonneg_iff.mp hpos).1
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply] at hre ⊢
  linarith [hre]

/-! ## §5 — M2.c: the real quadratic-discriminant auxiliary -/

/-- **r102.o (auxiliary)**: if the real quadratic
    `p − 2ts + t²sq` is nonnegative for every real `t`, with
    `p, q, s ≥ 0`, then `s ≤ p·q`. Via mathlib's `discrim_le_zero`. -/
private lemma quadratic_aux (p q s : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : 0 ≤ s)
    (h : ∀ t : ℝ, 0 ≤ p - 2 * (t * s) + t ^ 2 * s * q) : s ≤ p * q := by
  have hd : discrim (s * q) (-(2 * s)) p ≤ 0 := by
    apply discrim_le_zero
    intro t
    nlinarith [h t]
  rw [discrim] at hd
  rcases hs.eq_or_lt with hs0 | hspos
  · rw [← hs0]
    exact mul_nonneg hp hq
  · nlinarith [hd, hspos]

/-! ## §6 — M2.d: CAUCHY–SCHWARZ for the substrate UHF trace -/

/-- **★★★ r102.p: CAUCHY–SCHWARZ FOR THE SUBSTRATE UHF TRACE ★★★**

    `‖τ_UHF(y*·x)‖² ≤ Re τ_UHF(x*·x) · Re τ_UHF(y*·y)`

    for every x, y in the substrate UHF C*-algebra completion.

    Proof: the r102.n discriminant inequality along the real ray
    c = t · τ_UHF(y*·x) (t : ℝ) yields the real quadratic
    `0 ≤ p − 2ts + t²sq` with `p = Re τ(x*x)`, `q = Re τ(y*y)`,
    `s = |τ(y*x)|²`; the r102.o discriminant argument closes. -/
theorem UHF_trace_cauchySchwarz (x y : TimelessFieldCompletion) :
    ‖UHF_trace (star y * x)‖ ^ 2 ≤
      (UHF_trace (star x * x)).re * (UHF_trace (star y * y)).re := by
  have hp : 0 ≤ (UHF_trace (star x * x)).re :=
    (Complex.nonneg_iff.mp (UHF_trace_star_mul_self_nonneg x)).1
  have hq : 0 ≤ (UHF_trace (star y * y)).re :=
    (Complex.nonneg_iff.mp (UHF_trace_star_mul_self_nonneg y)).1
  have hs : 0 ≤ Complex.normSq (UHF_trace (star y * x)) :=
    Complex.normSq_nonneg _
  have hmaster : ∀ t : ℝ,
      0 ≤ (UHF_trace (star x * x)).re
            - 2 * (t * Complex.normSq (UHF_trace (star y * x)))
            + t ^ 2 * Complex.normSq (UHF_trace (star y * x))
              * (UHF_trace (star y * y)).re := by
    intro t
    have hm := UHF_trace_discriminant x y ((t : ℂ) * UHF_trace (star y * x))
    have h1 : (((t : ℂ) * UHF_trace (star y * x))
        * star (UHF_trace (star y * x))).re
        = t * Complex.normSq (UHF_trace (star y * x)) := by
      simp only [Complex.star_def, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.normSq_apply]
      ring
    have h2 : Complex.normSq ((t : ℂ) * UHF_trace (star y * x))
        = t ^ 2 * Complex.normSq (UHF_trace (star y * x)) := by
      rw [Complex.normSq_mul, Complex.normSq_ofReal]
      ring
    rw [h1, h2] at hm
    exact hm
  rw [Complex.sq_norm]
  exact quadratic_aux _ _ _ hp hq hs hmaster

/-! ## §7 — M2.e: trace-null left-ideal absorption -/

/-- **★★★ r102.q: TRACE-NULL LEFT-IDEAL ABSORPTION ★★★**

    If `τ_UHF(x*·x) = 0` then `τ_UHF((a·x)*·(a·x)) = 0` for every
    a — the trace-null cone absorbs left multiplication, the kernel
    form of "the trace-null set is a left ideal".

    Proof: Cauchy–Schwarz with y := a*·a·x gives
    ‖τ_UHF((a·x)*·(a·x))‖² ≤ Re τ_UHF(x*·x) · (…) = 0. -/
theorem UHF_trace_null_left_absorption (a x : TimelessFieldCompletion)
    (hx : UHF_trace (star x * x) = 0) :
    UHF_trace (star (a * x) * (a * x)) = 0 := by
  have hcs := UHF_trace_cauchySchwarz x (star a * a * x)
  have hyx : star (star a * a * x) * x = star (a * x) * (a * x) := by
    simp only [star_mul, star_star, mul_assoc]
  rw [hyx, hx] at hcs
  simp only [Complex.zero_re, zero_mul] at hcs
  have hnn : 0 ≤ ‖UHF_trace (star (a * x) * (a * x))‖ := norm_nonneg _
  have hle : ‖UHF_trace (star (a * x) * (a * x))‖ ≤ 0 := by
    nlinarith [hcs, hnn]
  exact norm_eq_zero.mp (le_antisymm hle hnn)

/-! ## §8 — r102 capstone -/

/-- **★★★ r102 SUBSTRATE UHF TRACE LINEARITY + CAUCHY–SCHWARZ
    CAPSTONE ★★★**

    Bundles the r102 substrate content:

      (L1) `substrate_pre_trace_smul` — pre-trace ℂ-homogeneity.
      (L2) `UHF_trace_add` — completion-tier additivity.
      (L3) `UHF_trace_smul` — completion-tier ℂ-homogeneity.
      (L4) `UHF_trace_zero` + `UHF_trace_neg` + `UHF_trace_sub`.
      (C1) `traceInner_self_nonneg` — pairing positivity (ComplexOrder).
      (C2) `UHF_trace_inner_conj` — conjugate symmetry.
      (C3) **`UHF_trace_cauchySchwarz`** — Cauchy–Schwarz for τ_UHF.
      (C4) **`UHF_trace_null_left_absorption`** — trace-null
           left-ideal absorption in kernel form.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r102 supplies the analytic engine of the
    completion-tier faithfulness route isolated by r100. With τ_UHF
    now ℂ-LINEAR on the full completion and satisfying CAUCHY–SCHWARZ,
    the trace-null set N = {x : τ(x*x) = 0} is closed (r101) and
    absorbs left multiplication (r102.q); the remaining steps to the
    r100 residual are two-sided absorption via traciality, additive
    closure of N via Cauchy–Schwarz, and the simplicity argument. -/
theorem r102_substrate_UHF_trace_cauchy_schwarz_capstone :
    (∀ (c : ℂ) (x : TimelessFieldRing),
      substrate_pre_trace (c • x) = c * substrate_pre_trace x) ∧
    (∀ x y : TimelessFieldCompletion,
      UHF_trace (x + y) = UHF_trace x + UHF_trace y) ∧
    (∀ (c : ℂ) (x : TimelessFieldCompletion),
      UHF_trace (c • x) = c * UHF_trace x) ∧
    (∀ x y : TimelessFieldCompletion,
      UHF_trace (x - y) = UHF_trace x - UHF_trace y) ∧
    (∀ x : TimelessFieldCompletion, 0 ≤ traceInner x x) ∧
    (∀ x y : TimelessFieldCompletion,
      UHF_trace (star x * y) = star (UHF_trace (star y * x))) ∧
    (∀ x y : TimelessFieldCompletion,
      ‖UHF_trace (star y * x)‖ ^ 2 ≤
        (UHF_trace (star x * x)).re * (UHF_trace (star y * y)).re) ∧
    (∀ a x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 →
      UHF_trace (star (a * x) * (a * x)) = 0) :=
  ⟨substrate_pre_trace_smul,
   UHF_trace_add,
   UHF_trace_smul,
   UHF_trace_sub,
   traceInner_self_nonneg,
   UHF_trace_inner_conj,
   UHF_trace_cauchySchwarz,
   UHF_trace_null_left_absorption⟩

/-! ## §9 — Axiom audit -/

#print axioms substrate_pre_trace_smul
#print axioms UHF_trace_add
#print axioms UHF_trace_smul
#print axioms UHF_trace_zero
#print axioms UHF_trace_neg
#print axioms UHF_trace_sub
#print axioms UHF_trace_linearMap
#print axioms traceInner_self_nonneg
#print axioms traceInner_self_re_nonneg
#print axioms traceInner_self_im_zero
#print axioms UHF_trace_inner_conj
#print axioms UHF_trace_expand
#print axioms UHF_trace_discriminant
#print axioms UHF_trace_cauchySchwarz
#print axioms UHF_trace_null_left_absorption
#print axioms r102_substrate_UHF_trace_cauchy_schwarz_capstone

end SubstrateUHFTraceCauchySchwarz
end PrincipiaTractalis
