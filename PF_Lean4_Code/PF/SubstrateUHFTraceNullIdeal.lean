/-
# r103: Substrate UHF trace — the TRACE-NULL TWO-SIDED IDEAL and
#       FAITHFULNESS FROM SIMPLICITY

★ 2026-07-21 r103 — Milestones M3 + M4 of the completion-tier
faithfulness route (Cauchy–Schwarz → trace-null ideal → simplicity →
faithfulness) ★

## The framework-first content

r101 defined the trace-null set N = {x : τ_UHF(x*·x) = 0} on the
substrate UHF C*-algebra completion, proved it closed, 0 ∈ N, 1 ∉ N.
r102 delivered completion-tier ℂ-linearity, Cauchy–Schwarz for the
trace pairing, and left-ideal absorption of N in kernel form. r103
completes the ALGEBRAIC layer of the r100 faithfulness route:

**M3 — N is a two-sided ideal (mathlib-native)**:
  * `traceNull_add_mem` — N is closed under addition, via the
    sesquilinear expansion of τ((x+y)*·(x+y)) (r102 linearity) with
    both cross terms killed by Cauchy–Schwarz (r102.p).
  * `traceNull_star_mem` — N is *-closed: (x*)*·(x*) = x·x* and
    τ(x·x*) = τ(x*·x) by r94 traciality.
  * `traceNull_right_absorption` — N absorbs RIGHT multiplication:
    right absorption = star ∘ left absorption (r102.q) ∘ star.
  * `traceNull_smul_mem`, `traceNull_neg_mem`, `traceNull_zero_mem` —
    ℂ-scalar, negation, and zero closure.
  * **`traceNullTwoSidedIdeal : TwoSidedIdeal TimelessFieldCompletion`**
    — the trace-null set bundled as a mathlib-native `TwoSidedIdeal`
    via `TwoSidedIdeal.mk'` (carrier `substrate_UHF_trace_null_set`).
  * `traceNullTwoSidedIdeal_ne_top` — the ideal is PROPER, from the
    r101.g unital non-membership 1 ∉ N.

**M4 — faithfulness from simplicity (the honest theorem)**:
  * **`UHF_trace_faithful_of_simple`** — IF the substrate UHF
    C*-algebra completion is algebraically simple (every two-sided
    ideal is ⊥ or ⊤), THEN τ_UHF is faithful:
    τ_UHF(x*·x) = 0 → x = 0.

    The simplicity hypothesis here is REAL algebraic simplicity of
    `TimelessFieldCompletion` — a meaningful open assumption whose
    classical realization is Glimm's UHF simplicity theorem (Glimm
    1960: every UHF C*-algebra is simple) — NOT a self-referential
    Prop marker. Everything downstream of the hypothesis is
    kernel-verified: simplicity + properness forces
    `traceNullTwoSidedIdeal = ⊥`, and ⊥-membership of any trace-null
    x forces x = 0.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-21 r103 — the substrate UHF trace-null two-sided ideal
+ faithfulness of τ_UHF conditional on genuine algebraic simplicity.
-/

import PF.SubstrateUHFTraceCauchySchwarz
import PF.SubstrateUHFCompletionSimplicityDischarge
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateUHFTraceNullIdeal

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open SubstrateUHFBoundedTrace SubstrateUHFTraceLipschitz
open SubstrateUHFCompletionTrace SubstrateUHFPreTraceDirectLimit
open SubstrateUHFTraceIsTracial SubstrateUHFTraceIsStarPreserving
open SubstrateUHFTraceIsPositive SubstrateUHFTraceCauchySchwarz
open SubstrateUHFCompletionSimplicityDischarge
open SubstrateDirectLimit SubstrateTimelessFieldCompletion
open SubstrateTimelessFieldNorm

/-! ## §1 — M3.a: cross-term vanishing and additive closure -/

/-- **r103.a (auxiliary): trace-null cross-term vanishing** —
    if `τ_UHF(x*·x) = 0` then `τ_UHF(y*·x) = 0` for EVERY y, by
    Cauchy–Schwarz: ‖τ(y*·x)‖² ≤ Re τ(x*·x) · Re τ(y*·y) = 0. -/
theorem UHF_trace_null_cross_left (x y : TimelessFieldCompletion)
    (hx : UHF_trace (star x * x) = 0) :
    UHF_trace (star y * x) = 0 := by
  have hcs := UHF_trace_cauchySchwarz x y
  rw [hx] at hcs
  simp only [Complex.zero_re, zero_mul] at hcs
  have hnn : 0 ≤ ‖UHF_trace (star y * x)‖ := norm_nonneg _
  have hle : ‖UHF_trace (star y * x)‖ ≤ 0 := by nlinarith [hcs, hnn]
  exact norm_eq_zero.mp (le_antisymm hle hnn)

/-- **r103.b (auxiliary): the mirrored cross term also vanishes** —
    if `τ_UHF(x*·x) = 0` then `τ_UHF(x*·y) = 0` for every y, via
    r102.l conjugate symmetry applied to r103.a. -/
theorem UHF_trace_null_cross_right (x y : TimelessFieldCompletion)
    (hx : UHF_trace (star x * x) = 0) :
    UHF_trace (star x * y) = 0 := by
  rw [UHF_trace_inner_conj x y, UHF_trace_null_cross_left x y hx, star_zero]

/-- **★★★ r103.c: TRACE-NULL ADDITIVE CLOSURE ★★★**

    If `τ_UHF(x*·x) = 0` and `τ_UHF(y*·y) = 0` then
    `τ_UHF((x+y)*·(x+y)) = 0`.

    Proof: expand `(x+y)*·(x+y) = x*x + x*y + y*x + y*y` by ring
    distributivity, push τ through with r102 additivity, and kill
    both cross terms with Cauchy–Schwarz (r103.a/r103.b). -/
theorem traceNull_add_mem (x y : TimelessFieldCompletion)
    (hx : UHF_trace (star x * x) = 0)
    (hy : UHF_trace (star y * y) = 0) :
    UHF_trace (star (x + y) * (x + y)) = 0 := by
  have h_alg : star (x + y) * (x + y) =
      star x * x + star x * y + star y * x + star y * y := by
    rw [star_add, add_mul, mul_add, mul_add]
    abel
  rw [h_alg, UHF_trace_add, UHF_trace_add, UHF_trace_add,
      hx, hy,
      UHF_trace_null_cross_left x y hx,
      UHF_trace_null_cross_right x y hx]
  ring

/-! ## §2 — M3.b: star closure and right absorption -/

/-- **r103.d: TRACE-NULL STAR CLOSURE** — if `τ_UHF(x*·x) = 0` then
    `τ_UHF((x*)*·(x*)) = 0`, since `(x*)*·(x*) = x·x*` and
    `τ(x·x*) = τ(x*·x)` by r94 traciality. -/
theorem traceNull_star_mem (x : TimelessFieldCompletion)
    (hx : UHF_trace (star x * x) = 0) :
    UHF_trace (star (star x) * star x) = 0 := by
  rw [star_star, UHF_trace_mul_comm]
  exact hx

/-- **★★★ r103.e: TRACE-NULL RIGHT-IDEAL ABSORPTION ★★★**

    If `τ_UHF(x*·x) = 0` then `τ_UHF((x·a)*·(x·a)) = 0` for every a —
    the trace-null cone absorbs right multiplication.

    Proof: right absorption = star ∘ left absorption ∘ star.
    `x* ∈ N` (r103.d), so `a*·x* ∈ N` (r102.q left absorption), so
    `(a*·x*)* = x·a ∈ N` (r103.d again). -/
theorem traceNull_right_absorption (a x : TimelessFieldCompletion)
    (hx : UHF_trace (star x * x) = 0) :
    UHF_trace (star (x * a) * (x * a)) = 0 := by
  have h1 : UHF_trace (star (star x) * star x) = 0 :=
    traceNull_star_mem x hx
  have h2 : UHF_trace (star (star a * star x) * (star a * star x)) = 0 :=
    UHF_trace_null_left_absorption (star a) (star x) h1
  have h3 : UHF_trace
      (star (star (star a * star x)) * star (star a * star x)) = 0 :=
    traceNull_star_mem (star a * star x) h2
  have h_eq : star (star a * star x) = x * a := by
    rw [star_mul, star_star, star_star]
  rw [h_eq] at h3
  exact h3

/-! ## §3 — M3.c: scalar, negation, and zero closure -/

/-- **r103.f: TRACE-NULL ℂ-SCALAR CLOSURE** — if `τ_UHF(x*·x) = 0`
    then `τ_UHF((c•x)*·(c•x)) = 0`, via `star_smul` (r58 StarModule)
    + r102 ℂ-homogeneity. -/
theorem traceNull_smul_mem (c : ℂ) (x : TimelessFieldCompletion)
    (hx : UHF_trace (star x * x) = 0) :
    UHF_trace (star (c • x) * (c • x)) = 0 := by
  have h_alg : star (c • x) * (c • x) = (star c * c) • (star x * x) := by
    rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [h_alg, UHF_trace_smul, hx, mul_zero]

/-- **r103.g: TRACE-NULL NEGATION CLOSURE** — if `τ_UHF(x*·x) = 0`
    then `τ_UHF((-x)*·(-x)) = 0`, since `(-x)*·(-x) = x*·x`. -/
theorem traceNull_neg_mem (x : TimelessFieldCompletion)
    (hx : UHF_trace (star x * x) = 0) :
    UHF_trace (star (-x) * (-x)) = 0 := by
  rw [star_neg, neg_mul_neg]
  exact hx

/-- **r103.h: TRACE-NULL ZERO MEMBERSHIP** — `τ_UHF(0*·0) = 0`,
    from `star 0 * 0 = 0` + r102.d `UHF_trace 0 = 0` (a self-contained
    re-proof of r101.f through the r102 linearity layer). -/
theorem traceNull_zero_mem :
    UHF_trace (star (0 : TimelessFieldCompletion) * 0) = 0 := by
  rw [star_zero, zero_mul]
  exact UHF_trace_zero

/-! ## §4 — M3.d: the trace-null set as a mathlib-native TwoSidedIdeal -/

/-- **★★★ r103.i: THE TRACE-NULL TWO-SIDED IDEAL ★★★**

    The r101 trace-null set
    `substrate_UHF_trace_null_set = {x | τ_UHF(x*·x) = 0}` bundled as
    a mathlib-native `TwoSidedIdeal TimelessFieldCompletion` via
    `TwoSidedIdeal.mk'`:

      * zero: r103.h,
      * addition: r103.c (Cauchy–Schwarz cross-term kill),
      * negation: r103.g,
      * left absorption `x·y` for y null: r102.q,
      * right absorption `x·y` for x null: r103.e
        (star ∘ left absorption ∘ star). -/
noncomputable def traceNullTwoSidedIdeal :
    TwoSidedIdeal TimelessFieldCompletion :=
  TwoSidedIdeal.mk' substrate_UHF_trace_null_set
    traceNull_zero_mem
    (fun {x y} hx hy => traceNull_add_mem x y hx hy)
    (fun {x} hx => traceNull_neg_mem x hx)
    (fun {x y} hy => UHF_trace_null_left_absorption x y hy)
    (fun {x y} hx => traceNull_right_absorption y x hx)

/-- **r103.j: membership in the trace-null ideal is trace-nullity** —
    `x ∈ traceNullTwoSidedIdeal ↔ τ_UHF(x*·x) = 0`. -/
theorem mem_traceNullTwoSidedIdeal_iff (x : TimelessFieldCompletion) :
    x ∈ traceNullTwoSidedIdeal ↔ UHF_trace (star x * x) = 0 :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x

/-- **r103.k: THE TRACE-NULL IDEAL IS PROPER** —
    `traceNullTwoSidedIdeal ≠ ⊤`, from the r101.g unital
    non-membership `1 ∉ substrate_UHF_trace_null_set` via mathlib's
    `TwoSidedIdeal.one_mem_iff`. -/
theorem traceNullTwoSidedIdeal_ne_top : traceNullTwoSidedIdeal ≠ ⊤ := by
  intro h_top
  exact substrate_UHF_trace_null_set_one_not_mem
    ((mem_traceNullTwoSidedIdeal_iff 1).mp
      (traceNullTwoSidedIdeal.one_mem_iff.mpr h_top))

/-! ## §5 — M4: faithfulness from simplicity — THE PUNCHLINE -/

/-- **★★★ r103.l: THE SUBSTRATE UHF TRACE IS FAITHFUL, GIVEN
    ALGEBRAIC SIMPLICITY ★★★**

    IF every two-sided ideal of `TimelessFieldCompletion` is `⊥` or
    `⊤` (algebraic simplicity), THEN the substrate UHF trace is
    faithful: `τ_UHF(x*·x) = 0 → x = 0`.

    **Honesty note on the hypothesis.** The hypothesis
    `∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤`
    is REAL algebraic simplicity of the substrate UHF C*-algebra
    completion — a meaningful, currently OPEN assumption in this
    development. Its classical realization is Glimm's theorem (Glimm
    1960): every UHF C*-algebra is simple (indeed the C*-completion
    of an increasing union of full matrix algebras is simple, and for
    unital C*-algebras topological simplicity coincides with algebraic
    simplicity). This is NOT the retired self-referential Prop-marker
    pattern: nothing in the hypothesis mentions the trace or the
    conclusion, and every step from the hypothesis to the conclusion
    is kernel-verified here.

    Proof: `traceNullTwoSidedIdeal` is a two-sided ideal (r103.i)
    that is proper (r103.k); simplicity forces it to be `⊥`; any x
    with `τ_UHF(x*·x) = 0` lies in it (r103.j), hence in `⊥`, hence
    `x = 0` by `TwoSidedIdeal.mem_bot`. -/
theorem UHF_trace_faithful_of_simple
    (h_simple : ∀ I : TwoSidedIdeal TimelessFieldCompletion,
      I = ⊥ ∨ I = ⊤) :
    ∀ x : TimelessFieldCompletion,
      UHF_trace (star x * x) = 0 → x = 0 := by
  intro x hx
  have h_bot : traceNullTwoSidedIdeal = ⊥ :=
    (h_simple traceNullTwoSidedIdeal).resolve_right
      traceNullTwoSidedIdeal_ne_top
  have h_mem : x ∈ traceNullTwoSidedIdeal :=
    (mem_traceNullTwoSidedIdeal_iff x).mpr hx
  rw [h_bot] at h_mem
  exact (TwoSidedIdeal.mem_bot TimelessFieldCompletion).mp h_mem

/-- **r103.m: simplicity also discharges the r100 Φ3 substrate
    residual** — under the same algebraic-simplicity hypothesis, the
    r100 conjecture `τ_UHF(x*·x) = 0 → x*·x = 0` holds (immediately,
    since x = 0 forces `star x * x = 0`). -/
theorem substrate_conjecture_of_simple
    (h_simple : ∀ I : TwoSidedIdeal TimelessFieldCompletion,
      I = ⊥ ∨ I = ⊤) :
    ∀ x : TimelessFieldCompletion,
      UHF_trace (star x * x) = 0 → star x * x = 0 := by
  intro x hx
  have h0 : x = 0 := UHF_trace_faithful_of_simple h_simple x hx
  rw [h0, star_zero, zero_mul]

/-! ## §6 — r103 capstone -/

/-- **★★★ r103 SUBSTRATE UHF TRACE-NULL TWO-SIDED IDEAL +
    FAITHFULNESS-FROM-SIMPLICITY CAPSTONE ★★★**

    Bundles the r103 substrate content:

      (N1) `UHF_trace_null_cross_left` / `_right` — Cauchy–Schwarz
           cross-term vanishing against any trace-null element.
      (N2) `traceNull_add_mem` — additive closure of the trace-null
           set (kernel form).
      (N3) `traceNull_star_mem` — *-closure via r94 traciality.
      (N4) `traceNull_right_absorption` — right-ideal absorption =
           star ∘ left absorption (r102.q) ∘ star.
      (N5) `traceNull_smul_mem` + `traceNull_neg_mem` +
           `traceNull_zero_mem` — scalar/negation/zero closure.
      (N6) **`traceNullTwoSidedIdeal`** — the trace-null set as a
           mathlib-native `TwoSidedIdeal TimelessFieldCompletion`,
           with `mem_traceNullTwoSidedIdeal_iff` characterizing
           membership.
      (N7) `traceNullTwoSidedIdeal_ne_top` — properness from the
           r101.g unital non-membership.
      (N8) **`UHF_trace_faithful_of_simple`** — the substrate UHF
           trace is FAITHFUL conditional on genuine algebraic
           simplicity of `TimelessFieldCompletion` (classically:
           Glimm 1960 UHF simplicity), with every post-hypothesis
           step kernel-verified.
      (N9) `substrate_conjecture_of_simple` — the same hypothesis
           discharges the r100 Φ3 residual
           `SubstrateUHFCompletionPositiveFaithfulnessSubstrateConjecture`
           in statement form.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r103 completes the ALGEBRAIC layer of the
    completion-tier faithfulness route isolated by r100 and powered
    by the r102 analytic engine. The trace-null set — closed (r101),
    additively closed and two-sidedly absorbing (r102 + r103), proper
    (r101.g/r103.k) — is now a mathlib-native proper two-sided ideal.
    The ONLY remaining gap between the substrate development and
    unconditional completion-tier faithfulness of τ_UHF is the
    algebraic simplicity of the substrate UHF C*-algebra completion
    (Glimm 1960) — a single, honest, classical operator-algebraic
    input, stated as an explicit hypothesis, never as an axiom. -/
theorem r103_substrate_UHF_trace_null_ideal_capstone :
    (∀ x y : TimelessFieldCompletion, UHF_trace (star x * x) = 0 →
      UHF_trace (star y * x) = 0) ∧
    (∀ x y : TimelessFieldCompletion,
      UHF_trace (star x * x) = 0 → UHF_trace (star y * y) = 0 →
      UHF_trace (star (x + y) * (x + y)) = 0) ∧
    (∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 →
      UHF_trace (star (star x) * star x) = 0) ∧
    (∀ a x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 →
      UHF_trace (star (x * a) * (x * a)) = 0) ∧
    (∀ (c : ℂ) (x : TimelessFieldCompletion),
      UHF_trace (star x * x) = 0 →
      UHF_trace (star (c • x) * (c • x)) = 0) ∧
    (∀ x : TimelessFieldCompletion,
      x ∈ traceNullTwoSidedIdeal ↔ UHF_trace (star x * x) = 0) ∧
    traceNullTwoSidedIdeal ≠ ⊤ ∧
    ((∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤) →
      ∀ x : TimelessFieldCompletion,
        UHF_trace (star x * x) = 0 → x = 0) :=
  ⟨UHF_trace_null_cross_left,
   traceNull_add_mem,
   traceNull_star_mem,
   traceNull_right_absorption,
   traceNull_smul_mem,
   mem_traceNullTwoSidedIdeal_iff,
   traceNullTwoSidedIdeal_ne_top,
   UHF_trace_faithful_of_simple⟩

/-! ## §7 — Axiom audit -/

#print axioms UHF_trace_null_cross_left
#print axioms UHF_trace_null_cross_right
#print axioms traceNull_add_mem
#print axioms traceNull_star_mem
#print axioms traceNull_right_absorption
#print axioms traceNull_smul_mem
#print axioms traceNull_neg_mem
#print axioms traceNull_zero_mem
#print axioms traceNullTwoSidedIdeal
#print axioms mem_traceNullTwoSidedIdeal_iff
#print axioms traceNullTwoSidedIdeal_ne_top
#print axioms UHF_trace_faithful_of_simple
#print axioms substrate_conjecture_of_simple
#print axioms r103_substrate_UHF_trace_null_ideal_capstone

end SubstrateUHFTraceNullIdeal
end PrincipiaTractalis
