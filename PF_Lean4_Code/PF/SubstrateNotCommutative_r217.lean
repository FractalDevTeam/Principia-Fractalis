/-
# r217: the substrate is NOT commutative, and its Gelfand spectrum is EMPTY

★ 2026-08-08 r217 — an ADDITIVE, kernel-visible disclosure. One new file.
Nothing is deleted, weakened, renamed, or edited. Every declaration cited
below is imported by exact name and left exactly as it stands. ★

## What this file is about

`ch16_spectral_foundations.tex:340-349` proves that `T_∞` is nuclear by this
route:

    1. `T_∞` is commutative (functions commute pointwise)
    2. By Gelfand-Naimark, `T_∞ ≅ C₀(X)` for some space `X`
    3. Commutative C*-algebras are automatically nuclear
    4. Therefore, `T_∞` is nuclear

Step 1 is the hypothesis of the argument. **The substrate does not satisfy it.**

`ch04_timeless_field.tex:260-272` defines the Timeless Field as the projective
limit `T_∞ = ⟵lim (N(H_k) ⊗_min F_α)` — the UHF algebra `M_{3^∞}`,
noncommutative and simple. That is the object the machine-checked corpus
actually builds:

    PF/SubstrateBase3Levels.lean
      → PF/SubstrateDirectLimit.lean          (`TimelessFieldRing`, T_∞)
      → PF/SubstrateTimelessFieldCompletion.lean:82  (`TimelessFieldCompletion`)

and it is the object of `UHF_trace_faithful` and
`substrate_completion_simple_unconditional` (r112/r113).

§1-§2 below put step 1's failure in the kernel: two explicit matrix units at a
finite substrate level, pushed through the isometric level embedding
`ι_k = levelToCompletion k`, do not commute in `TimelessFieldCompletion`.

## THE NUCLEARITY CONCLUSION IS TRUE — the defect is the route, not the theorem

This must be said plainly, and it is the fair reading.
`ch16` Theorem `thm:timeless-field-nuclear` asserts that `T_∞` is nuclear, and
**that is correct** for the Chapter 4 substrate: UHF algebras are AF, and AF
C*-algebras are nuclear (Blackadar, *K-Theory for Operator Algebras*, 6.3.10).
The conclusion stands. What does not stand is the proof given for it: steps 1-3
establish nuclearity of a *commutative* algebra introduced in `ch16`, which is
not the substrate. The correct route for the substrate runs through AF-ness,
and the substrate-side input for that route is already in the corpus —
`substrate_UHF_denseRange` (r60), re-exported unchanged in §5 below.

This file therefore does **not** claim that `ch16`'s nuclearity theorem is
false. It claims that `ch16`'s *proof* is a proof about a different object.

## The attribution

`ch16:323-325` opens *"Recall from Chapter [timeless-field]:"* and then writes

    T_∞ = completion of ℂ[ζ(s), ζ*(1-s), e^{iπα D₃(n)}]

Chapter 4 does not define it that way. Nothing is being recalled; a second,
different object is being introduced under the same name.

## §4 — what the emptiness of the Gelfand spectrum means

`ch16:353-360` defines `Spec(T_∞)` to be the set of **nonzero multiplicative
linear functionals** `φ : T_∞ → ℂ`, and `ch16:362-369` says the Riemann zeros
are *"special points"* in it, at which `φ(ζ(s)) = 0`.

§4 proves, in the kernel, that for the substrate that set is **empty**. Not
"small", not "differently indexed" — empty. The argument is the standard one:
`ker φ` is a two-sided ideal; simplicity (r112, unconditional) forces it to be
`⊥` or `⊤`; `⊤` contradicts `φ ≠ 0`; `⊥` forces every element of the algebra to
be a scalar multiple of `1`, hence the algebra to be commutative, contradicting
§2.

So `ch16:363`'s "the Riemann zeros are special points in `Spec(T_∞)`" has no
referent for the substrate: there are no points at all to be special among.
This is **not** merely a switch between the Gelfand sense of "spectrum" (the
character space) and the operator-theoretic sense (`spectrum ℂ a` for a single
element `a`). The operator-theoretic spectra of substrate elements are perfectly
non-empty; it is the object `ch16:353` explicitly defines — the character
space — that is empty.

Note the shape of the last step: the emptiness proof needs an input saying the
algebra is not `ℂ`. Rather than assume infinite-dimensionality (which the
corpus does not formalize, and which this file therefore does not invent), §3
derives the needed input — "some element is not a scalar multiple of `1`" —
directly from the noncommutativity landed in §2. The result is
**unconditional**, with no added hypothesis.

## This is a known gap being made precise, not concealment

`ch16`'s own verification ledger, dated 2026-07-23 (`ch16:527-534`), already
flags it under **ASSERTED (not derived)**:

  > the construction of `T_∞` used *here* as a *commutative* algebra of
  > ζ-values differs from the noncommutative UHF substrate of
  > Chapter [timeless-field]; the "nuclear because commutative" argument is
  > not the machine-verified result.

r217 turns that prose disagreement into a kernel-checked one. See also
`codex/FRAMEWORK_TRANSLATION_2026-08-06.md`, §5 "THREE DEFECTS", item 2
("Two incompatible `T_∞`"), which is the comprehension-pass entry this stone
discharges.

## r102-r113 are untouched

`UHF_trace_faithful` and `substrate_completion_simple_unconditional`
(`PF/SubstrateCompletionFaithful.lean:328, :367`) are unconditional, are
imported here by exact name, and are **used** by §4 rather than modified. This
file adds; it subtracts nothing.

## Scope of what is landed here

  * §1 `matrix_level_not_commutative`   — matrix tier, every level `k ≥ 1`.
  * §2 `substrate_not_commutative`      — COMPLETION tier. `∃ a b, a*b ≠ b*a`.
  * §3 `substrate_not_scalar_line`      — the algebra is not the scalar line.
  * §4 `gelfandSpectrum_eq_empty`       — `Spec(T_∞) = ∅`, unconditional.
  * §5 re-export of the AF density witness (the correct nuclearity input).

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.

Stage 2026-08-08 r217 — substrate noncommutativity + empty Gelfand spectrum.
-/

import PF.SubstrateCompletionSimplicity
import PF.SubstrateCompletionFaithful
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateNotCommutative

open scoped Matrix.Norms.L2Operator
open Matrix
open SubstrateDirectLimit
open SubstrateTimelessFieldNorm
open SubstrateTimelessFieldCompletion
open SubstrateCompletionSimplicity
open SubstrateCompletionFaithful

/-! ## §1 — The matrix tier

At every substrate level `k ≥ 1` the level algebra
`M_{3^k}(ℂ) = Matrix (Fin (3^k)) (Fin (3^k)) ℂ` is noncommutative. The witness
is the order-sensitive matrix-unit pair already used at
`PF/SubstrateTraceUniqueness.lean:94-110`:

    E_{ij} · E_{jj} = E_{ij}        E_{jj} · E_{ij} = 0     (i ≠ j)

with `E_{ij} = Matrix.single i j 1`. -/

/-- **r217.a — two distinct indices exist at every level `k ≥ 1`.**
    `3^k ≥ 3`, so `0` and `1` are both valid indices of `Fin (3^k)`. -/
theorem three_le_three_pow (k : ℕ) (hk : 0 < k) : 3 ≤ 3 ^ k := by
  simpa using Nat.pow_le_pow_right (by norm_num : 0 < 3) hk

/-- **r217.b — the matrix unit `E_{ij}` is nonzero.**
    Its `(i,j)` entry is `1 ≠ 0`. -/
theorem single_one_ne_zero {n : ℕ} (i j : Fin n) :
    (single i j (1 : ℂ) : Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
  intro hcon
  have h2 : (single i j (1 : ℂ) : Matrix (Fin n) (Fin n) ℂ) i j
      = (0 : Matrix (Fin n) (Fin n) ℂ) i j := by rw [hcon]
  rw [single_apply_same, Matrix.zero_apply] at h2
  exact one_ne_zero h2

/-- **★ r217.1 — MATRIX TIER: the substrate level algebra is not commutative ★**

    For every level `k ≥ 1` there exist `A B : M_{3^k}(ℂ)` with `A*B ≠ B*A`.
    The witnesses are the matrix units `E_{01}` and `E_{11}`:
    `E_{01} · E_{11} = E_{01} ≠ 0 = E_{11} · E_{01}`. -/
theorem matrix_level_not_commutative (k : ℕ) (hk : 0 < k) :
    ∃ A B : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ, A * B ≠ B * A := by
  have h3 : 3 ≤ 3 ^ k := three_le_three_pow k hk
  let i : Fin (3 ^ k) := ⟨0, by omega⟩
  let j : Fin (3 ^ k) := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  refine ⟨single i j (1 : ℂ), single j j (1 : ℂ), ?_⟩
  have hAB : (single i j (1 : ℂ) : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ)
      * single j j (1 : ℂ) = single i j (1 : ℂ) := by
    rw [single_mul_single_same, mul_one]
  have hBA : (single j j (1 : ℂ) : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ)
      * single i j (1 : ℂ) = 0 :=
    single_mul_single_of_ne (1 : ℂ) j j i (Ne.symm hij) (1 : ℂ)
  rw [hAB, hBA]
  exact single_one_ne_zero i j

/-! ## §2 — Transport to the completion tier

`levelToCompletion k : M_{3^k}(ℂ) →+* T∞̂` (r106.c,
`PF/SubstrateCompletionSimplicity.lean:155`) is a ring homomorphism, and
`levelToCompletion_norm` (r106.f, `:208`) says it is norm-preserving. A
norm-preserving additive map is injective, so the §1 witnesses survive
transport. -/

/-- **r217.c — the level embedding into the completion is injective.**
    Immediate from `levelToCompletion_norm` (`‖ι_k A‖ = ‖A‖`): if
    `ι_k X = ι_k Y` then `‖X - Y‖ = ‖ι_k (X - Y)‖ = 0`. -/
theorem levelToCompletion_injective (k : ℕ) :
    Function.Injective (levelToCompletion k) := by
  intro X Y h
  have hz : ‖X - Y‖ = 0 := by
    rw [← levelToCompletion_norm k (X - Y), map_sub, h, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- **★★★ r217.2 — COMPLETION TIER: THE SUBSTRATE IS NOT COMMUTATIVE ★★★**

    `∃ a b : TimelessFieldCompletion, a * b ≠ b * a`.

    This is the direct contradiction of `ch16:342` step 1
    (*"`T_∞` is commutative (functions commute pointwise)"*) for the object
    Chapter 4 defines and the corpus builds.

    Witnesses: the images under `ι_1 = levelToCompletion 1` of the level-1
    matrix units `E_{01}, E_{11} ∈ M_3(ℂ)`. -/
theorem substrate_not_commutative :
    ∃ a b : TimelessFieldCompletion, a * b ≠ b * a := by
  obtain ⟨A, B, hAB⟩ := matrix_level_not_commutative 1 Nat.one_pos
  refine ⟨levelToCompletion 1 A, levelToCompletion 1 B, ?_⟩
  intro hcon
  rw [← map_mul, ← map_mul] at hcon
  exact hAB (levelToCompletion_injective 1 hcon)

/-- **r217.2′ — the same fact in universally quantified form**, which is
    literally the negation of `ch16:342` step 1. -/
theorem ch16_step1_commutativity_fails :
    ¬ (∀ a b : TimelessFieldCompletion, a * b = b * a) := by
  intro hcomm
  obtain ⟨a, b, hab⟩ := substrate_not_commutative
  exact hab (hcomm a b)

/-! ## §3 — The substrate is not the scalar line

The emptiness argument in §4 needs one input beyond simplicity: that the
algebra is not isomorphic to `ℂ`. The textbook input for this is
infinite-dimensionality. The corpus does not formalize
infinite-dimensionality of `TimelessFieldCompletion`, and this file does not
invent it. Instead §3 derives the *exact* input §4 consumes — some element is
not a scalar multiple of `1` — from §2, which is already landed. Nothing is
assumed. -/

/-- **★ r217.3 — some substrate element is not a scalar multiple of `1` ★**

    If every element were `c • 1`, the algebra would be commutative (scalars
    commute), contradicting §2. -/
theorem substrate_not_scalar_line :
    ∃ x : TimelessFieldCompletion, ∀ c : ℂ, x ≠ c • (1 : TimelessFieldCompletion) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, b, hab⟩ := substrate_not_commutative
  obtain ⟨c, hc⟩ := hcon a
  obtain ⟨d, hd⟩ := hcon b
  apply hab
  have hcA : c • (1 : TimelessFieldCompletion)
      = algebraMap ℂ TimelessFieldCompletion c :=
    (Algebra.algebraMap_eq_smul_one c).symm
  have hdA : d • (1 : TimelessFieldCompletion)
      = algebraMap ℂ TimelessFieldCompletion d :=
    (Algebra.algebraMap_eq_smul_one d).symm
  rw [hc, hd, hcA, hdA]
  calc algebraMap ℂ TimelessFieldCompletion c * algebraMap ℂ TimelessFieldCompletion d
      = algebraMap ℂ TimelessFieldCompletion (c * d) := (map_mul _ _ _).symm
    _ = algebraMap ℂ TimelessFieldCompletion (d * c) := by rw [mul_comm]
    _ = algebraMap ℂ TimelessFieldCompletion d * algebraMap ℂ TimelessFieldCompletion c :=
        map_mul _ _ _

/-! ## §4 — `Spec(T_∞)` as `ch16:353` defines it is EMPTY

`ch16:353-357`:

  > The **spectrum** `Spec(T_∞)` is the set of all nonzero multiplicative
  > linear functionals `φ : T_∞ → ℂ`, `φ(AB) = φ(A)φ(B)`.

We take that definition literally: additive, ℂ-homogeneous, multiplicative,
nonzero. -/

/-- **r217.d — an additive functional kills `0`.** -/
theorem additive_map_zero (φ : TimelessFieldCompletion → ℂ)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) : φ 0 = 0 := by
  have h := hadd 0 0
  rw [add_zero] at h
  linear_combination -h

/-- **r217.e — an additive functional negates.** -/
theorem additive_map_neg (φ : TimelessFieldCompletion → ℂ)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (x : TimelessFieldCompletion) :
    φ (-x) = - φ x := by
  have h := hadd x (-x)
  rw [add_neg_cancel, additive_map_zero φ hadd] at h
  linear_combination -h

/-- **r217.f — an additive functional subtracts.** -/
theorem additive_map_sub (φ : TimelessFieldCompletion → ℂ)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (x y : TimelessFieldCompletion) :
    φ (x - y) = φ x - φ y := by
  rw [sub_eq_add_neg, hadd, additive_map_neg φ hadd, sub_eq_add_neg]

/-- **★ r217.4 — `ker φ` IS A TWO-SIDED IDEAL ★**

    For `φ` additive and multiplicative, the set `{x | φ x = 0}` is the
    carrier of a genuine `TwoSidedIdeal TimelessFieldCompletion`. This is the
    step `ch16` would need and does not take: it is exactly what makes
    simplicity bite.

    `φ a = 0 ⟹ φ (b*a) = φ b · φ a = 0` and `φ (a*b) = φ a · φ b = 0`. -/
theorem ker_multiplicative_is_twoSided
    (φ : TimelessFieldCompletion → ℂ)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    (hmul : ∀ x y, φ (x * y) = φ x * φ y) :
    ∃ I : TwoSidedIdeal TimelessFieldCompletion, ∀ x, x ∈ I ↔ φ x = 0 := by
  refine ⟨TwoSidedIdeal.mk' {x : TimelessFieldCompletion | φ x = 0}
      (additive_map_zero φ hadd)
      (fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [hadd, hx, hy, add_zero])
      (fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [additive_map_neg φ hadd, hx, neg_zero])
      (fun {x y} hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        rw [hmul, hy, mul_zero])
      (fun {x y} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [hmul, hx, zero_mul]), ?_⟩
  intro x
  simp

/-- **r217.g — a nonzero multiplicative functional is unital.**
    From `φ a = φ (a * 1) = φ a · φ 1` and `φ a ≠ 0`. -/
theorem multiplicative_map_one
    (φ : TimelessFieldCompletion → ℂ)
    (hmul : ∀ x y, φ (x * y) = φ x * φ y)
    (a : TimelessFieldCompletion) (ha : φ a ≠ 0) : φ 1 = 1 := by
  have h : φ a = φ a * φ 1 := by
    conv_lhs => rw [← mul_one a]
    rw [hmul]
  have h2 : φ a * (1 - φ 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 ha
  · linear_combination -h3

/-- **★★★ r217.5 — EVERY MULTIPLICATIVE LINEAR FUNCTIONAL ON THE SUBSTRATE
    IS ZERO ★★★**

    Unconditional. The chain:

      * `ker φ` is a two-sided ideal                     (r217.4)
      * simplicity: `ker φ = ⊥` or `ker φ = ⊤`           (r112,
        `substrate_completion_simple_unconditional`, unconditional, untouched)
      * `ker φ = ⊤` gives `φ 1 = 0`, hence `φ = 0`
      * `ker φ = ⊥` gives `x = φ x • 1` for every `x`, i.e. the algebra is the
        scalar line — refuted by r217.3, which is refuted by r217.2.

    No infinite-dimensionality hypothesis is assumed: the "not `ℂ`" input is
    supplied by noncommutativity. -/
theorem no_nonzero_multiplicative_functional
    (φ : TimelessFieldCompletion → ℂ)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    (hsmul : ∀ (c : ℂ) (x : TimelessFieldCompletion), φ (c • x) = c * φ x)
    (hmul : ∀ x y, φ (x * y) = φ x * φ y) :
    ∀ x, φ x = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, ha⟩ := hcon
  have hone : φ 1 = 1 := multiplicative_map_one φ hmul a ha
  obtain ⟨I, hI⟩ := ker_multiplicative_is_twoSided φ hadd hmul
  rcases substrate_completion_simple_unconditional I with hbot | htop
  · -- `ker φ = ⊥`: every element is a scalar multiple of `1`.
    have hspan : ∀ x : TimelessFieldCompletion,
        x = φ x • (1 : TimelessFieldCompletion) := by
      intro x
      have hmem : (x - φ x • (1 : TimelessFieldCompletion)) ∈ I := by
        rw [hI]
        rw [additive_map_sub φ hadd, hsmul, hone, mul_one, sub_self]
      rw [hbot, TwoSidedIdeal.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
    obtain ⟨y, hy⟩ := substrate_not_scalar_line
    exact hy (φ y) (hspan y)
  · -- `ker φ = ⊤`: then `1 ∈ ker φ`, contradicting `φ 1 = 1`.
    have hmem : (1 : TimelessFieldCompletion) ∈ I := by
      rw [htop]; exact TwoSidedIdeal.mem_top TimelessFieldCompletion
    rw [hI, hone] at hmem
    exact one_ne_zero hmem

/-- **The set `ch16:353` calls `Spec(T_∞)`** — the nonzero multiplicative
    ℂ-linear functionals on the substrate, transcribed literally. -/
def GelfandSpectrum : Set (TimelessFieldCompletion →ₗ[ℂ] ℂ) :=
  {φ | φ ≠ 0 ∧ ∀ a b : TimelessFieldCompletion, φ (a * b) = φ a * φ b}

/-- **★★★ r217.6 — `Spec(T_∞) = ∅` ★★★**

    For the substrate — the Chapter 4 UHF algebra that the corpus builds —
    the set `ch16:353` defines as the spectrum has no elements at all.

    Consequence for `ch16:362-369`: *"The Riemann zeros are special points in
    `Spec(T_∞)`"* has no referent. There are no points. This is not a switch
    between the Gelfand and operator-theoretic senses of "spectrum": the
    operator-theoretic spectrum `spectrum ℂ a` of a substrate element is a
    different object and is not claimed empty here. It is the character space
    — the object `ch16:353` explicitly writes down — that is empty. -/
theorem gelfandSpectrum_eq_empty : GelfandSpectrum = ∅ := by
  ext φ
  simp only [GelfandSpectrum, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
    not_and]
  intro hne hmul
  refine hne (LinearMap.ext fun x => ?_)
  have := no_nonzero_multiplicative_functional (fun y => φ y)
    (fun x y => map_add φ x y)
    (fun c x => by simp [map_smul φ c x])
    hmul x
  simpa using this

/-- **r217.6′ — the existential form**, matching the shape asked for in the
    r217 brief: there is no nonzero multiplicative ℂ-linear functional. -/
theorem no_nonzero_multiplicative_linear_functional :
    ¬ ∃ φ : TimelessFieldCompletion →ₗ[ℂ] ℂ,
        φ ≠ 0 ∧ ∀ a b : TimelessFieldCompletion, φ (a * b) = φ a * φ b := by
  intro h
  obtain ⟨φ, hφ⟩ := h
  have : φ ∈ GelfandSpectrum := hφ
  rw [gelfandSpectrum_eq_empty] at this
  exact this

/-! ## §5 — What the CORRECT nuclearity route needs, already in the corpus

Re-exported unchanged from `PF/SubstrateTimelessFieldCompletion.lean:644`
(r60). This is the AF/UHF density witness: `TimelessFieldCompletion` is the
norm closure of the union of its finite-dimensional matrix levels. AF ⟹
nuclear is the classical route that *does* apply to the substrate.

This is a re-export, not a nuclearity proof. Mathlib has no `Nuclear`
typeclass, no C*-tensor products, and no Choi-Effros; the r60 docstring says
so and nothing here changes that. -/

/-- **r217.7 — the substrate is the norm closure of its finite matrix levels.**
    A re-export of `substrate_UHF_denseRange` (r60), stated here only to make
    visible, in the same file as the defect, that the input to the correct
    (AF-based) nuclearity argument is already kernel-checked. This theorem does
    NOT assert nuclearity. -/
theorem substrate_is_norm_closure_of_finite_matrix_levels :
    DenseRange (fun p : (Σ k : ℕ, Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) =>
      ((substrateLevelToTimelessField p.1 p.2 : TimelessFieldRing) :
        TimelessFieldCompletion)) :=
  substrate_UHF_denseRange

/-! ## §6 — r217 capstone -/

/-- **★★★ r217 CAPSTONE ★★★**

    Bundles, for the substrate `TimelessFieldCompletion` (= the Chapter 4 UHF
    algebra `M_{3^∞}`, the object the corpus builds):

      (N1) `∃ a b, a * b ≠ b * a`      — `ch16:342` step 1 is FALSE here.
      (N2) `¬ ∀ a b, a * b = b * a`    — the same, universally quantified.
      (N3) `∃ x, ∀ c, x ≠ c • 1`       — the algebra is not the scalar line.
      (N4) `GelfandSpectrum = ∅`       — `ch16:353`'s `Spec(T_∞)` is empty,
                                         so `ch16:363` has no referent.
      (N5) the AF density witness (r60), re-exported — the input to the
           CORRECT nuclearity route, which is why `ch16`'s nuclearity
           CONCLUSION nonetheless stands.

    Kernel-only `[propext, Classical.choice, Quot.sound]`. Zero project
    axioms. Zero sorries. -/
theorem r217_substrate_not_commutative_capstone :
    (∃ a b : TimelessFieldCompletion, a * b ≠ b * a) ∧
    (¬ (∀ a b : TimelessFieldCompletion, a * b = b * a)) ∧
    (∃ x : TimelessFieldCompletion, ∀ c : ℂ, x ≠ c • (1 : TimelessFieldCompletion)) ∧
    GelfandSpectrum = ∅ ∧
    DenseRange (fun p : (Σ k : ℕ, Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) =>
      ((substrateLevelToTimelessField p.1 p.2 : TimelessFieldRing) :
        TimelessFieldCompletion)) :=
  ⟨substrate_not_commutative,
   ch16_step1_commutativity_fails,
   substrate_not_scalar_line,
   gelfandSpectrum_eq_empty,
   substrate_is_norm_closure_of_finite_matrix_levels⟩

/-! ## §7 — Axiom audit

Every theorem in this file, with its axiom set. All must be
⊆ `[propext, Classical.choice, Quot.sound]`. No `sorry`, no `native_decide`,
no `axiom` declared here.
-/

-- §1
#print axioms three_le_three_pow
#print axioms single_one_ne_zero
#print axioms matrix_level_not_commutative

-- §2
#print axioms levelToCompletion_injective
#print axioms substrate_not_commutative
#print axioms ch16_step1_commutativity_fails

-- §3
#print axioms substrate_not_scalar_line

-- §4
#print axioms additive_map_zero
#print axioms additive_map_neg
#print axioms additive_map_sub
#print axioms ker_multiplicative_is_twoSided
#print axioms multiplicative_map_one
#print axioms no_nonzero_multiplicative_functional
#print axioms gelfandSpectrum_eq_empty
#print axioms no_nonzero_multiplicative_linear_functional

-- §5
#print axioms substrate_is_norm_closure_of_finite_matrix_levels

-- §6
#print axioms r217_substrate_not_commutative_capstone

end SubstrateNotCommutative
end PrincipiaTractalis
