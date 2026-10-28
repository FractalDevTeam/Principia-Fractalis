/-
# r105: Substrate matrix-level SIMPLICITY + M3.2 DIRECT-LIMIT-TIER
#       SIMPLICITY — every two-sided ideal of T_∞ is ⊥ or ⊤

★ 2026-07-22 r105 — Milestone M3.2 of the Glimm-simplicity program
(the route to unconditional completion-tier faithfulness of the
substrate UHF trace, continuing r103/r104) ★

## The framework-first content

r103 reduced completion-tier faithfulness of τ_UHF to algebraic
simplicity of the substrate UHF C*-algebra completion (Glimm 1960).
r104 built the finite-dimensional engine: the discrete Weyl family
averages every matrix to (trace/n)•1, so two-sided-absorbing sets
swallow the averaged trace scalar. r105 fires that engine twice:

**r105a — the matrix-level absorbing-set identity element**:
  * `matrix_ne_zero_has_ne_zero_entry` — a nonzero matrix has a
    nonzero entry (contrapositive of entrywise extensionality).
  * `trace_single_mul` — the trace-extraction identity
    `trace (E_{q,p} · x) = x p q` for the matrix unit
    `E_{q,p} = Matrix.single q p 1`.
  * **`absorbing_set_contains_one`** — any S ⊆ M_n(ℂ) closed under
    addition, arbitrary left/right multiplication, and ℂ-smul that
    contains some x ≠ 0 contains 1: left-multiply x by the matrix
    unit E_{q,p} aimed at a nonzero entry x p q, average with the
    r104 Weyl engine to put (x p q / n)•1 in S, and rescale by
    (n / x p q).

**r105b — matrix-level simplicity (mathlib-native)**:
  * **`matrix_twoSidedIdeal_bot_or_top`** — every two-sided ideal of
    M_n(ℂ) (n ≥ 1) is ⊥ or ⊤, via mathlib's `IsSimpleRing.matrix`
    instance (`Mathlib.RingTheory.SimpleRing.Matrix`: matrix rings
    over the simple ring ℂ are simple) + `eq_bot_or_eq_top` from
    `IsSimpleOrder (TwoSidedIdeal _)`.

**★ M3.2 MAIN — direct-limit-tier simplicity**:
  * `twoSidedIdeal_exists_mem_ne_zero_of_ne_bot` — a two-sided ideal
    ≠ ⊥ contains a nonzero element (generic, any nonunital ring).
  * `substrateIdealPullback` — the level-k pullback
    `{B : M_{3^k}(ℂ) | ⟦⟨k, B⟩⟧ ∈ I}` of a two-sided ideal I of T_∞,
    with closure lemmas `substrateIdealPullback_add_mem`,
    `substrateIdealPullback_mul_left_mem`,
    `substrateIdealPullback_mul_right_mem`,
    `substrateIdealPullback_smul_mem` (ℂ-smul closure REDUCED to
    left-mul closure via the matrix identity c•B = (c•1)·B — no
    scalar action on T_∞ is needed).
  * `substrate_quotient_one_same_level` — `⟦⟨k, 1⟩⟧ = 1` in T_∞
    (the `DirectLimit.one_def` analogue of the r100
    `substrate_quotient_zero_same_level`).
  * **★ `directLimit_twoSidedIdeal_bot_or_top`** — EVERY two-sided
    ideal of `TimelessFieldRing` is ⊥ or ⊤. Route: I ≠ ⊥ gives a
    nonzero x ∈ I; `DirectLimit.exists_eq_mk` lands x at a level k
    as ⟦⟨k, A⟩⟧ with A ≠ 0 (contrapositive of
    `substrate_quotient_zero_same_level`); the pullback of I at
    level k is two-sided absorbing and contains A, so it contains 1
    by r105a; hence ⟦⟨k, 1⟩⟧ = 1 ∈ I and I = ⊤ by
    `TwoSidedIdeal.one_mem_iff`.

This is Glimm's 1960 simplicity argument executed at the ALGEBRAIC
(direct-limit) tier of the substrate UHF tower: the increasing union
of full matrix algebras is a simple ring. The remaining gap to the
r103 hypothesis (`∀ I : TwoSidedIdeal TimelessFieldCompletion,
I = ⊥ ∨ I = ⊤`) is the COMPLETION tier — M3.3 — where a closed
proper ideal of the completion must be pushed down to the dense
subring T_∞; the honest analytic difficulty (a closed ideal of the
completion need not meet the dense subring nontrivially in any
obvious way) is recorded in the M3.3 target note at the end of this
file's capstone docstring.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-22 r105 — matrix-level and direct-limit-tier
simplicity: every two-sided ideal of every substrate matrix level
and of the substrate Timeless Field T_∞ is ⊥ or ⊤.
-/

import PF.SubstrateMatrixUnitaryAveraging
import PF.SubstrateUHFTraceIsFaithful
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateDirectLimitSimplicity

open SubstrateDirectLimit
open SubstrateUHFTraceIsFaithful
open SubstrateMatrixUnitaryAveraging

/-! ## §1 — r105a: matrix-level absorbing sets contain the identity -/

/-- **r105.a: a nonzero matrix has a nonzero entry** — the
    contrapositive of entrywise extensionality. -/
theorem matrix_ne_zero_has_ne_zero_entry {n : ℕ}
    (x : Matrix (Fin n) (Fin n) ℂ) (hx : x ≠ 0) :
    ∃ p q, x p q ≠ 0 := by
  by_contra h
  push_neg at h
  refine hx ?_
  ext p q
  rw [Matrix.zero_apply]
  exact h p q

/-- **r105.b: the trace-extraction identity** —
    `trace (E_{q,p} · x) = x p q` where `E_{q,p} = Matrix.single q p 1`
    is the matrix unit. Left multiplication by the matrix unit moves
    the (p,q) entry onto the diagonal at position (q,q); the trace
    picks it out. -/
theorem trace_single_mul {n : ℕ} (p q : Fin n)
    (x : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (Matrix.single q p (1 : ℂ) * x) = x p q := by
  have hterm : ∀ i : Fin n,
      (Matrix.single q p (1 : ℂ) * x) i i
        = if i = q then x p q else 0 := by
    intro i
    by_cases h : i = q
    · subst h
      rw [if_pos rfl, Matrix.single_mul_apply_same, one_mul]
    · rw [if_neg h, Matrix.single_mul_apply_of_ne (h := h)]
  show ∑ i : Fin n, (Matrix.single q p (1 : ℂ) * x) i i = x p q
  rw [Finset.sum_congr rfl fun i _ => hterm i,
      Finset.sum_ite_eq' Finset.univ q (fun _ => x p q),
      if_pos (Finset.mem_univ q)]

/-- **★★★ r105.c: TWO-SIDED-ABSORBING SETS WITH A NONZERO ELEMENT
    CONTAIN THE IDENTITY ★★★** (the matrix-level simplicity engine)

    If `S ⊆ M_n(ℂ)` (n ≥ 1) is closed under addition, left and right
    multiplication by ARBITRARY matrices, and ℂ-scalar multiplication,
    and contains some `x ≠ 0`, then `1 ∈ S`.

    Route: x has a nonzero entry `x p q`
    (`matrix_ne_zero_has_ne_zero_entry`); the left product
    `E_{q,p} · x ∈ S` has trace `x p q` (`trace_single_mul`); the
    r104 Weyl averaging plug-in
    (`trace_smul_one_mem_of_two_sided_absorbing`) puts
    `(x p q / n) • 1 ∈ S`; rescaling by `n / x p q ≠ 0` finishes. -/
theorem absorbing_set_contains_one {n : ℕ} [NeZero n]
    (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (h_add : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S)
    (h_left : ∀ (a : Matrix (Fin n) (Fin n) ℂ) (x : Matrix (Fin n) (Fin n) ℂ),
      x ∈ S → a * x ∈ S)
    (h_right : ∀ (a : Matrix (Fin n) (Fin n) ℂ) (x : Matrix (Fin n) (Fin n) ℂ),
      x ∈ S → x * a ∈ S)
    (h_smul : ∀ (c : ℂ) (x : Matrix (Fin n) (Fin n) ℂ), x ∈ S → c • x ∈ S)
    (x : Matrix (Fin n) (Fin n) ℂ) (hx : x ∈ S) (hx0 : x ≠ 0) :
    (1 : Matrix (Fin n) (Fin n) ℂ) ∈ S := by
  obtain ⟨p, q, hpq⟩ := matrix_ne_zero_has_ne_zero_entry x hx0
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hyS : Matrix.single q p (1 : ℂ) * x ∈ S := h_left _ _ hx
  have havg := trace_smul_one_mem_of_two_sided_absorbing
    S h_add h_left h_right h_smul _ hyS
  rw [trace_single_mul p q x] at havg
  have hfin := h_smul ((n : ℂ) / x p q) _ havg
  rw [smul_smul] at hfin
  have hcoef : ((n : ℂ) / x p q) * (x p q / (n : ℂ)) = 1 := by
    rw [div_mul_div_comm, mul_comm ((n : ℂ)) (x p q)]
    exact div_self (mul_ne_zero hpq hn)
  rw [hcoef, one_smul] at hfin
  exact hfin

/-! ## §2 — r105b: matrix-level simplicity (mathlib-native) -/

/-- **★★★ r105.d: EVERY TWO-SIDED IDEAL OF M_n(ℂ) IS ⊥ OR ⊤ ★★★**

    Matrix-level algebraic simplicity, mathlib-native: ℂ is a simple
    ring (`DivisionRing.isSimpleRing`), matrix rings over simple
    rings are simple (`IsSimpleRing.matrix`,
    `Mathlib.RingTheory.SimpleRing.Matrix`), and `IsSimpleRing`
    unfolds to `IsSimpleOrder (TwoSidedIdeal _)`, whose
    `eq_bot_or_eq_top` is exactly the claim. -/
theorem matrix_twoSidedIdeal_bot_or_top {n : ℕ} [NeZero n]
    (I : TwoSidedIdeal (Matrix (Fin n) (Fin n) ℂ)) :
    I = ⊥ ∨ I = ⊤ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  exact eq_bot_or_eq_top I

/-! ## §3 — M3.2 scaffolding: nonzero elements, the level-k pullback,
and the same-level one -/

/-- **r105.e: a two-sided ideal ≠ ⊥ contains a nonzero element**
    (generic, any nonunital nonassociative ring): if every element
    of I were 0, then I = ⊥ by `SetLike` extensionality. -/
theorem twoSidedIdeal_exists_mem_ne_zero_of_ne_bot
    {R : Type*} [NonUnitalNonAssocRing R]
    (I : TwoSidedIdeal R) (h : I ≠ ⊥) :
    ∃ x : R, x ∈ I ∧ x ≠ 0 := by
  by_contra hno
  push_neg at hno
  refine h (SetLike.ext fun z => ?_)
  constructor
  · intro hz
    exact (TwoSidedIdeal.mem_bot R).mpr (hno z hz)
  · intro hz
    rw [(TwoSidedIdeal.mem_bot R).mp hz]
    exact I.zero_mem

/-- **r105.f: the level-k pullback of a two-sided ideal of T_∞** —
    the set of level-k matrices whose quotient class lands in I. -/
def substrateIdealPullback (I : TwoSidedIdeal TimelessFieldRing) (k : ℕ) :
    Set (Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :=
  {B | (⟦⟨k, B⟩⟧ : TimelessFieldRing) ∈ I}

/-- **r105.f′: pullback membership unfolds definitionally.** -/
theorem mem_substrateIdealPullback_iff
    (I : TwoSidedIdeal TimelessFieldRing) (k : ℕ)
    (B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    B ∈ substrateIdealPullback I k ↔ (⟦⟨k, B⟩⟧ : TimelessFieldRing) ∈ I :=
  Iff.rfl

/-- **r105.g: the pullback is closed under addition** — via the r30
    same-level sum identity + `TwoSidedIdeal.add_mem`. -/
theorem substrateIdealPullback_add_mem
    (I : TwoSidedIdeal TimelessFieldRing) (k : ℕ) :
    ∀ a ∈ substrateIdealPullback I k, ∀ b ∈ substrateIdealPullback I k,
      a + b ∈ substrateIdealPullback I k := by
  intro a ha b hb
  show (⟦⟨k, a + b⟩⟧ : TimelessFieldRing) ∈ I
  rw [← substrate_quotient_add_same_level k a b]
  exact I.add_mem ha hb

/-- **r105.h: the pullback absorbs LEFT multiplication by arbitrary
    level-k matrices** — via the r30/r31 same-level product identity
    + `TwoSidedIdeal.mul_mem_left`. -/
theorem substrateIdealPullback_mul_left_mem
    (I : TwoSidedIdeal TimelessFieldRing) (k : ℕ) :
    ∀ (a B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ),
      B ∈ substrateIdealPullback I k → a * B ∈ substrateIdealPullback I k := by
  intro a B hB
  show (⟦⟨k, a * B⟩⟧ : TimelessFieldRing) ∈ I
  rw [← substrate_quotient_mul_same_level k a B]
  exact I.mul_mem_left _ _ hB

/-- **r105.i: the pullback absorbs RIGHT multiplication by arbitrary
    level-k matrices** — via the r30/r31 same-level product identity
    + `TwoSidedIdeal.mul_mem_right`. -/
theorem substrateIdealPullback_mul_right_mem
    (I : TwoSidedIdeal TimelessFieldRing) (k : ℕ) :
    ∀ (a B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ),
      B ∈ substrateIdealPullback I k → B * a ∈ substrateIdealPullback I k := by
  intro a B hB
  show (⟦⟨k, B * a⟩⟧ : TimelessFieldRing) ∈ I
  rw [← substrate_quotient_mul_same_level k B a]
  exact I.mul_mem_right _ _ hB

/-- **r105.j: the pullback is closed under ℂ-scalar multiplication** —
    REDUCED to left-multiplication absorption via the matrix identity
    `c • B = (c • 1) · B` (`Matrix.smul_mul` + `one_mul`); no scalar
    action on T_∞ is needed. -/
theorem substrateIdealPullback_smul_mem
    (I : TwoSidedIdeal TimelessFieldRing) (k : ℕ) :
    ∀ (c : ℂ) (B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ),
      B ∈ substrateIdealPullback I k → c • B ∈ substrateIdealPullback I k := by
  intro c B hB
  have h1 : (c • (1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ)) * B = c • B := by
    rw [Matrix.smul_mul, one_mul]
  rw [← h1]
  exact substrateIdealPullback_mul_left_mem I k _ B hB

/-- **r105.k: `⟦⟨k, 1⟩⟧ = (1 : TimelessFieldRing)` at every level k** —
    the `DirectLimit.one_def` analogue of the r100
    `substrate_quotient_zero_same_level`. -/
theorem substrate_quotient_one_same_level (k : ℕ) :
    (⟦⟨k, (1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ)⟩⟧ : TimelessFieldRing) = 1 :=
  (DirectLimit.one_def
    (G := fun k : ℕ => Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
    (f := fun i j (h : i ≤ j) => substrateRingHomIter i j h) k).symm

/-! ## §4 — ★ M3.2 MAIN: direct-limit-tier simplicity of T_∞ -/

/-- **★★★ r105.l = M3.2: EVERY TWO-SIDED IDEAL OF THE SUBSTRATE
    TIMELESS FIELD T_∞ IS ⊥ OR ⊤ ★★★**

    Algebraic simplicity of `TimelessFieldRing` — Glimm's 1960
    simplicity argument executed at the direct-limit tier of the
    substrate UHF tower:

    If I ≠ ⊥, take a nonzero x ∈ I (r105.e), land it at a level k as
    `x = ⟦⟨k, A⟩⟧` (`DirectLimit.exists_eq_mk`) with `A ≠ 0`
    (contrapositive of the r100 `substrate_quotient_zero_same_level`).
    The level-k pullback of I is closed under addition (r105.g),
    absorbs left/right multiplication (r105.h/r105.i), is ℂ-smul
    closed (r105.j), and contains A — so it contains 1 by the r105.c
    Weyl-averaging engine. Hence `⟦⟨k, 1⟩⟧ = 1 ∈ I` (r105.k), and
    `I = ⊤` by `TwoSidedIdeal.one_mem_iff`. -/
theorem directLimit_twoSidedIdeal_bot_or_top
    (I : TwoSidedIdeal TimelessFieldRing) : I = ⊥ ∨ I = ⊤ := by
  by_cases hbot : I = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨x, hxI, hx0⟩ := twoSidedIdeal_exists_mem_ne_zero_of_ne_bot I hbot
    obtain ⟨k, A, hxA⟩ :=
      DirectLimit.exists_eq_mk
        (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
    subst hxA
    haveI : NeZero (3 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
    have hA0 : A ≠ 0 := by
      intro h0
      rw [h0] at hxI hx0
      exact hx0 (substrate_quotient_zero_same_level k)
    have hAS : A ∈ substrateIdealPullback I k := hxI
    have h1S : (1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
        ∈ substrateIdealPullback I k :=
      absorbing_set_contains_one
        (substrateIdealPullback I k)
        (substrateIdealPullback_add_mem I k)
        (substrateIdealPullback_mul_left_mem I k)
        (substrateIdealPullback_mul_right_mem I k)
        (substrateIdealPullback_smul_mem I k)
        A hAS hA0
    have h1I : (1 : TimelessFieldRing) ∈ I := by
      rw [← substrate_quotient_one_same_level k]
      exact h1S
    exact I.one_mem_iff.mp h1I

/-! ## §5 — r105 capstone -/

/-- **★★★ r105 SUBSTRATE SIMPLICITY CAPSTONE (matrix level + M3.2
    direct-limit tier) ★★★**

    Bundles the r105 substrate content:

      (S1) **`absorbing_set_contains_one`** — for every n ≥ 1, any
           two-sided-absorbing S ⊆ M_n(ℂ) containing a nonzero
           element contains 1 (the r104 Weyl engine fired at a
           nonzero entry via the matrix unit E_{q,p} + rescaling).
      (S2) **`matrix_twoSidedIdeal_bot_or_top`** — every two-sided
           ideal of M_n(ℂ) is ⊥ or ⊤ (mathlib-native:
           `IsSimpleRing.matrix` + `eq_bot_or_eq_top`).
      (S3) **★ `directLimit_twoSidedIdeal_bot_or_top` = M3.2** —
           every two-sided ideal of the substrate Timeless Field T_∞
           (`TimelessFieldRing`, the direct limit of the substrate
           matrix tower M_{3^k}(ℂ)) is ⊥ or ⊤: ALGEBRAIC SIMPLICITY
           of the substrate UHF direct limit.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r105 discharges the direct-limit tier of
    Glimm's 1960 simplicity theorem for the substrate UHF tower. The
    r103 faithfulness hypothesis lives one tier up:
    `∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤`.

    **M3.3 target (r106).** For the completion tier, ⊥-or-⊤ for
    ARBITRARY two-sided ideals of `TimelessFieldCompletion` is the
    r103 hypothesis; the classical statement is for CLOSED ideals
    (topological simplicity), which coincides with algebraic
    simplicity for unital C*-algebras via Neumann-series
    invertibility: mathlib supplies `Units.oneSub : ‖t‖ < 1 → Rˣ`
    in complete normed rings
    (`Mathlib.Analysis.SpecificLimits.Normed`). The naive route
    "intersect a closed proper ideal J with the dense subring image
    of T_∞ and apply M3.2" BREAKS at the first step: a closed proper
    ideal of the completion need not meet the dense subring
    nontrivially — J ∩ T_∞ can be ⊥ even when J ≠ ⊥, because density
    of T_∞ in the completion says nothing about density inside J.
    The standard fix — the r106 target — is APPROXIMATION +
    LEVEL-UNITARY AVERAGING INSIDE THE COMPLETION: given a nonzero
    positive element y ∈ J, approximate it within ε by a level-k
    element ⟦⟨k, A⟩⟧, average y itself with the finitely many level-k
    Weyl unitaries (r104 images in the completion, so the average
    stays in J), and use the r104 averaging identity plus the
    1-Lipschitz trace bounds to show the average is within ε of the
    invertible scalar (τ(y))•1 with τ(y) > 0 — Neumann-series
    invertibility (`Units.oneSub`) then puts an invertible element
    in J, forcing J = ⊤. -/
theorem r105_substrate_simplicity_capstone :
    (∀ (n : ℕ) [NeZero n] (S : Set (Matrix (Fin n) (Fin n) ℂ)),
      (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) →
      (∀ (a : Matrix (Fin n) (Fin n) ℂ) (x : Matrix (Fin n) (Fin n) ℂ),
        x ∈ S → a * x ∈ S) →
      (∀ (a : Matrix (Fin n) (Fin n) ℂ) (x : Matrix (Fin n) (Fin n) ℂ),
        x ∈ S → x * a ∈ S) →
      (∀ (c : ℂ) (x : Matrix (Fin n) (Fin n) ℂ), x ∈ S → c • x ∈ S) →
      ∀ x ∈ S, x ≠ 0 → (1 : Matrix (Fin n) (Fin n) ℂ) ∈ S) ∧
    (∀ (n : ℕ) [NeZero n] (I : TwoSidedIdeal (Matrix (Fin n) (Fin n) ℂ)),
      I = ⊥ ∨ I = ⊤) ∧
    (∀ I : TwoSidedIdeal TimelessFieldRing, I = ⊥ ∨ I = ⊤) :=
  ⟨fun _ _ S h_add h_left h_right h_smul x hx hx0 =>
     absorbing_set_contains_one S h_add h_left h_right h_smul x hx hx0,
   fun _ _ I => matrix_twoSidedIdeal_bot_or_top I,
   directLimit_twoSidedIdeal_bot_or_top⟩

/-! ## §6 — Axiom audit -/

#print axioms matrix_ne_zero_has_ne_zero_entry
#print axioms trace_single_mul
#print axioms absorbing_set_contains_one
#print axioms matrix_twoSidedIdeal_bot_or_top
#print axioms twoSidedIdeal_exists_mem_ne_zero_of_ne_bot
#print axioms substrateIdealPullback
#print axioms mem_substrateIdealPullback_iff
#print axioms substrateIdealPullback_add_mem
#print axioms substrateIdealPullback_mul_left_mem
#print axioms substrateIdealPullback_mul_right_mem
#print axioms substrateIdealPullback_smul_mem
#print axioms substrate_quotient_one_same_level
#print axioms directLimit_twoSidedIdeal_bot_or_top
#print axioms r105_substrate_simplicity_capstone

end SubstrateDirectLimitSimplicity
end PrincipiaTractalis
