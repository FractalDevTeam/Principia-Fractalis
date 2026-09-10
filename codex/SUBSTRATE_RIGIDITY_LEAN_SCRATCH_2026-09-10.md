# PF/SubstrateRigidity.lean — SCRATCH (not a `.lean` file yet)

**Purpose.** The proposed Lean-4 text for `PF/SubstrateRigidity.lean`. Read-back-audit-cleared through v2.1 in `codex/SUBSTRATE_RIGIDITY_AXIOM_DRAFT_2026-09-10.md`. This document holds the scratch as a code block in `.md` so Pablo can review the *exact shape* that would land — Lean-tokenised, mathlib-cited, sorry-scaffolded — before the `.lean` file itself is created.

**Not committed as `.lean`. Not imported in `PF.lean`. Won't compile until you sign off and I create the actual module.**

The `sorry`-scaffolded lemmas (C1–C4) are the four proof blocks named in `SUBSTRATE_RIGIDITY_AXIOM_DRAFT_2026-09-10.md` §3. They are stubs; each expands to a mini-arc that will be farmed (C1, C2 per FLT-lessons pattern) or authored (C3, C4).

Total: ~130 Lean lines. Zero `axiom` keywords. Uses `sorry` only inside the four C-block scaffolds — those `sorry`s are what a working session would replace with proof terms, and no version of this file is meant to be released with `sorry` present.

```lean
/-
# PF/SubstrateRigidity.lean

The substrate is uniquely determined: any C*-algebra satisfying the
`Substrate3Inf` characterisation is *-isomorphic to
`TimelessFieldCompletion`. This is Glimm's 1960 UHF classification
theorem specialised to supernatural number `3^∞`.

Program: `codex/UNIFIED_THEORY_PROOF_PROGRAM.md` §1.
Structure design + read-back audit trail:
`codex/SUBSTRATE_RIGIDITY_AXIOM_DRAFT_2026-09-10.md`.

Kernel discipline: NO `axiom`, NO `sorry` in the release version, NO
`native_decide`. The four `sorry`-scaffolded lemmas below are proof
blocks C1–C4 named in the draft §3; each is discharged before this
module is landed.

Author: Pablo Cohen + Claude Opus 4.7. 2026-09-10.
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Topology.Algebra.UniformRing
import PF.SubstrateTimelessFieldCompletion
import PF.SubstrateTraceUniqueness
import PF.AlphaFromSubstrateKTheory_r123

open scoped Matrix.Norms.L2Operator

namespace PrincipiaTractalis
namespace SubstrateRigidity

/-! ## §1 — The tracial-linear-functional predicate

Local Prop, parametric in the ambient C*-algebra. Mirrors
`PF.SubstrateTraceUniqueness.IsTracialState` (per-completion) but
generalised so the classification structure can quantify over an
arbitrary `A`. Semantic caveat: this predicate omits positivity and
star-hermitianness (as does `IsTracialState`). Sufficient for the
Elliott specialisation to `3^∞`. See draft §12.2.
-/

/-- A continuous unital ℂ-linear functional on `A` with the trace
    property. Does NOT include positivity or star-hermitianness — see
    draft §12.2 for the semantic caveat and v3 upgrade path. -/
structure IsTracialLinearFunctional
    (A : Type*) [CStarAlgebra A] (φ : A → ℂ) : Prop where
  continuous : Continuous φ
  add        : ∀ x y : A, φ (x + y) = φ x + φ y
  smul       : ∀ (c : ℂ) (x : A), φ (c • x) = c * φ x
  tracial    : ∀ x y : A, φ (x * y) = φ (y * x)
  unital     : φ 1 = 1

/-! ## §2 — The `Substrate3Inf` characterisation -/

/-- A `Substrate3Inf A` witness places `A` in the class of C*-algebras
    characterised by:
      · a directed tower of `3^k`-dimensional matrix *-subalgebras;
      · dense union of the tower;
      · a unique tracial linear functional (in the sense of §1).

    By the classification theorem `T_infinity_rigidity` below, any such
    `A` is *-isomorphic to `TimelessFieldCompletion`. -/
structure Substrate3Inf (A : Type*) [CStarAlgebra A] where
  tower         : ℕ → StarSubalgebra ℂ A
  tower_matrix  : ∀ k, Nonempty
                    (tower k ≃⋆ₐ[ℂ] Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
  tower_mono    : ∀ k, tower k ≤ tower (k+1)
  tower_dense   : Dense (((⨆ k, tower k : StarSubalgebra ℂ A) : Set A))
  trace_unique  : ∃! τ : A → ℂ, IsTracialLinearFunctional A τ

namespace Substrate3Inf
variable {A : Type*} [CStarAlgebra A] (h : Substrate3Inf A)

/-- Every inclusion in the tower is unital — free from `StarSubalgebra`
    structure since unital subalgebras are preserved by inclusion. -/
lemma connect_unital (k : ℕ) :
    (StarSubalgebra.inclusion (h.tower_mono k)) 1 = 1 := by
  rfl

/-- Every inclusion in the tower is isometric — free from mathlib for
    injective *-alg-hom between complex C*-algebras. -/
lemma connect_iso (k : ℕ) :
    Isometry (StarSubalgebra.inclusion (h.tower_mono k)) :=
  NonUnitalStarAlgHom.isometry _ (StarSubalgebra.inclusion_injective _)

end Substrate3Inf

/-! ## §3 — Proof blocks C1–C4 (SCAFFOLD)

Each block is a named-lemma cluster. Sizes below match
`SUBSTRATE_RIGIDITY_AXIOM_DRAFT_2026-09-10.md` §3.

- C1 (~5 lemmas): block-diagonal unital *-embedding
  `M_n(ℂ) →⋆ₐ[ℂ] M_{kn}(ℂ)` and its injectivity.
- C2 (~10 lemmas): Noether–Skolem for `M_n(ℂ)` — any two unital *-homs
  `M_n → M_{kn}` are conjugate by a unitary in `M_{kn}`.
- C3 (~5 lemmas): the universal property of the C*-completion of the
  pre-C* direct-limit ring, upgraded to star.
- C4 (~10 lemmas + 1 main construction): Elliott back-and-forth on two
  `3^∞`-towers producing a *-iso.

These `sorry`s are scaffolds. Not committable while present.
-/

section C1_BlockDiagonalEmbedding
variable (n k : ℕ)

/-- The canonical unital *-embedding `M_n(ℂ) →⋆ₐ[ℂ] M_{kn}(ℂ)` given by
    `x ↦ diag(x, x, ..., x)` (block-diagonal, `k` copies). -/
noncomputable def blockDiagonalStarAlgHom :
    Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
  sorry -- C1.1 — construct as `AlgHom` + `map_star'`

lemma blockDiagonalStarAlgHom_injective :
    Function.Injective (blockDiagonalStarAlgHom n k) :=
  sorry -- C1.2

lemma blockDiagonalStarAlgHom_unital :
    blockDiagonalStarAlgHom n k 1 = 1 :=
  sorry -- C1.3

end C1_BlockDiagonalEmbedding

section C2_NoetherSkolem
variable (n k : ℕ)

/-- Noether–Skolem for `M_n(ℂ)`: any two unital *-homs
    `M_n(ℂ) →⋆ₐ[ℂ] M_{kn}(ℂ)` are conjugate by a unitary in `M_{kn}(ℂ)`. -/
lemma unital_star_hom_inner_unique
    (φ ψ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] Matrix (Fin (k * n)) (Fin (k * n)) ℂ) :
    ∃ U : Matrix (Fin (k * n)) (Fin (k * n)) ℂ, IsUnit U ∧ U⋆ * U = 1 ∧
      ∀ x, φ x = U * ψ x * U⋆ :=
  sorry -- C2 main; ~10 supporting lemmas

end C2_NoetherSkolem

section C3_CompletionUniversalProperty
variable {A : Type*} [CStarAlgebra A]

/-- Any coherent family of *-homs from the tower to a C*-algebra `B`
    extends uniquely to a *-hom on `A`, given that the tower is dense
    and `A` is a C*-algebra. Specialisation of
    `UniformSpace.Completion.extensionHom` upgraded to *-preservation. -/
lemma tower_universal_star_extension
    (h : Substrate3Inf A) {B : Type*} [CStarAlgebra B]
    (fam : ∀ k, h.tower k →⋆ₐ[ℂ] B)
    (compat : ∀ k, (fam (k+1)).comp (StarSubalgebra.inclusion (h.tower_mono k))
                     = fam k) :
    ∃! F : A →⋆ₐ[ℂ] B, ∀ k, F.comp (h.tower k).subtype = fam k :=
  sorry -- C3 main; ~5 supporting lemmas

end C3_CompletionUniversalProperty

section C4_ElliottBackAndForth
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Given `Substrate3Inf` witnesses on both `A` and `B`, the two
    algebras are *-isomorphic. Elliott back-and-forth specialised to
    `3^∞` — consumes C1, C2, C3. -/
theorem substrate3Inf_iso
    (hA : Substrate3Inf A) (hB : Substrate3Inf B) :
    Nonempty (A ≃⋆ₐ[ℂ] B) :=
  sorry -- C4 main; ~10 supporting lemmas + one central intertwining

end C4_ElliottBackAndForth

/-! ## §4 — The main theorem -/

/-- **`T_infinity_rigidity`.** Any C*-algebra with a `Substrate3Inf`
    witness is *-isomorphic to `TimelessFieldCompletion`. This is
    Glimm's UHF classification specialised to supernatural number
    `3^∞`. -/
theorem T_infinity_rigidity
    (A : Type*) [CStarAlgebra A]
    (h : Substrate3Inf A) :
    Nonempty (A ≃⋆ₐ[ℂ] TimelessFieldCompletion) :=
  -- Consume C4 with hB := Substrate3Inf-on-completion (constructed
  -- from Pablo's kernel-verified ingredients per draft §7).
  substrate3Inf_iso h substrate3Inf_TimelessFieldCompletion

/-! ## §5 — Discharge on the completion side

The completion carries a natural `Substrate3Inf` witness built from
Pablo's kernel-verified ingredients (draft §7 inhabitation table). -/

/-- The canonical `Substrate3Inf` witness on `TimelessFieldCompletion`. -/
noncomputable def substrate3Inf_TimelessFieldCompletion :
    Substrate3Inf TimelessFieldCompletion where
  tower         := sorry -- from PF/SubstrateTimelessFieldNorm.lean tower
  tower_matrix  := sorry -- direct-limit definition unfolding
  tower_mono    := sorry -- directed-system inclusion
  tower_dense   := sorry -- Completion.denseRange
  trace_unique  := by
    -- Existence: use UHF_trace.
    -- Uniqueness: substrate_UHF_trace_unique
    --   (PF/SubstrateTraceUniqueness.lean:239).
    -- Bridge: prove UHF_trace satisfies IsTracialLinearFunctional
    -- (mirror of Pablo's IsTracialState — 5 fields to discharge, each
    -- kernel-visible in r113_substrate_UHF_factor_capstone).
    sorry -- ~5 field-by-field discharges + uniqueness by transport

/-! ## §6 — Kernel-audit block

Mandatory per build-tree-discipline. Verdict must be
`[propext, Classical.choice, Quot.sound]` on the final release. -/

#print axioms T_infinity_rigidity
#print axioms substrate3Inf_iso
#print axioms substrate3Inf_TimelessFieldCompletion
#print axioms Substrate3Inf.connect_iso
#print axioms Substrate3Inf.connect_unital

end SubstrateRigidity
end PrincipiaTractalis
```

---

## SCRATCH — landing checklist for when it becomes `.lean`

Before creating `PF/SubstrateRigidity.lean` and importing into `PF.lean`:

1. **Read-back v3** on the actual Lean text above (not the doc version). Confirm elaboration story matches intent. Cheap.
2. **Land C1 first** (~5 lemmas, self-contained). Discharge `blockDiagonalStarAlgHom_injective` + `_unital`. This has no dependencies and clears the smallest scaffold.
3. **Farm C1 as statement cards** if hand-writing takes >30 min per lemma per FLT-lessons pattern.
4. **Land C2** (Noether–Skolem for `M_n(ℂ)`). This is the largest single block and the one most likely to hit mathlib-primitive gaps.
5. **Land C3** (completion universal property, star-upgraded). Pablo's `SubstrateTimelessFieldCompletion.lean` already has the star lift for the specific `TimelessFieldCompletion` case; C3 factors it into a reusable lemma.
6. **Land C4** (Elliott back-and-forth). Requires C1, C2, C3. Single-author.
7. **Discharge `substrate3Inf_TimelessFieldCompletion`** — the 5 sorry-fields, using Pablo's ingredients per draft §7 inhabitation table.
8. **Land the C4-via-completion composition** to close `T_infinity_rigidity`.
9. **Run `#print axioms T_infinity_rigidity`** — must show `[propext, Classical.choice, Quot.sound]`. If it shows more, fix or quarantine.
10. **Run `#check @T_infinity_rigidity`** — the type signature must show the four explicit binders (`(A : Type*) [inst : CStarAlgebra A] (h : Substrate3Inf A)`) and no unexpected implicits.
11. **Wire into `PF.lean`** with a `-- 2026-09-XX rNNN` comment matching Pablo's existing import-line convention.
12. **Commit + push to `r331b-provenance`.** Do NOT push to `master` without §G5 sign-off.

---

## Provenance

- Structure design: `codex/SUBSTRATE_RIGIDITY_AXIOM_DRAFT_2026-09-10.md` v2.1
- Ingredient signatures: draft §6, verbatim from source grep 2026-09-10
- Mathlib API pin: draft §9, verified against mathlib4 HEAD 2026-09-09
- Read-back cycle: draft §12.1 v1 → v2 → v2.1 (rename applied)
- Semantic caveat on tracial predicate: draft §12.2 (positivity, star-hermitian upgrade paths)
- Coherence deliberately not asserted: draft §12.3 (C2 recovers it)
- No circularity: draft §12.4
- FLT-lessons statement-card farming pattern: `codex/FLT_LESSONS_FOR_PF_2026-09-08.md`

*Public HEAD `96c71da7`. NO PUSH TO MASTER. Branch `r331b-provenance`. Scratch only.*
