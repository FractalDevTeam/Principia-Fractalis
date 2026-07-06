/-
# r43: The Substrate Timeless Field T_∞ carries a Norm

★ 2026-07-06 r43 — descending the level-wise operator norm to T_∞ ★

## Framework-first content

r42 established the substrate embedding isometry at the matrix level:
`‖substrateEmbedMatrix k A‖ = ‖A‖`. r43 iterates this over the full
directed system (`substrateRingHomIter i j h` is norm-preserving for
every `i ≤ j`) and uses that iterated isometry to descend a
well-defined `Norm` to the `DirectLimit` quotient T_∞.

The construction is the standard UHF direct-limit norm:
    `‖[⟨k, A⟩]_{T_∞}‖ := ‖A‖`
well-defined because r42-iterated forces representatives of the same
equivalence class at different levels to have the same norm.

## What this file establishes (kernel-only, zero sorries)

  * `substrateRingHomIter_opNorm_eq` — iterated r42:
    `‖substrateRingHomIter i j h A‖ = ‖A‖` for all `i ≤ j`.
  * `substrate_sigma_norm` — raw norm on the underlying `Σ` type.
  * `substrate_sigma_norm_respects_setoid` — well-definedness under
    the DirectLimit setoid.
  * `Norm TimelessFieldRing` instance descended via `Quotient.lift`.
  * `substrateLevelToTimelessField_opNorm_eq` — the canonical level
    embedding into T_∞ is an isometry.

## Framework positioning

r42 delivered the finite-level isometry; r43 promotes it to T_∞. With
`Norm TimelessFieldRing` in hand, r44 can register the `NormedRing`
axioms (triangle inequality, submultiplicativity) by lifting the
level-wise C*-algebra norm structure through the direct limit, and
r45+ closes toward `NormedAlgebra ℂ` and `CStarAlgebra` on T_∞.

Stage 2026-07-06 r43 — substrate T_∞ Norm.
-/

import PF.SubstrateBase3Norm
import PF.SubstrateDirectLimit
import Mathlib.Tactic

open scoped Matrix.Norms.L2Operator

namespace PrincipiaTractalis
namespace SubstrateTimelessFieldNorm

open SubstrateBase3Norm SubstrateDirectLimit

/-! ## §1 — Iterated substrate embedding isometry

The r42 successor-level isometry lifts to arbitrary `i ≤ j` by
induction on the level gap. -/

/-- **Iterated substrate embedding isometry** — the full directed
    system is norm-preserving:
        `‖substrateRingHomIter i j h A‖ = ‖A‖`
    for every `i ≤ j`. Proved by `Nat.le_induction` on the level gap,
    using r42 (`substrateRingHom_opNorm_eq`) at each successor step. -/
theorem substrateRingHomIter_opNorm_eq (i : ℕ) :
    ∀ (j : ℕ) (h : i ≤ j) (A : Matrix (Fin (3^i)) (Fin (3^i)) ℂ),
    ‖substrateRingHomIter i j h A‖ = ‖A‖ := by
  intro j h
  induction j, h using Nat.le_induction with
  | base =>
    intro A
    rw [substrateRingHomIter_self]
    rfl
  | succ n hn ih =>
    intro A
    rw [substrateRingHomIter_succ i n hn (hn.trans (Nat.le_succ n))]
    rw [RingHom.comp_apply]
    rw [substrateRingHom_opNorm_eq n]
    exact ih A

/-! ## §2 — Descending the norm to the DirectLimit quotient

Standard UHF construction: the sigma-level norm respects the
DirectLimit setoid, so `Quotient.lift` produces a well-defined norm
on the quotient T_∞. -/

/-- **Raw norm on the substrate Sigma type**: `⟨k, A⟩ ↦ ‖A‖`. -/
noncomputable def substrate_sigma_norm :
    (Σ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ) → ℝ :=
  fun p => ‖p.2‖

/-- **Sigma norm respects the DirectLimit setoid**: any two
    representatives of the same equivalence class have the same norm.
    Uses the iterated isometry `substrateRingHomIter_opNorm_eq`. -/
theorem substrate_sigma_norm_respects_setoid :
    ∀ x y : Σ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ,
    (DirectLimit.setoid
      (fun i j (h : i ≤ j) => substrateRingHomIter i j h)).r x y →
    substrate_sigma_norm x = substrate_sigma_norm y := by
  rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, hik, hjk, hcompat⟩
  show ‖a‖ = ‖b‖
  have ha := substrateRingHomIter_opNorm_eq i k hik a
  have hb := substrateRingHomIter_opNorm_eq j k hjk b
  calc ‖a‖ = ‖substrateRingHomIter i k hik a‖ := ha.symm
    _ = ‖substrateRingHomIter j k hjk b‖ := by rw [hcompat]
    _ = ‖b‖ := hb

/-- **Norm instance on the raw substrate Quotient type**. Descended via
    `Quotient.lift` from `substrate_sigma_norm`, using the DirectLimit
    setoid respect proved above. Registered on the raw `Quotient` type
    for consistent typeclass resolution (matches the pattern used for
    Star / InvolutiveStar / StarMul / StarRing in r31-r32). -/
noncomputable instance instNormQuotientSubstrate :
    Norm (Quotient
      (DirectLimit.setoid
        (fun i j (h : i ≤ j) => substrateRingHomIter i j h))) where
  norm := Quotient.lift substrate_sigma_norm substrate_sigma_norm_respects_setoid

/-- **Forwarding `Norm` instance to `TimelessFieldRing`**. Since
    `TimelessFieldRing = DirectLimit ... = Quotient (setoid ...)`
    definitionally, this alias makes the norm findable via typeclass
    search on `TimelessFieldRing`. -/
noncomputable instance instNormTimelessField : Norm TimelessFieldRing :=
  instNormQuotientSubstrate

/-! ## §3 — Level embedding isometry

The canonical embedding `substrateLevelToTimelessField k : A_k → T_∞`
is an L2 operator-norm isometry. -/

/-- **★★★ r43: Level embedding isometry ★★★**

    The canonical embedding of each substrate level into T_∞ is
    norm-preserving:
        `‖substrateLevelToTimelessField k A‖ = ‖A‖`

    Immediate from the `Quotient.lift` definition of the norm on T_∞
    together with `substrateLevelToTimelessField k A = ⟦⟨k, A⟩⟧`. -/
theorem substrateLevelToTimelessField_opNorm_eq (k : ℕ)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    ‖substrateLevelToTimelessField k A‖ = ‖A‖ := rfl

/-! ## §4 — r44: Norm arithmetic identities on T_∞

The two core inequalities required by `SeminormedRing`:
  * Triangle inequality: `‖x + y‖ ≤ ‖x‖ + ‖y‖`
  * Submultiplicativity: `‖x * y‖ ≤ ‖x‖ * ‖y‖`

Both lift from the finite-level `NormedRing (Matrix _ _ ℂ)` structure
via `DirectLimit.exists_eq_mk₂` to reduce to common-level
representatives, then discharge via the level-wise inequalities. -/

/-- **r44: Triangle inequality on T_∞** — `‖x + y‖ ≤ ‖x‖ + ‖y‖`.

    Standard direct-limit lift: reduce `x` and `y` to common-level
    representatives `⟦⟨i, a⟩⟧` and `⟦⟨i, b⟩⟧` via
    `DirectLimit.exists_eq_mk₂`, use r32's `substrate_quotient_add_same_level`
    to identify `x + y = ⟦⟨i, a + b⟩⟧`, then discharge via the
    level-`i` NormedRing triangle inequality. -/
theorem norm_add_le_TimelessField (x y : TimelessFieldRing) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  obtain ⟨i, a, b, hx, hy⟩ :=
    DirectLimit.exists_eq_mk₂
      (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x y
  subst hx; subst hy
  rw [substrate_quotient_add_same_level i a b]
  show ‖a + b‖ ≤ ‖a‖ + ‖b‖
  exact norm_add_le a b

/-- **r44: Submultiplicativity on T_∞** — `‖x * y‖ ≤ ‖x‖ * ‖y‖`.

    Standard direct-limit lift: reduce `x` and `y` to common-level
    representatives `⟦⟨i, a⟩⟧` and `⟦⟨i, b⟩⟧` via
    `DirectLimit.exists_eq_mk₂`, use r32's `substrate_quotient_mul_same_level`
    to identify `x * y = ⟦⟨i, a * b⟩⟧`, then discharge via the
    level-`i` NormedRing submultiplicativity. -/
theorem norm_mul_le_TimelessField (x y : TimelessFieldRing) :
    ‖x * y‖ ≤ ‖x‖ * ‖y‖ := by
  obtain ⟨i, a, b, hx, hy⟩ :=
    DirectLimit.exists_eq_mk₂
      (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x y
  subst hx; subst hy
  rw [substrate_quotient_mul_same_level i a b]
  show ‖a * b‖ ≤ ‖a‖ * ‖b‖
  exact norm_mul_le a b

/-! ## §5 — Substrate T_∞ Norm existence capstone -/

/-- **★★★ SUBSTRATE T_∞ NORM CAPSTONE ★★★**

    The substrate's Timeless Field T_∞ carries a mathlib-native
    `Norm`, well-defined by descent from the L2 operator norm on the
    finite substrate levels via the iterated r42 isometry.

    This capstone bundles:
      (N1) `Norm TimelessFieldRing` — the descended norm instance.
      (N2) `substrateLevelToTimelessField_opNorm_eq` — every canonical
           level embedding is an isometry.

    Combined with the r30-r32 algebraic structure (Ring, Star,
    StarRing), T_∞ is now a normed *-algebra at the algebraic +
    metric level — the input for the NormedRing structure (r44) and
    the eventual C*-algebra completion.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries. -/
theorem substrate_TimelessField_Norm_exists :
    Nonempty (Norm TimelessFieldRing) ∧
    (∀ (k : ℕ) (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ),
      ‖substrateLevelToTimelessField k A‖ = ‖A‖) ∧
    (∀ x y : TimelessFieldRing, ‖x + y‖ ≤ ‖x‖ + ‖y‖) ∧
    (∀ x y : TimelessFieldRing, ‖x * y‖ ≤ ‖x‖ * ‖y‖) :=
  ⟨⟨inferInstance⟩, substrateLevelToTimelessField_opNorm_eq,
   norm_add_le_TimelessField, norm_mul_le_TimelessField⟩

end SubstrateTimelessFieldNorm
end PrincipiaTractalis
