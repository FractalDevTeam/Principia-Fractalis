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

/-! ## §5 — r45: Norm of zero and negation on T_∞

The remaining norm identities needed for `SeminormedAddGroup`:
  * `‖0‖ = 0`
  * `‖-x‖ = ‖x‖`

Both use mathlib's `@[to_additive]`-generated `zero_def` and
`neg_def` for `DirectLimit`, then discharge via the level-wise
`NormedRing` structure. -/

/-- **r45: Norm of zero on T_∞** — `‖(0 : TimelessFieldRing)‖ = 0`.

    Uses `DirectLimit.zero_def 0` to identify `(0 : T_∞)` with
    `⟦⟨0, (0 : Matrix (Fin 1) (Fin 1) ℂ)⟩⟧`, then reduces via the
    `Quotient.lift` definition to `‖(0 : Matrix ..)‖ = 0`. -/
theorem norm_zero_TimelessField : ‖(0 : TimelessFieldRing)‖ = 0 := by
  have h0 : (0 : TimelessFieldRing) =
      (⟦⟨0, (0 : Matrix (Fin (3^0)) (Fin (3^0)) ℂ)⟩⟧ :
        Quotient (DirectLimit.setoid
          (fun i j (h : i ≤ j) => substrateRingHomIter i j h))) :=
    DirectLimit.zero_def
      (G := fun k : ℕ => Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
      (f := fun i j (h : i ≤ j) => substrateRingHomIter i j h)
      0
  rw [h0]
  show ‖(0 : Matrix (Fin (3^0)) (Fin (3^0)) ℂ)‖ = 0
  exact norm_zero

/-- **r45: Negation preserves norm on T_∞** — `‖-x‖ = ‖x‖`.

    Reduce `x` to a level-i representative via
    `DirectLimit.exists_eq_mk`, apply `DirectLimit.neg_def` to
    rewrite `-⟦⟨i, a⟩⟧ = ⟦⟨i, -a⟩⟧`, discharge via the level-`i`
    `NormedAddGroup` identity `‖-a‖ = ‖a‖`. -/
theorem norm_neg_TimelessField (x : TimelessFieldRing) : ‖-x‖ = ‖x‖ := by
  obtain ⟨i, a, hx⟩ :=
    DirectLimit.exists_eq_mk
      (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
  subst hx
  rw [DirectLimit.neg_def
        (G := fun k : ℕ => Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
        (f := fun i j (h : i ≤ j) => substrateRingHomIter i j h)]
  show ‖-a‖ = ‖a‖
  exact norm_neg a

/-! ## §6 — r46: SeminormedRing structure on T_∞

With `‖0‖ = 0`, `‖-x‖ = ‖x‖`, `‖x + y‖ ≤ ‖x‖ + ‖y‖`, and
`‖x * y‖ ≤ ‖x‖ * ‖y‖` in hand (r43-r45), we can package everything
into a mathlib-native `SeminormedRing TimelessFieldRing` instance.

Path: `AddGroupSeminorm TimelessFieldRing` (bundling the additive
seminorm axioms) → `SeminormedAddCommGroup TimelessFieldRing` via
mathlib's `AddGroupSeminorm.toSeminormedAddCommGroup` → combine with
`norm_mul_le_TimelessField` to produce `SeminormedRing`. -/

/-- **Substrate `AddGroupSeminorm` on T_∞** bundling the three
    additive seminorm axioms proved in r43-r45:
      * `map_zero'`: `‖0‖ = 0` (r45.a)
      * `neg'`:     `‖-x‖ = ‖x‖` (r45.b)
      * `add_le'`:  `‖x + y‖ ≤ ‖x‖ + ‖y‖` (r44.a)
    Feeds mathlib's `AddGroupSeminorm.toSeminormedAddCommGroup`. -/
noncomputable def substrateAddGroupSeminorm : AddGroupSeminorm TimelessFieldRing where
  toFun x := ‖x‖
  map_zero' := norm_zero_TimelessField
  neg' := norm_neg_TimelessField
  add_le' := norm_add_le_TimelessField

/-- **`SeminormedAddCommGroup TimelessFieldRing`** — the metric-space
    packaging of T_∞'s norm arithmetic. Registered via
    `substrateAddGroupSeminorm.toSeminormedAddCommGroup`. -/
noncomputable instance instSeminormedAddCommGroupTimelessField :
    SeminormedAddCommGroup TimelessFieldRing :=
  substrateAddGroupSeminorm.toSeminormedAddCommGroup

/-- **★★★ r46: SeminormedRing structure on T_∞ ★★★**

    The substrate's Timeless Field T_∞ is now a mathlib-native
    `SeminormedRing`. Combines the r43-r45 additive seminorm axioms
    (bundled via `substrateAddGroupSeminorm.toSeminormedAddCommGroup`)
    with r44's submultiplicativity (`norm_mul_le_TimelessField`). -/
noncomputable instance instSeminormedRingTimelessField :
    SeminormedRing TimelessFieldRing :=
  { instSeminormedAddCommGroupTimelessField,
    (inferInstance : Ring TimelessFieldRing) with
    norm_mul_le := norm_mul_le_TimelessField }

/-! ## §7 — r47: Norm nondegeneracy and NormedRing structure on T_∞

The final step from `SeminormedRing` to `NormedRing`: the norm on
T_∞ is a genuine (not merely seminormed) norm — `‖x‖ = 0 → x = 0`.

Proof strategy: reduce `x` to a level-i representative `⟦⟨i, a⟩⟧`,
identify `‖⟦⟨i, a⟩⟧‖ = ‖a‖`, conclude `a = 0` from the matrix-ring
norm nondegeneracy at level i, then `⟦⟨i, 0⟩⟧ = 0` via
`DirectLimit.zero_def`. -/

/-- **r47: Norm nondegeneracy on T_∞**: `‖x‖ = 0 → x = 0`.

    Reduce `x` to a level-i representative via
    `DirectLimit.exists_eq_mk`, identify `‖⟦⟨i, a⟩⟧‖ = ‖a‖` via the
    `Quotient.lift` definition, apply the level-i matrix-ring norm
    nondegeneracy (`norm_eq_zero`) to conclude `a = 0`, then
    `⟦⟨i, 0⟩⟧ = 0` via `DirectLimit.zero_def`. -/
theorem norm_eq_zero_TimelessField (x : TimelessFieldRing) (h : ‖x‖ = 0) :
    x = 0 := by
  obtain ⟨i, a, hx⟩ :=
    DirectLimit.exists_eq_mk
      (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
  subst hx
  -- h : ‖⟦⟨i, a⟩⟧‖ = 0, which reduces to ‖a‖ = 0
  have hnorm_a : ‖a‖ = 0 := h
  have ha_zero : a = 0 := by
    rwa [← norm_eq_zero (a := a)]
  rw [ha_zero]
  -- Goal: (⟦⟨i, (0 : Matrix _ _ ℂ)⟩⟧ : Quotient _) = 0
  exact (DirectLimit.zero_def
      (G := fun k : ℕ => Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
      (f := fun i j (h : i ≤ j) => substrateRingHomIter i j h)
      i).symm

/-- **Substrate `AddGroupNorm` on T_∞** — the r46 `AddGroupSeminorm`
    upgraded with r47's nondegeneracy. Feeds mathlib's
    `AddGroupNorm.toNormedAddCommGroup`. -/
noncomputable def substrateAddGroupNorm : AddGroupNorm TimelessFieldRing where
  toFun x := ‖x‖
  map_zero' := norm_zero_TimelessField
  neg' := norm_neg_TimelessField
  add_le' := norm_add_le_TimelessField
  eq_zero_of_map_eq_zero' := norm_eq_zero_TimelessField

/-- **`NormedAddCommGroup TimelessFieldRing`** — the substrate
    Timeless Field carries a genuine normed abelian group structure.
    Registered via `substrateAddGroupNorm.toNormedAddCommGroup`. -/
noncomputable instance instNormedAddCommGroupTimelessField :
    NormedAddCommGroup TimelessFieldRing :=
  substrateAddGroupNorm.toNormedAddCommGroup

/-- **★★★ r47: NormedRing structure on T_∞ ★★★**

    The substrate's Timeless Field T_∞ is now a mathlib-native
    `NormedRing` — a genuine (not merely seminormed) normed ring.
    Combines `NormedAddCommGroup TimelessFieldRing` with r44's
    submultiplicativity. -/
noncomputable instance instNormedRingTimelessField :
    NormedRing TimelessFieldRing :=
  { instNormedAddCommGroupTimelessField,
    (inferInstance : Ring TimelessFieldRing) with
    norm_mul_le := norm_mul_le_TimelessField }

/-! ## §8 — r48: NormOneClass on T_∞

The multiplicative identity has unit norm: `‖(1 : T_∞)‖ = 1`.
Uses `DirectLimit.one_def 0` to identify `(1 : T_∞) = ⟦⟨0, 1⟩⟧`,
then the level-0 matrix norm of the 1×1 identity is 1 via
`norm_one` on the L2 operator norm. -/

/-- **r48: Norm of one on T_∞** — `‖(1 : TimelessFieldRing)‖ = 1`.

    Uses `DirectLimit.one_def 0` to identify `(1 : T_∞) = ⟦⟨0, 1⟩⟧`,
    where `1 : Matrix (Fin (3^0)) (Fin (3^0)) ℂ` is the 1×1 identity
    matrix. Its L2 operator norm equals 1 by matrix `norm_one`. -/
theorem norm_one_TimelessField : ‖(1 : TimelessFieldRing)‖ = 1 := by
  rw [DirectLimit.one_def
        (G := fun k : ℕ => Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
        (f := fun i j (h : i ≤ j) => substrateRingHomIter i j h)
        0]
  show ‖(1 : Matrix (Fin (3^0)) (Fin (3^0)) ℂ)‖ = 1
  exact norm_one

/-- **`NormOneClass TimelessFieldRing`** — T_∞'s multiplicative
    identity has unit norm. Registers the standard mathlib class
    used by `NormedAlgebra`, `NormedField`, and related structures. -/
noncomputable instance instNormOneClassTimelessField :
    NormOneClass TimelessFieldRing where
  norm_one := norm_one_TimelessField

/-! ## §9 — r49: CStarRing structure on T_∞

The C*-identity `‖star x * x‖ = ‖x‖²` on T_∞. Mathlib's modern
`CStarRing` class asks only for the one-sided inequality
`‖x‖ * ‖x‖ ≤ ‖star x * x‖`; the equality follows automatically
(see `norm_star_mul_self`).

Proof strategy: reduce `x` to a common-level representative
`⟦⟨i, a⟩⟧`, use the substrate star instance (r31: `star ⟦⟨i, a⟩⟧ =
⟦⟨i, star a⟩⟧`) together with r32's `substrate_quotient_mul_same_level`
to reduce to `‖a‖ * ‖a‖ ≤ ‖star a * a‖` at the matrix level, then
discharge via `CStarRing.norm_mul_self_le` on the level-i matrix
ring (from r33's `instCStarRingSubstrateLevel`). -/

/-- **r49: C*-inequality on T_∞** — `‖x‖ * ‖x‖ ≤ ‖star x * x‖`.

    Direct-limit lift of the matrix-ring C*-property via
    common-level representatives. -/
theorem cstar_ineq_TimelessField (x : TimelessFieldRing) :
    ‖x‖ * ‖x‖ ≤ ‖star x * x‖ := by
  obtain ⟨i, a, hx⟩ :=
    DirectLimit.exists_eq_mk
      (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
  subst hx
  -- star ⟦⟨i, a⟩⟧ = ⟦⟨i, star a⟩⟧ by definitional unfolding of the r31
  -- Star instance (Quotient.map substrate_sigma_star …); Quotient.map_mk
  -- reduces the LHS to ⟦substrate_sigma_star ⟨i, a⟩⟧ = ⟦⟨i, star a⟩⟧.
  have hstar :
      star (⟦⟨i, a⟩⟧ :
        Quotient (DirectLimit.setoid
          (fun i j (h : i ≤ j) => substrateRingHomIter i j h))) =
        ⟦⟨i, star a⟩⟧ := rfl
  rw [hstar, substrate_quotient_mul_same_level i (star a) a]
  exact CStarRing.norm_mul_self_le a

/-- **★★★ r49: CStarRing structure on T_∞ ★★★**

    The substrate's Timeless Field T_∞ carries the C*-identity
    `‖star x * x‖ = ‖x‖²` — the defining property of a C*-algebra
    ring. Combined with r30-r32 (Ring, StarRing) and r43-r48
    (NormedRing, NormOneClass), T_∞ is now a pre-C*-algebra at
    the algebraic + metric + involutive level.

    Kernel-only [propext, Classical.choice, Quot.sound]. -/
noncomputable instance instCStarRingTimelessField :
    CStarRing TimelessFieldRing where
  norm_mul_self_le := cstar_ineq_TimelessField

/-! ## §10 — Substrate T_∞ Norm existence capstone -/

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
    (‖(0 : TimelessFieldRing)‖ = 0) ∧
    (∀ x : TimelessFieldRing, ‖-x‖ = ‖x‖) ∧
    (∀ x y : TimelessFieldRing, ‖x + y‖ ≤ ‖x‖ + ‖y‖) ∧
    (∀ x y : TimelessFieldRing, ‖x * y‖ ≤ ‖x‖ * ‖y‖) :=
  ⟨⟨inferInstance⟩, substrateLevelToTimelessField_opNorm_eq,
   norm_zero_TimelessField, norm_neg_TimelessField,
   norm_add_le_TimelessField, norm_mul_le_TimelessField⟩

/-! ## §11 — r51: SMul + Module ℂ on T_∞

The substrate embeddings are ℂ-linear (r28's
`substrateEmbedMatrix_smul`); this lifts through the direct limit
to a ℂ-scalar action on T_∞, then to the full `Module ℂ` structure. -/

/-- **Iterated smul preservation**: the iterated substrate RingHom
    respects ℂ-scalar multiplication.
        `substrateRingHomIter i j h (r • A) = r • substrateRingHomIter i j h A`
    Proved by `Nat.le_induction` on the level gap using r28's
    `substrateEmbedMatrix_smul` at each successor step. -/
theorem substrateRingHomIter_smul (i : ℕ) :
    ∀ (j : ℕ) (h : i ≤ j) (r : ℂ) (A : Matrix (Fin (3^i)) (Fin (3^i)) ℂ),
    substrateRingHomIter i j h (r • A) = r • substrateRingHomIter i j h A := by
  intro j h r
  induction j, h using Nat.le_induction with
  | base =>
    intro A
    rw [substrateRingHomIter_self]
    rfl
  | succ n hn ih =>
    intro A
    rw [substrateRingHomIter_succ i n hn (hn.trans (Nat.le_succ n))]
    rw [RingHom.comp_apply, RingHom.comp_apply, ih A]
    exact SubstrateBase3Embed.substrateEmbedMatrix_smul n r
      (substrateRingHomIter i n hn A)

/-- **Sigma-level scalar action**: `⟨k, A⟩ ↦ ⟨k, r • A⟩`. -/
def substrate_sigma_smul (r : ℂ) :
    (Σ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ) →
    (Σ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :=
  fun p => ⟨p.1, r • p.2⟩

/-- **Sigma smul respects the DirectLimit setoid**. Uses the
    iterated smul preservation (`substrateRingHomIter_smul`). -/
theorem substrate_sigma_smul_respects_setoid (r : ℂ) :
    ∀ x y : Σ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ,
    (DirectLimit.setoid
      (fun i j (h : i ≤ j) => substrateRingHomIter i j h)).r x y →
    (DirectLimit.setoid
      (fun i j (h : i ≤ j) => substrateRingHomIter i j h)).r
      (substrate_sigma_smul r x) (substrate_sigma_smul r y) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, hik, hjk, hcompat⟩
  refine ⟨k, hik, hjk, ?_⟩
  show substrateRingHomIter i k hik (r • a) = substrateRingHomIter j k hjk (r • b)
  rw [substrateRingHomIter_smul i k hik r a,
      substrateRingHomIter_smul j k hjk r b, hcompat]

/-- **`SMul ℂ` on the raw substrate Quotient type**. Registered
    on the raw `Quotient` type for consistent typeclass search
    (matching the r31-r32 Star pattern). -/
noncomputable instance instSMulQuotientSubstrate :
    SMul ℂ (Quotient
      (DirectLimit.setoid
        (fun i j (h : i ≤ j) => substrateRingHomIter i j h))) where
  smul r := Quotient.map (substrate_sigma_smul r)
    (substrate_sigma_smul_respects_setoid r)

/-- **Forwarding `SMul ℂ` instance to `TimelessFieldRing`**. -/
noncomputable instance instSMulTimelessField : SMul ℂ TimelessFieldRing :=
  instSMulQuotientSubstrate

/-- **Same-level scalar action equality**: `r • ⟦⟨i, a⟩⟧ = ⟦⟨i, r • a⟩⟧`. -/
theorem substrate_quotient_smul_same_level (r : ℂ) (i : ℕ)
    (a : Matrix (Fin (3^i)) (Fin (3^i)) ℂ) :
    r • (⟦⟨i, a⟩⟧ : Quotient
      (DirectLimit.setoid
        (fun i j (h : i ≤ j) => substrateRingHomIter i j h))) =
      ⟦⟨i, r • a⟩⟧ := rfl

/-- **`MulAction ℂ TimelessFieldRing`** — `one_smul` and `mul_smul`
    lifted via common-level representatives + matrix-level axioms. -/
noncomputable instance instMulActionTimelessField :
    MulAction ℂ TimelessFieldRing where
  one_smul x := by
    obtain ⟨i, a, hx⟩ :=
      DirectLimit.exists_eq_mk
        (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
    subst hx
    show (1 : ℂ) • (⟦⟨i, a⟩⟧ : TimelessFieldRing) = ⟦⟨i, a⟩⟧
    change (⟦substrate_sigma_smul 1 ⟨i, a⟩⟧ : TimelessFieldRing) = ⟦⟨i, a⟩⟧
    show (⟦⟨i, (1 : ℂ) • a⟩⟧ : TimelessFieldRing) = ⟦⟨i, a⟩⟧
    rw [one_smul]
  mul_smul r s x := by
    obtain ⟨i, a, hx⟩ :=
      DirectLimit.exists_eq_mk
        (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
    subst hx
    show (r * s) • (⟦⟨i, a⟩⟧ : TimelessFieldRing) =
         r • (s • (⟦⟨i, a⟩⟧ : TimelessFieldRing))
    change (⟦⟨i, (r * s) • a⟩⟧ : TimelessFieldRing) = ⟦⟨i, r • s • a⟩⟧
    rw [mul_smul]

/-- **`DistribMulAction ℂ TimelessFieldRing`** — `smul_zero` and
    `smul_add` lifted via common-level representatives. -/
noncomputable instance instDistribMulActionTimelessField :
    DistribMulAction ℂ TimelessFieldRing where
  smul_zero r := by
    have h0 : (0 : TimelessFieldRing) =
        (⟦⟨0, (0 : Matrix (Fin (3^0)) (Fin (3^0)) ℂ)⟩⟧ : TimelessFieldRing) :=
      DirectLimit.zero_def
        (G := fun k : ℕ => Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
        (f := fun i j (h : i ≤ j) => substrateRingHomIter i j h)
        0
    rw [h0]
    show r • (⟦⟨0, (0 : Matrix (Fin (3^0)) (Fin (3^0)) ℂ)⟩⟧ :
              TimelessFieldRing) = _
    change (⟦⟨0, r • (0 : Matrix (Fin (3^0)) (Fin (3^0)) ℂ)⟩⟧ :
            TimelessFieldRing) = _
    rw [smul_zero]
  smul_add r x y := by
    obtain ⟨i, a, b, hx, hy⟩ :=
      DirectLimit.exists_eq_mk₂
        (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x y
    subst hx; subst hy
    show r • ((⟦⟨i, a⟩⟧ : TimelessFieldRing) + ⟦⟨i, b⟩⟧) =
         r • (⟦⟨i, a⟩⟧ : TimelessFieldRing) + r • ⟦⟨i, b⟩⟧
    rw [substrate_quotient_add_same_level i a b]
    change (⟦⟨i, r • (a + b)⟩⟧ : TimelessFieldRing) =
           ⟦⟨i, r • a⟩⟧ + ⟦⟨i, r • b⟩⟧
    rw [smul_add, substrate_quotient_add_same_level i (r • a) (r • b)]

/-- **★★★ r51: Module ℂ TimelessFieldRing ★★★**

    T_∞ is a `ℂ`-module: `add_smul` and `zero_smul` lifted via
    common-level representatives. Combined with the r30 `Ring`
    structure and the r28-lifted ℂ-linearity of embeddings, this
    delivers the full ℂ-scalar linear-algebra structure on T_∞. -/
noncomputable instance instModuleTimelessField :
    Module ℂ TimelessFieldRing where
  add_smul r s x := by
    obtain ⟨i, a, hx⟩ :=
      DirectLimit.exists_eq_mk
        (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
    subst hx
    show (r + s) • (⟦⟨i, a⟩⟧ : TimelessFieldRing) =
         r • (⟦⟨i, a⟩⟧ : TimelessFieldRing) + s • ⟦⟨i, a⟩⟧
    change (⟦⟨i, (r + s) • a⟩⟧ : TimelessFieldRing) =
           ⟦⟨i, r • a⟩⟧ + ⟦⟨i, s • a⟩⟧
    rw [add_smul, substrate_quotient_add_same_level i (r • a) (s • a)]
  zero_smul x := by
    obtain ⟨i, a, hx⟩ :=
      DirectLimit.exists_eq_mk
        (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
    subst hx
    show (0 : ℂ) • (⟦⟨i, a⟩⟧ : TimelessFieldRing) = 0
    change (⟦⟨i, (0 : ℂ) • a⟩⟧ : TimelessFieldRing) = 0
    rw [zero_smul]
    exact (DirectLimit.zero_def
        (G := fun k : ℕ => Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
        (f := fun i j (h : i ≤ j) => substrateRingHomIter i j h)
        i).symm

/-! ## §12 — r50: Substrate T_∞ pre-C*-algebra capstone

The r43-r49 sequence delivers T_∞ as a **pre-C*-algebra**: it
carries every C*-algebra structure axiom except completeness. The
metric completion `UniformSpace.Completion T_∞` is a genuine
C*-algebra — that construction is r51+ territory.

Formal restatement of what T_∞ satisfies at the end of r49:
  * `Ring TimelessFieldRing`
  * `StarRing TimelessFieldRing`
  * `Norm TimelessFieldRing` (descended via UHF direct-limit norm)
  * `NormedAddCommGroup TimelessFieldRing`
  * `NormedRing TimelessFieldRing`
  * `NormOneClass TimelessFieldRing`
  * `CStarRing TimelessFieldRing` — the C*-identity ‖x⋆ x‖ = ‖x‖²

The only `CStarAlgebra` ingredients missing (per
`Mathlib.Analysis.CStarAlgebra.Classes` line 32) are:
  * `CompleteSpace TimelessFieldRing` — false; T_∞ is only pre-C*.
    The metric completion `Completion T_∞` supplies this.
  * `NormedAlgebra ℂ TimelessFieldRing` — requires ℂ-scalar
    structure lifted from the finite levels; scheduled for r51+.
  * `StarModule ℂ TimelessFieldRing` — star commutes with scalar
    multiplication; follows from the SMul lift once ℂ-structure
    is in place. -/

/-- **★★★ SUBSTRATE T_∞ PRE-C*-ALGEBRA CAPSTONE (r49 STATE) ★★★**

    The substrate's Timeless Field T_∞ satisfies every C*-algebra
    ring axiom short of completeness. Bundles nine typeclass
    witnesses:
      (S1) `Ring TimelessFieldRing`                  (r30)
      (S2) `StarRing TimelessFieldRing`              (r32)
      (S3) `Norm TimelessFieldRing`                  (r43)
      (S4) `SeminormedAddCommGroup TimelessFieldRing` (r46)
      (S5) `NormedAddCommGroup TimelessFieldRing`    (r47)
      (S6) `SeminormedRing TimelessFieldRing`        (r46)
      (S7) `NormedRing TimelessFieldRing`            (r47)
      (S8) `NormOneClass TimelessFieldRing`          (r48)
      (S9) `CStarRing TimelessFieldRing`             (r49)

    Plus the substrate-specific isometry content:
      (I1) canonical level embedding is norm-preserving (r43)
      (I2) full C*-identity `‖star x * x‖ = ‖x‖²` (r49)

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero
    project axioms. Zero sorries.

    Remaining for full mathlib-native `CStarAlgebra TimelessFieldRing`:
      * `NormedAlgebra ℂ` scalar structure (r51)
      * `StarModule ℂ` (r51)
      * `CompleteSpace` via metric completion `Completion T_∞` (r52+) -/
theorem substrate_TimelessField_pre_CStar_capstone :
    Nonempty (Ring TimelessFieldRing) ∧
    Nonempty (StarRing TimelessFieldRing) ∧
    Nonempty (Norm TimelessFieldRing) ∧
    Nonempty (SeminormedAddCommGroup TimelessFieldRing) ∧
    Nonempty (NormedAddCommGroup TimelessFieldRing) ∧
    Nonempty (SeminormedRing TimelessFieldRing) ∧
    Nonempty (NormedRing TimelessFieldRing) ∧
    Nonempty (NormOneClass TimelessFieldRing) ∧
    Nonempty (CStarRing TimelessFieldRing) ∧
    (∀ (k : ℕ) (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ),
      ‖substrateLevelToTimelessField k A‖ = ‖A‖) ∧
    (∀ x : TimelessFieldRing, ‖star x * x‖ = ‖x‖ * ‖x‖) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩,
   ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩,
   ⟨inferInstance⟩,
   substrateLevelToTimelessField_opNorm_eq,
   fun _ => CStarRing.norm_star_mul_self⟩

end SubstrateTimelessFieldNorm
end PrincipiaTractalis
