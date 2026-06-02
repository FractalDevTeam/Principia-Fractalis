/-
# PF.Consciousness.TimelessFieldPartialTraceMorphism

**Date**: 2026-06-02
**Status**: concrete partial-trace connecting morphism (UPGRADE from `zeroMorphism`).
**Source**: `Principia_Fractalis_master_folder_rev2/chapters/ch04_timeless_field.tex`
+ Wave 57 handoff "Timeless Field directive (Ch 4) was never addressed"
+ Pabs's 2026-06-02 directive to replace the trivial zero family with a
  real partial-trace morphism.

## Purpose

The pre-existing `PF/Consciousness/TimelessFieldConcreteMorphism.lean`
supplies `truncMorphism := zeroMorphism`, i.e. the constant-zero family,
because top-left-block truncation fails projective compatibility in the
degenerate `k = 0, k' > 0` case under `k ∣ k'`.

This module supplies a **genuine partial-trace family**
`partialTraceMorphism : ∀ k k', k ∣ k' → LevelMorphism k k'`, defined
via base-3 digit-block marginalisation. The morphism is the mathematical
partial trace over the last `k' - k` base-3 digits when `k ≤ k'`, and
is the zero morphism in the degenerate `k > k'` corner case (which is
only possible when `k' = 0` and `k > 0` under `k ∣ k'`).

## Mathematical construction

For `H_k = ℂ^(3^k)` we represent each computational basis vector by its
base-3 digit expansion: `Fin (3^k) ≃ (Fin k → Fin 3)` (mathlib
`finFunctionFinEquiv`). A matrix on `Fin (3^k)` is thus a matrix on
digit-functions `(Fin k → Fin 3)`. The partial trace from level `k'`
down to level `k` (when `k ≤ k'`) is then "marginalise the last
`k' - k` digits":
```
  (PT A) f g = Σ (t : Fin (k'-k) → Fin 3),
                 A (encode (Fin.append f t ∘ Fin.cast _))
                   (encode (Fin.append g t ∘ Fin.cast _))
```
where `encode := digitEquiv k'` and `Fin.cast` repairs
`k + (k'-k) = k'`.

This is genuinely the manuscript's ch04 Def 4.5 `Tr_{k+1,k'} ⊗ σ_m`
partial-trace coarse-graining at the digit level.

## Theorems shipped (all axiom-free)

* `partialTraceMorphism` — the genuine partial-trace family.
* `partialTraceMorphism_apply_of_le` and `_of_not_le` — case-split
  unfoldings.
* `partialTraceMorphism_zero` — partial trace of zero is zero.
* `partialTraceMorphism_self` — identity at level `k = k'`.
* `appendCast_assoc` — digit-block associativity (via
  `Fin.append_assoc`).
* `combineBlocks` — canonical equivalence
  `(Fin (k-j) → Fin 3) × (Fin (ℓ-k) → Fin 3) ≃ (Fin (ℓ-j) → Fin 3)`
  for `j ≤ k ≤ ℓ`.
* **`partialTraceMorphism_projective_compatible`** —
  `ProjectiveCompatibility partialTraceMorphism`, the discharge of
  Ch 4 Def 4.5's compatibility law for the genuine partial-trace
  family.

## Honest scope

This is a **structural-discharge** upgrade. The partial trace defined
here is the standard mathematical partial trace, expressed via base-3
digit marginalisation, with projective compatibility proved
axiom-free. It does NOT carry the operator-algebraic content of a
nuclear C*-algebra projective limit (Pimsner–Voiculescu K-theory,
spacetime-from-automorphisms, etc.) — those remain downstream work.
But at the level of the projective-system law itself, the connecting
morphism family is now genuine, not a vacuous zero map.

The upstream `truncMorphism` alias in
`TimelessFieldConcreteMorphism.lean` is re-pointed to
`partialTraceMorphism` (2026-06-02); `truncMorphism_projective_compatible`
is re-stated in terms of `partialTraceMorphism_projective_compatible`.
-/

import PF.Consciousness.TimelessField
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

namespace PrincipiaTractalis
namespace TimelessField

open scoped Classical BigOperators
open Matrix

/-! ## §1 — Digit-function equivalence of `Fin (3^k)` -/

/-- **Digit equivalence**: `Fin k → Fin 3 ≃ Fin (3^k)` via mathlib's
    `finFunctionFinEquiv` at base 3. -/
noncomputable def digitEquiv (k : ℕ) : (Fin k → Fin 3) ≃ Fin (3^k) :=
  finFunctionFinEquiv

/-! ## §2 — Partial-trace, digit-level formulation -/

/-- **Append-and-cast helper**: given digit blocks `f : Fin k → Fin 3`
    and `t : Fin (k'-k) → Fin 3` with `k ≤ k'`, produce the
    concatenated digit function `Fin k' → Fin 3`. -/
noncomputable def appendCast {k k' : ℕ} (h : k ≤ k')
    (f : Fin k → Fin 3) (t : Fin (k' - k) → Fin 3) :
    Fin k' → Fin 3 :=
  Fin.append f t ∘ Fin.cast (Nat.add_sub_of_le h).symm

/-- **Partial trace at the digit-function level**.
    Given `k ≤ k'`, marginalise over the last `k' - k` digits. -/
noncomputable def partialTraceDigits (k k' : ℕ) (h : k ≤ k')
    (A : Matrix (Fin (3^k')) (Fin (3^k')) ℂ) :
    Matrix (Fin k → Fin 3) (Fin k → Fin 3) ℂ := fun f g =>
  ∑ t : Fin (k' - k) → Fin 3,
    A (digitEquiv k' (appendCast h f t)) (digitEquiv k' (appendCast h g t))

/-- **Partial-trace connecting morphism** at level pair `(k, k')`.
    The intended canonical concrete morphism for `T_∞`. -/
noncomputable def partialTraceMorphism (k k' : ℕ) (_h : k ∣ k') :
    LevelMorphism k k' := fun A =>
  if hle : k ≤ k' then
    fun i j =>
      partialTraceDigits k k' hle A
        ((digitEquiv k).symm i) ((digitEquiv k).symm j)
  else
    0

/-! ## §3 — Basic identities -/

/-- **Unfold of `partialTraceMorphism` in the normal regime**. -/
theorem partialTraceMorphism_apply_of_le {k k' : ℕ}
    (hdvd : k ∣ k') (hle : k ≤ k')
    (A : Matrix (Fin (3^k')) (Fin (3^k')) ℂ) (i j : Fin (3^k)) :
    partialTraceMorphism k k' hdvd A i j =
      partialTraceDigits k k' hle A
        ((digitEquiv k).symm i) ((digitEquiv k).symm j) := by
  unfold partialTraceMorphism
  simp [hle]

/-- **Degenerate regime gives the zero matrix**. -/
theorem partialTraceMorphism_apply_of_not_le {k k' : ℕ}
    (hdvd : k ∣ k') (hnle : ¬ k ≤ k')
    (A : Matrix (Fin (3^k')) (Fin (3^k')) ℂ) :
    partialTraceMorphism k k' hdvd A = 0 := by
  unfold partialTraceMorphism
  simp [hnle]

/-- **Partial-trace of the zero matrix is zero**. -/
theorem partialTraceDigits_zero (k k' : ℕ) (h : k ≤ k') :
    partialTraceDigits k k' h (0 : Matrix _ _ ℂ) = 0 := by
  ext f g
  unfold partialTraceDigits
  simp

/-- **Partial-trace morphism of the zero matrix is zero**. -/
theorem partialTraceMorphism_zero (k k' : ℕ) (hdvd : k ∣ k') :
    partialTraceMorphism k k' hdvd 0 = 0 := by
  by_cases hle : k ≤ k'
  · ext i j
    rw [partialTraceMorphism_apply_of_le hdvd hle, partialTraceDigits_zero]
    simp
  · exact partialTraceMorphism_apply_of_not_le hdvd hle 0

/-! ## §4 — Identity at level `k = k'` -/

/-- Sum over `(Fin (k - k) → α)` reduces by `Subsingleton`-style
    collapse since `k - k = 0`. -/
private lemma sum_arrow_sub_self {α β : Type*} [AddCommMonoid β]
    [Fintype α] (k : ℕ) (f : (Fin (k - k) → α) → β) :
    ∑ t : Fin (k - k) → α, f t = f (fun x => (Nat.sub_self k ▸ x).elim0) := by
  obtain ⟨t₀, ht₀⟩ : ∃ t : Fin (k - k) → α, True :=
    ⟨fun x => (Nat.sub_self k ▸ x).elim0, trivial⟩
  have hsub : Subsingleton (Fin (k - k) → α) := by
    rw [Nat.sub_self]; exact ⟨fun f g => funext fun x => x.elim0⟩
  rw [Finset.sum_eq_single t₀]
  · rw [hsub.allEq t₀]
  · intros t _ ht_ne
    exact absurd (hsub.allEq t t₀) ht_ne
  · intro hni; exact absurd (Finset.mem_univ t₀) hni

/-- **Identity at level k = k'**: `partialTraceMorphism k k h = id`. -/
theorem partialTraceMorphism_self {k : ℕ} (hdvd : k ∣ k)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    partialTraceMorphism k k hdvd A = A := by
  ext i j
  rw [partialTraceMorphism_apply_of_le hdvd (le_refl k)]
  unfold partialTraceDigits
  -- Sum is over t : Fin (k - k) → Fin 3; collapse to single term.
  have hsub : Subsingleton (Fin (k - k) → Fin 3) := by
    rw [Nat.sub_self]; exact ⟨fun f g => funext fun x => x.elim0⟩
  obtain ⟨t₀, _⟩ : ∃ t : Fin (k - k) → Fin 3, True :=
    ⟨fun x => (Nat.sub_self k ▸ x).elim0, trivial⟩
  rw [Finset.sum_eq_single t₀]
  · have happend : ∀ (f : Fin k → Fin 3),
        digitEquiv k (appendCast (le_refl k) f t₀) = digitEquiv k f := by
      intro f
      congr 1
      unfold appendCast
      funext x
      simp only [Function.comp_apply]
      have hcast : Fin.cast (Nat.add_sub_of_le (le_refl k)).symm x
                 = Fin.castAdd (k - k) x := by
        apply Fin.ext; simp
      rw [hcast, Fin.append_left]
    rw [happend, happend]
    simp
  · intros t _ ht_ne
    exact absurd (hsub.allEq t t₀) ht_ne
  · intro hni; exact absurd (Finset.mem_univ t₀) hni

/-! ## §5 — Append-cast associativity (substrate for `ProjectiveCompatibility`) -/

/-- **Key combinatorial fact**: for `j ≤ k ≤ ℓ` and a digit head
    `f : Fin j → Fin 3`, blocks `s : Fin (k-j) → Fin 3` and
    `t : Fin (ℓ-k) → Fin 3`:
    ```
      appendCast hkℓ (appendCast hjk f s) t
        = appendCast hjℓ f (Fin.append s t ∘ Fin.cast hsum)
    ```
    where `hsum : k-j + (ℓ-k) = ℓ-j`. Proved via mathlib's
    `Fin.append_assoc` plus `append_cast_left`. -/
theorem appendCast_assoc {j k ℓ : ℕ} (hjk : j ≤ k) (hkℓ : k ≤ ℓ)
    (f : Fin j → Fin 3) (s : Fin (k - j) → Fin 3) (t : Fin (ℓ - k) → Fin 3) :
    appendCast hkℓ (appendCast hjk f s) t =
      appendCast (le_trans hjk hkℓ) f
        (Fin.append s t ∘ Fin.cast (by omega : ℓ - j = k - j + (ℓ - k))) := by
  unfold appendCast
  -- LHS: Fin.append (Fin.append f s ∘ Fin.cast h₁) t ∘ Fin.cast h₂
  -- where h₁ : k = j + (k - j), h₂ : ℓ = k + (ℓ - k).
  -- Use append_cast_left to absorb the inner cast:
  -- Fin.append (Fin.append f s ∘ Fin.cast h₁) t
  --   = Fin.append (Fin.append f s) t ∘ Fin.cast h₁'  where h₁' rearranges.
  rw [Fin.append_cast_left]
  -- Now LHS: Fin.append (Fin.append f s) t ∘ Fin.cast _ ∘ Fin.cast _
  --        = Fin.append (Fin.append f s) t ∘ Fin.cast _
  -- (composition of casts is a cast).
  -- Apply Fin.append_assoc to combine the two inner appends.
  rw [Fin.append_assoc]
  -- Now LHS: (Fin.append f (Fin.append s t) ∘ Fin.cast _) ∘ Fin.cast _ ∘ Fin.cast _
  --        = Fin.append f (Fin.append s t) ∘ (cast chain)
  -- RHS: Fin.append f (Fin.append s t ∘ Fin.cast _) ∘ Fin.cast _
  -- Use append_cast_right on RHS to absorb the inner cast:
  rw [Fin.append_cast_right]
  -- Now both sides are Fin.append f (Fin.append s t) ∘ (some cast chain).
  -- Composition of Fin.cast is Fin.cast, and casts between two equal
  -- naturals are unique. Reduce by funext + Fin.ext.
  funext x
  simp only [Function.comp_apply]
  -- Both sides apply Fin.append f (Fin.append s t) at some cast of x.
  -- The cast chains differ syntactically but have the same Nat value.
  congr 1

/-! ## §6 — Combined-block bijection -/

/-- **Combined-block equivalence**: for `j ≤ k ≤ ℓ`,
    `(Fin (k-j) → Fin 3) × (Fin (ℓ-k) → Fin 3) ≃ (Fin (ℓ-j) → Fin 3)`
    via `Fin.appendEquiv` composed with the cast `(k-j) + (ℓ-k) = ℓ-j`. -/
noncomputable def combineBlocks {j k ℓ : ℕ} (_hjk : j ≤ k) (_hkℓ : k ≤ ℓ) :
    (Fin (k - j) → Fin 3) × (Fin (ℓ - k) → Fin 3) ≃ (Fin (ℓ - j) → Fin 3) :=
  (Fin.appendEquiv (k - j) (ℓ - k)).trans
    (Equiv.piCongrLeft (fun _ => Fin 3)
      (finCongr (by omega : k - j + (ℓ - k) = ℓ - j)))

/-- The combineBlocks bijection produces digit blocks consistent with
    direct append: `combineBlocks (s, t)` is `Fin.append s t ∘ Fin.cast _`. -/
theorem combineBlocks_apply {j k ℓ : ℕ} (hjk : j ≤ k) (hkℓ : k ≤ ℓ)
    (s : Fin (k - j) → Fin 3) (t : Fin (ℓ - k) → Fin 3) :
    combineBlocks hjk hkℓ (s, t) =
      Fin.append s t ∘ Fin.cast (by omega : ℓ - j = k - j + (ℓ - k)) := by
  unfold combineBlocks
  funext x
  simp only [Equiv.trans_apply, Fin.appendEquiv_apply, Equiv.piCongrLeft_apply,
             Function.comp_apply]
  -- piCongrLeft (Fin.append s t) at index x = (Fin.append s t) (finCongr.symm x)
  -- We need to show this equals (Fin.append s t) (Fin.cast _ x).
  congr 1

/-! ## §7 — `ProjectiveCompatibility` discharge -/

/-- **★ MAIN THEOREM ★** : the partial-trace morphism satisfies
    `ProjectiveCompatibility` axiom-free. -/
theorem partialTraceMorphism_projective_compatible :
    ProjectiveCompatibility partialTraceMorphism := by
  intro j k ℓ hjk hkℓ hjℓ A
  by_cases hℓ : ℓ = 0
  · -- ℓ = 0 case.
    subst hℓ
    by_cases hk : k = 0
    · subst hk
      by_cases hj : j = 0
      · subst hj
        -- j = k = ℓ = 0. partialTraceMorphism 0 0 _ A = A by partialTraceMorphism_self.
        rw [partialTraceMorphism_self hkℓ]
      · push_neg at hj
        have hjpos : 0 < j := Nat.pos_of_ne_zero hj
        have hjnle : ¬ j ≤ 0 := by omega
        rw [partialTraceMorphism_apply_of_not_le hjk hjnle]
        rw [partialTraceMorphism_apply_of_not_le hjℓ hjnle]
    · push_neg at hk
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hknle : ¬ k ≤ 0 := by omega
      rw [partialTraceMorphism_apply_of_not_le hkℓ hknle]
      rw [partialTraceMorphism_zero]
      by_cases hj : j = 0
      · subst hj
        have : k = 0 := Nat.eq_zero_of_zero_dvd hjk
        omega
      · push_neg at hj
        have hjpos : 0 < j := Nat.pos_of_ne_zero hj
        have hjnle : ¬ j ≤ 0 := by omega
        exact (partialTraceMorphism_apply_of_not_le hjℓ hjnle A).symm
  · -- ℓ > 0.
    have hℓpos : 0 < ℓ := Nat.pos_of_ne_zero hℓ
    have hkle : k ≤ ℓ := Nat.le_of_dvd hℓpos hkℓ
    by_cases hk : k = 0
    · subst hk
      -- k = 0, ℓ > 0. But k ∣ ℓ means 0 ∣ ℓ, which forces ℓ = 0. Contradiction.
      have : ℓ = 0 := Nat.eq_zero_of_zero_dvd hkℓ
      exact absurd this hℓ
    · -- NORMAL case: k > 0, ℓ > 0.
      push_neg at hk
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hjle : j ≤ k := Nat.le_of_dvd hkpos hjk
      have hjℓle : j ≤ ℓ := le_trans hjle hkle
      ext i j'
      rw [partialTraceMorphism_apply_of_le hjk hjle]
      rw [partialTraceMorphism_apply_of_le hjℓ hjℓle]
      unfold partialTraceDigits
      simp only [partialTraceMorphism_apply_of_le hkℓ hkle]
      change ∑ s : Fin (k - j) → Fin 3, ∑ t : Fin (ℓ - k) → Fin 3, _ = _
      simp only [Equiv.symm_apply_apply]
      rw [← Finset.sum_product']
      -- Reindex via the equivalence combineBlocks: sum over
      -- (Fin (k-j) → Fin 3) × (Fin (ℓ-k) → Fin 3) ≃ (Fin (ℓ-j) → Fin 3).
      let E := combineBlocks hjle hkle
      rw [← E.sum_comp (fun u =>
        A (digitEquiv ℓ (appendCast hjℓle ((digitEquiv j).symm i) u))
          (digitEquiv ℓ (appendCast hjℓle ((digitEquiv j).symm j') u)))]
      apply Finset.sum_congr rfl
      rintro ⟨s, t⟩ _
      -- E (s, t) = combineBlocks _ _ (s, t) = Fin.append s t ∘ Fin.cast _ by combineBlocks_apply.
      rw [show E (s, t) = Fin.append s t ∘ Fin.cast (by omega : ℓ - j = k - j + (ℓ - k)) from
            combineBlocks_apply hjle hkle s t]
      congr 1 <;>
      · apply congrArg
        rw [appendCast_assoc hjle hkle]

/-! ## §8 — Wrap-up

This module ships the genuine partial-trace connecting morphism family
`partialTraceMorphism` (ch04 Def 4.5) and an axiom-free discharge of
`ProjectiveCompatibility` for it. The upstream
`TimelessFieldConcreteMorphism.lean` now re-points `truncMorphism` to
`partialTraceMorphism` and re-uses
`partialTraceMorphism_projective_compatible` as the source of truth
for the projective-system law.

Pieces of the proof, all axiom-free (depend only on `propext`,
`Classical.choice`, `Quot.sound`):

* `appendCast_assoc`: associativity of double-append via
  `Fin.append_assoc`, `Fin.append_cast_left`, `Fin.append_cast_right`.
* `combineBlocks`: canonical bijection
  `(Fin (k-j) → Fin 3) × (Fin (ℓ-k) → Fin 3) ≃ (Fin (ℓ-j) → Fin 3)`
  via `Fin.appendEquiv` + `finCongr`.
* Sum reindex via `Equiv.sum_comp` against `combineBlocks`.
* Case analysis on the degenerate `ℓ = 0` / `k = 0` corners
  (handled via `partialTraceMorphism_zero` and the
  `Nat.eq_zero_of_zero_dvd` lemma forcing `ℓ = 0` whenever
  `k = 0` and `k ∣ ℓ`).

The upstream `TimelessFieldConcreteMorphism.lean` continues to expose
`zeroMorphism` for historical reference, but the canonical
`truncMorphism` is now the partial-trace family. -/

#check @partialTraceMorphism
#check @partialTraceMorphism_apply_of_le
#check @partialTraceMorphism_apply_of_not_le
#check @partialTraceMorphism_zero
#check @partialTraceMorphism_self
#check @appendCast_assoc
#check @combineBlocks
#check @partialTraceMorphism_projective_compatible

end TimelessField
end PrincipiaTractalis
