/-
# PF.RankPipelineUniversal_r202

★★★ 2026-08-05 — THE UNIVERSAL RANK PIPELINE: THE CAPSTONE ★★★

The end of the arc that began at r129 with a single curve.  For **any**
Weierstrass curve over ℚ with integer b-invariants, nonzero discriminant,
and no rational 2-torsion, and for **any** finite family of rational points:

  **a nonzero Gram determinant of the canonical-height pairing forces
  `n ≤ rank E(ℚ)`**  (`rank_ge_universal`).

Nothing curve-specific enters.  The constants come from the coefficients
(r175/r193), the content bounds from the resultant keystone (r174/r196),
the window from the secant + duplication estimates (r197/r198), the exact
parallelogram from the limit (r199/r200), bi-additivity from the pairing
algebra (r201), and independence from the Gram criterion (r170).

What this is, precisely: a **machine**.  Hand it a curve's coefficients, a
list of candidate points, and a certified-nonzero Gram determinant, and it
returns a kernel-checked rank lower bound.  What it is **not**: a proof of
BSD, or of anything about `L(E, s)`.  Rank lower bounds are one side of the
Mordell–Weil picture; the analytic side is untouched here.

Contents:
* `rank_ge_universal` — the capstone, any `n`;
* `gram_det_fin_two` / `rank_ge_two_universal` — the 2×2 regulator form,
  the shape actually checked in practice (`ĥP·ĥQ − ⟨P,Q⟩² ≠ 0`);
* `gram_det_fin_three` — the 3×3 expansion;
* §4 **non-vacuity**: 389a1 satisfies the whole hypothesis package
  (`h389_b₂ … h389_hΔ`, and `h389_2tor` from r155's torsion triviality),
  so the machine's hypotheses are inhabited by a real curve.  The
  determinant input for that curve is r153's interval computation; this
  file does not re-derive it.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-05.
-/
import PF.BiAdditiveUniversal_r201
import PF.TorsionTrivial389a1_r155
import PF.Universal389a1_r180

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.RankPipelineUniversal

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.DuplicationBezout
open PrincipiaTractalis.CanonicalHeightGeneric
open PrincipiaTractalis.PointParallelogramUniversal
open PrincipiaTractalis.CanheightParallelogramUniversal
open PrincipiaTractalis.BiAdditiveUniversal
open PrincipiaTractalis.GramRankGeneral
open WeierstrassCurve WeierstrassCurve.Affine

variable {W : WeierstrassCurve.Affine ℚ} {B₂ B₄ B₆ B₈ : ℤ}

/-! ## §1 — THE CAPSTONE -/

/-- **The universal rank pipeline.**  On any Weierstrass curve over ℚ with
integer b-invariants, nonzero discriminant and no rational 2-torsion, a
nonzero Gram determinant of the canonical-height pairing at `n` points
forces `n ≤ rank E(ℚ)`. -/
theorem rank_ge_universal {n : ℕ}
    (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (P : Fin n → W.Point)
    (hdet : (gram (pairingW W) P).det ≠ 0) :
    (n : Cardinal) ≤ Module.rank ℤ W.Point :=
  rank_ge_of_gram_det_ne_zero
    (biAdditive_pairingW h₂ h₄ h₆ h₈ hΔ h2tor) P hdet

/-! ## §2 — the 2×2 regulator form -/

/-- The Gram determinant at two points is the classical regulator
expression `ĥ(P)·ĥ(Q) − ⟨P,Q⟩²`. -/
theorem gram_det_fin_two
    (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (P Q : W.Point) :
    (gram (pairingW W) ![P, Q]).det
      = canheightW W P * canheightW W Q - pairingW W P Q ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [gram, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [pairing_self_universal h₂ h₄ h₆ h₈ hΔ h2tor P,
    pairing_self_universal h₂ h₄ h₆ h₈ hΔ h2tor Q,
    pairing_comm Q P]
  ring

/-- **Rank ≥ 2 from a nonzero regulator**, on any admissible curve. -/
theorem rank_ge_two_universal
    (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (P Q : W.Point)
    (hreg : canheightW W P * canheightW W Q - pairingW W P Q ^ 2 ≠ 0) :
    (2 : Cardinal) ≤ Module.rank ℤ W.Point := by
  have h := rank_ge_universal h₂ h₄ h₆ h₈ hΔ h2tor ![P, Q]
    (by rw [gram_det_fin_two h₂ h₄ h₆ h₈ hΔ h2tor]; exact hreg)
  simpa using h

/-! ## §3 — the 3×3 expansion -/

/-- The Gram determinant at three points, expanded in the pairing. -/
theorem gram_det_fin_three
    (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (P Q R : W.Point) :
    (gram (pairingW W) ![P, Q, R]).det
      = canheightW W P * (canheightW W Q * canheightW W R
            - pairingW W Q R ^ 2)
        - pairingW W P Q * (pairingW W P Q * canheightW W R
            - pairingW W Q R * pairingW W P R)
        + pairingW W P R * (pairingW W P Q * pairingW W Q R
            - canheightW W Q * pairingW W P R) := by
  rw [Matrix.det_fin_three]
  simp only [gram, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [pairing_self_universal h₂ h₄ h₆ h₈ hΔ h2tor P,
    pairing_self_universal h₂ h₄ h₆ h₈ hΔ h2tor Q,
    pairing_self_universal h₂ h₄ h₆ h₈ hΔ h2tor R,
    pairing_comm Q P, pairing_comm R P, pairing_comm R Q]
  ring

/-! ## §4 — NON-VACUITY: the hypothesis package is inhabited

389a1 satisfies every hypothesis of the pipeline.  The b-invariant
identifications come from r180, the discriminant from r174, and the
2-torsion-freeness from r155's torsion triviality.  (The *determinant*
input for this curve is r153's interval computation; it is not re-derived
here — the point of this section is that the hypotheses are satisfiable by
a real curve, i.e. the machine is not vacuous.) -/

section Witness389a1

open PrincipiaTractalis.E389a1RankOne
open PrincipiaTractalis.Universal389a1
open PrincipiaTractalis.TorsionTrivial389a1

theorem h389_b₂ : (E389a1.toAffine).b₂ = ((4 : ℤ) : ℚ) := b₂_eq.symm
theorem h389_b₄ : (E389a1.toAffine).b₄ = ((-4 : ℤ) : ℚ) := b₄_eq.symm
theorem h389_b₆ : (E389a1.toAffine).b₆ = ((1 : ℤ) : ℚ) := b₆_eq.symm
theorem h389_b₈ : (E389a1.toAffine).b₈ = ((-3 : ℤ) : ℚ) := b₈_eq.symm

theorem h389_hΔ : Disc 4 (-4) 1 (-3) ≠ 0 := by
  rw [disc_389a1]; decide

/-- 389a1 has no rational 2-torsion: `2 • R = 0` with `R ≠ 0` would make `R`
a torsion point, and r155 proved the torsion subgroup trivial. -/
theorem h389_2tor : ∀ R : (E389a1.toAffine).Point, R ≠ 0 → (2 : ℕ) • R ≠ 0 := by
  intro R hR h2
  exact hR (torsion_eq_zero (isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨2, by norm_num, h2⟩))

/-- **The pipeline instantiated on 389a1**: two points with nonzero
regulator force rank ≥ 2 — through the universal machine, with no
389a1-specific height estimate anywhere in the chain. -/
theorem rank_ge_two_389a1 (P Q : (E389a1.toAffine).Point)
    (hreg : canheightW E389a1.toAffine P * canheightW E389a1.toAffine Q
        - pairingW E389a1.toAffine P Q ^ 2 ≠ 0) :
    (2 : Cardinal) ≤ Module.rank ℤ (E389a1.toAffine).Point :=
  rank_ge_two_universal h389_b₂ h389_b₄ h389_b₆ h389_b₈ h389_hΔ h389_2tor
    P Q hreg

end Witness389a1

end PrincipiaTractalis.RankPipelineUniversal

#print axioms PrincipiaTractalis.RankPipelineUniversal.rank_ge_universal
#print axioms PrincipiaTractalis.RankPipelineUniversal.gram_det_fin_two
#print axioms PrincipiaTractalis.RankPipelineUniversal.rank_ge_two_universal
#print axioms PrincipiaTractalis.RankPipelineUniversal.gram_det_fin_three
#print axioms PrincipiaTractalis.RankPipelineUniversal.h389_2tor
#print axioms PrincipiaTractalis.RankPipelineUniversal.rank_ge_two_389a1
