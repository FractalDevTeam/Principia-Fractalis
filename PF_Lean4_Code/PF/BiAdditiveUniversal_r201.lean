/-
# PF.BiAdditiveUniversal_r201

★★★ 2026-08-05 — THE HEIGHT PAIRING IS BI-ADDITIVE, UNIVERSALLY ★★★

r167 proved bi-additivity of the canonical-height pairing for 5077a1;
r151 proved the multiple law for 389a1.  This stone ports both to EVERY
Weierstrass curve over ℚ with integer b-invariants, nonzero discriminant,
and no rational 2-torsion — the standing hypotheses of r200.

The chain, with every per-curve input replaced by its universal
counterpart:

1. `canheight_neg` — `ĥ(−R) = ĥ(R)`, because negation fixes the
   x-coordinate, so every term of the defining sequence agrees
   (hypothesis-free: pure sequence equality).
2. `canheight_zero` — `ĥ(0) = 0`, from the doubling law at `0`.
3. `par` — the ALL-CASES parallelogram law.  The distinct-x case is
   r200's `canheight_parallelogram_universal`; the degenerate cases
   (`P = 0`, `Q = 0`, `Q = −P`, `P = Q`) close via `canheight_zero`,
   `canheight_neg`, and `ĥ(2P) = 4ĥ(P)` (r171).  Equal x-coordinates
   force one of the degenerate cases via r199's
   `eq_or_eq_neg_of_x_eq`, so nothing is lost.  Where r167 leaned on
   5077a1's torsion-freeness, `h2tor` now carries the load.
4. `mul` — `ĥ(k•R) = k²·ĥ(R)` for all `k : ℤ`, by r151's two-step
   induction on the (now unconditional) parallelogram recurrence.
5. `four_pairing`, `pairing_add_left`, `pairing_comm`,
   `pairing_add_right` — r167's Jordan–von Neumann derivation,
   verbatim over `par` and `canheight_neg`.
6. `biAdditive_pairingW` — the capstone: r170's `BiAdditive`
   structure for `pairingW W`, ready for
   `rank_ge_of_gram_det_ne_zero` on ANY admissible curve.

HONEST SCOPE.  Bi-additivity of the pairing and the unconditional
laws, on the point group of any rational Weierstrass curve with
integer b-invariants, nonzero discriminant, and no rational
2-torsion.  No Gram determinant is computed here; no rank claim.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-05.
-/
import PF.CanheightParallelogramUniversal_r200
import PF.GramRankGeneral_r170

set_option maxHeartbeats 800000

namespace PrincipiaTractalis.BiAdditiveUniversal

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.DuplicationBezout
open PrincipiaTractalis.DuplicationSize
open PrincipiaTractalis.DuplicationHeight
open PrincipiaTractalis.DuplicationLogWindow
open PrincipiaTractalis.CanonicalHeightGeneric
open PrincipiaTractalis.PointParallelogramUniversal
open PrincipiaTractalis.CanheightParallelogramUniversal
open PrincipiaTractalis.GramRankGeneral
open WeierstrassCurve WeierstrassCurve.Affine
open Filter Topology

variable {W : WeierstrassCurve.Affine ℚ} {B₂ B₄ B₆ B₈ : ℤ}

/-! ## §1 — negation invariance and `ĥ(0) = 0` -/

/-- Negation fixes the x-coordinate, on any curve. -/
theorem X_neg (R : W.Point) : X (-R) = X R := by
  rcases R with _ | @⟨x, y, h⟩
  · rfl
  · rw [Point.neg_some]
    rfl

/-- Hence the log-naive height on points is negation-invariant. -/
theorem lognh_neg (R : W.Point) : lognh (X (-R)) = lognh (X R) := by
  rw [X_neg]

/-- **`ĥ(−R) = ĥ(R)`** — every term of the defining sequence agrees.
Hypothesis-free: this is an equality of limits of identical sequences. -/
theorem canheight_neg (R : W.Point) :
    canheightW W (-R) = canheightW W R := by
  have hseq_eq : hseq (fun R : W.Point => lognh (X R)) (-R)
      = hseq (fun R : W.Point => lognh (X R)) R := by
    funext n
    simp only [hseq, smul_neg, X_neg]
  unfold canheightW canheight
  rw [hseq_eq]

/-- The doubling law `ĥ(R+R) = 4ĥ(R)`, specialised to `canheightW`
(r171's generic law through r200's universal window). -/
theorem canheightW_dbl (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (R : W.Point) :
    canheightW W (R + R) = 4 * canheightW W R := by
  have hw := heightWindow_universal h₂ h₄ h₆ h₈ hΔ h2tor
  unfold canheightW
  exact canheight_dbl hw R

/-- **`ĥ(0) = 0`** — from the doubling law at the identity. -/
theorem canheight_zero (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0) :
    canheightW W (0 : W.Point) = 0 := by
  have h := canheightW_dbl h₂ h₄ h₆ h₈ hΔ h2tor (0 : W.Point)
  rw [add_zero] at h
  linarith

/-! ## §2 — the ALL-CASES parallelogram law -/

/-- **★ THE PARALLELOGRAM LAW FOR EVERY PAIR ★**, degenerate cases
included, on any admissible curve. -/
theorem par (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (P Q : W.Point) :
    canheightW W (P + Q) + canheightW W (P - Q)
      = 2 * canheightW W P + 2 * canheightW W Q := by
  by_cases hP0 : P = 0
  · subst hP0
    rw [zero_add, zero_sub, canheight_neg,
      canheight_zero h₂ h₄ h₆ h₈ hΔ h2tor]
    ring
  by_cases hQ0 : Q = 0
  · subst hQ0
    rw [add_zero, sub_zero, canheight_zero h₂ h₄ h₆ h₈ hΔ h2tor]
    ring
  by_cases hs : P + Q = 0
  · have hQP : Q = -P := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hs
    subst hQP
    rw [hs, canheight_zero h₂ h₄ h₆ h₈ hΔ h2tor, sub_neg_eq_add,
      canheightW_dbl h₂ h₄ h₆ h₈ hΔ h2tor, canheight_neg]
    ring
  by_cases hd : P - Q = 0
  · have hPQ : P = Q := sub_eq_zero.mp hd
    subst hPQ
    rw [hd, canheight_zero h₂ h₄ h₆ h₈ hΔ h2tor,
      canheightW_dbl h₂ h₄ h₆ h₈ hΔ h2tor]
    ring
  · -- both affine; equal x-coordinates would force a degenerate case
    obtain ⟨xp, yp, hp, rfl⟩ := exists_affine hP0
    obtain ⟨xq, yq, hq, rfl⟩ := exists_affine hQ0
    have hne : xp ≠ xq := by
      intro hx
      subst hx
      rcases eq_or_eq_neg_of_x_eq hp hq with h | h
      · exact hd (by rw [h, sub_self])
      · exact hs (by rw [h, neg_add_cancel])
    exact canheight_parallelogram_universal h₂ h₄ h₆ h₈ hΔ h2tor hp hq hne

/-! ## §3 — the multiple law `ĥ(k•R) = k²·ĥ(R)` -/

theorem smul_succ (k : ℤ) (R : W.Point) :
    (k + 1) • R = k • R + R := by
  rw [add_smul, one_smul]

theorem smul_pred (k : ℤ) (R : W.Point) :
    (k - 1) • R = k • R - R := by
  rw [sub_smul, one_smul]

/-- **The recurrence.**  The unconditional parallelogram law at
`((n+2)R, R)` — whose sum is `(n+3)R` and difference `(n+1)R` — gives
the three-term relation, with no side conditions. -/
theorem canheight_rec (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (R : W.Point) (n : ℕ) :
    canheightW W ((((n : ℤ) + 3)) • R)
      = 2 * canheightW W ((((n : ℤ) + 2)) • R) + 2 * canheightW W R
        - canheightW W ((((n : ℤ) + 1)) • R) := by
  have hsum : (((n : ℤ) + 2)) • R + R = (((n : ℤ) + 3)) • R := by
    have h := smul_succ ((n : ℤ) + 2) R
    rw [show ((n : ℤ) + 2 + 1) = ((n : ℤ) + 3) from by ring] at h
    exact h.symm
  have hdif : (((n : ℤ) + 2)) • R - R = (((n : ℤ) + 1)) • R := by
    have h := smul_pred ((n : ℤ) + 2) R
    rw [show ((n : ℤ) + 2 - 1) = ((n : ℤ) + 1) from by ring] at h
    exact h.symm
  have hpar := par h₂ h₄ h₆ h₈ hΔ h2tor ((((n : ℤ) + 2)) • R) R
  rw [hsum, hdif] at hpar
  linarith [hpar]

/-- The two-step induction, carrying consecutive pairs. -/
theorem canheight_nat_pair (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (R : W.Point) (n : ℕ) :
    canheightW W ((((n : ℤ) + 1)) • R)
        = ((n : ℝ) + 1) ^ 2 * canheightW W R ∧
    canheightW W ((((n : ℤ) + 2)) • R)
        = ((n : ℝ) + 2) ^ 2 * canheightW W R := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · have e : (((0 : ℕ) : ℤ) + 1) = 1 := by norm_num
        rw [e, one_smul]
        norm_num
      · have e : (((0 : ℕ) : ℤ) + 2) = 2 := by norm_num
        have h2R : (2 : ℤ) • R = R + R := by
          rw [show (2 : ℤ) = 1 + 1 from rfl, add_smul, one_smul]
        rw [e, h2R, canheightW_dbl h₂ h₄ h₆ h₈ hΔ h2tor]
        norm_num
  | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨?_, ?_⟩
      · -- the (k+1)+1 = k+2 case is ih2, modulo cast normalisation
        have e : (((k : ℕ) + 1 : ℕ) : ℤ) + 1 = ((k : ℤ) + 2) := by
          push_cast; ring
        rw [e, ih2]
        push_cast
        ring
      · -- the new value, from the recurrence
        have hrec := canheight_rec h₂ h₄ h₆ h₈ hΔ h2tor R k
        have e : (((k : ℕ) + 1 : ℕ) : ℤ) + 2 = ((k : ℤ) + 3) := by
          push_cast; ring
        rw [e, hrec, ih1, ih2]
        push_cast
        ring

/-- The multiple law for natural multiples. -/
theorem canheight_nsmul (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (R : W.Point) (k : ℕ) :
    canheightW W (((k : ℤ)) • R) = (k : ℝ) ^ 2 * canheightW W R := by
  cases k with
  | zero =>
      show canheightW W ((0 : ℤ) • R)
        = ((0 : ℕ) : ℝ) ^ 2 * canheightW W R
      rw [zero_smul, canheight_zero h₂ h₄ h₆ h₈ hΔ h2tor]
      norm_num
  | succ m =>
      have h := (canheight_nat_pair h₂ h₄ h₆ h₈ hΔ h2tor R m).1
      rw [show (((m + 1 : ℕ)) : ℤ) = ((m : ℤ) + 1) from by push_cast; ring, h]
      push_cast
      ring

/-- **★ THE MULTIPLE LAW FOR EVERY `k : ℤ` AND EVERY POINT ★**
`ĥ(k•R) = k²·ĥ(R)`, on any admissible curve. -/
theorem mul (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (R : W.Point) (k : ℤ) :
    canheightW W (k • R) = (k : ℝ) ^ 2 * canheightW W R := by
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk with m
    exact canheight_nsmul h₂ h₄ h₆ h₈ hΔ h2tor R m
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [hm, neg_smul, canheight_neg,
      canheight_nsmul h₂ h₄ h₆ h₈ hΔ h2tor R m]
    push_cast
    ring

/-! ## §4 — the pairing, and `4B = q(x+y) − q(x−y)` -/

theorem four_pairing (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (P Q : W.Point) :
    4 * pairingW W P Q = canheightW W (P + Q) - canheightW W (P - Q) := by
  have hp := par h₂ h₄ h₆ h₈ hΔ h2tor P Q
  simp only [pairingW]
  linarith [hp]

/-! ## §5 — BI-ADDITIVITY -/

/-- **★ THE PAIRING IS ADDITIVE IN ITS FIRST SLOT ★**
`⟨P+Q, R⟩ = ⟨P, R⟩ + ⟨Q, R⟩`, by Jordan–von Neumann, universally. -/
theorem pairing_add_left (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (P Q R : W.Point) :
    pairingW W (P + Q) R = pairingW W P R + pairingW W Q R := by
  -- the four instances of the unconditional law
  have A := par h₂ h₄ h₆ h₈ hΔ h2tor (P + R) Q
  have B := par h₂ h₄ h₆ h₈ hΔ h2tor (P - R) Q
  have C := par h₂ h₄ h₆ h₈ hΔ h2tor (Q + R) P
  have D := par h₂ h₄ h₆ h₈ hΔ h2tor (Q - R) P
  -- the mixed differences pair up under q(-u) = q(u)
  have e1 : (P + R) - Q = -((Q - R) - P) := by abel
  have e2 : (P - R) - Q = -((Q + R) - P) := by abel
  have h1 : canheightW W ((P + R) - Q) = canheightW W ((Q - R) - P) := by
    rw [e1, canheight_neg]
  have h2 : canheightW W ((P - R) - Q) = canheightW W ((Q + R) - P) := by
    rw [e2, canheight_neg]
  -- align the sum arguments
  have s1 : (P + R) + Q = (P + Q) + R := by abel
  have s2 : (P - R) + Q = (P + Q) - R := by abel
  have s3 : (Q + R) + P = (P + Q) + R := by abel
  have s4 : (Q - R) + P = (P + Q) - R := by abel
  rw [s1] at A
  rw [s2] at B
  rw [s3] at C
  rw [s4] at D
  -- assemble
  have f1 := four_pairing h₂ h₄ h₆ h₈ hΔ h2tor (P + Q) R
  have f2 := four_pairing h₂ h₄ h₆ h₈ hΔ h2tor P R
  have f3 := four_pairing h₂ h₄ h₆ h₈ hΔ h2tor Q R
  have key : canheightW W ((P + Q) + R) - canheightW W ((P + Q) - R)
      = (canheightW W (P + R) - canheightW W (P - R))
        + (canheightW W (Q + R) - canheightW W (Q - R)) := by
    linarith [A, B, C, D, h1, h2]
  linarith [f1, f2, f3, key]

/-- Symmetry of the pairing — hypothesis-free. -/
theorem pairing_comm (P Q : W.Point) :
    pairingW W P Q = pairingW W Q P := by
  simp only [pairingW, add_comm P Q]
  ring

/-- Additivity in the second slot, by symmetry. -/
theorem pairing_add_right (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (P Q R : W.Point) :
    pairingW W P (Q + R) = pairingW W P Q + pairingW W P R := by
  rw [pairing_comm, pairing_add_left h₂ h₄ h₆ h₈ hΔ h2tor,
    pairing_comm Q P, pairing_comm R P]

/-! ## §6 — THE CAPSTONE: the r170 `BiAdditive` structure -/

/-- **★★★ r201 — THE UNIVERSAL BI-ADDITIVE HEIGHT PAIRING ★★★**

On ANY Weierstrass curve over ℚ with integer b-invariants, nonzero
discriminant, and no rational 2-torsion, the canonical-height pairing
`pairingW W` is a symmetric bi-additive form on the point group —
exactly what r170's `rank_ge_of_gram_det_ne_zero` consumes. -/
theorem biAdditive_pairingW (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0) :
    BiAdditive (pairingW W) :=
  { add_left := pairing_add_left h₂ h₄ h₆ h₈ hΔ h2tor
    symm := pairing_comm }

end PrincipiaTractalis.BiAdditiveUniversal

#print axioms PrincipiaTractalis.BiAdditiveUniversal.X_neg
#print axioms PrincipiaTractalis.BiAdditiveUniversal.canheight_neg
#print axioms PrincipiaTractalis.BiAdditiveUniversal.canheight_zero
#print axioms PrincipiaTractalis.BiAdditiveUniversal.par
#print axioms PrincipiaTractalis.BiAdditiveUniversal.mul
#print axioms PrincipiaTractalis.BiAdditiveUniversal.four_pairing
#print axioms PrincipiaTractalis.BiAdditiveUniversal.pairing_add_left
#print axioms PrincipiaTractalis.BiAdditiveUniversal.pairing_add_right
#print axioms PrincipiaTractalis.BiAdditiveUniversal.biAdditive_pairingW
