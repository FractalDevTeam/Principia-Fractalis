(*
  # Level-2 Matrix Spectrum — Coq Port (IFS-Reflection Block Decomposition)

  Coq counterpart of the Lean-side level-2 spectral content in
  PF/Analytic/MatrixEntry.lean.

  The Lean side proves these results against the actual fractal kernel
  `fractalKernelReal α a (x, y)` evaluated at the four level-2 cell
  midpoint distances {2/9, 4/9, 2/3, 8/9}. The Coq side abstracts the
  four kernel values:
    * V_2_9  := V_P(x, y) when dist(x, y) = 2/9
    * V_4_9  := V_P(x, y) when dist(x, y) = 4/9
    * V_2_3  := V_P(x, y) when dist(x, y) = 2/3
    * V_8_9  := V_P(x, y) when dist(x, y) = 8/9

  Each is bounded by a/(a-1) (the operator-norm bound; theorem on Lean
  side, hypothesis here).

  Under the IFS reflection x ↦ 1-x, the 4×4 level-2 matrix decomposes
  into two 2×2 sub-blocks B_sym, B_anti with explicit entries:

    A_sym  := a/(a-1) + V_8_9    (diagonal of 4·B_sym, (1,1))
    C_sym  := a/(a-1) + V_4_9    (diagonal of 4·B_sym, (2,2))
    B_sym  := V_2_3 + V_2_9      (off-diagonal of 4·B_sym)

    A_anti := a/(a-1) - V_8_9    (diagonal of 4·B_anti, (1,1))
    C_anti := a/(a-1) - V_4_9    (diagonal of 4·B_anti, (2,2))
    B_anti := V_2_3 - V_2_9      (off-diagonal of 4·B_anti)

  This file mirrors the Lean-side level-2 closed-form spectrum theorems
  for these blocks (trace, gap, determinant, sum-of-squares per block;
  cross-block trace identity).

  Status: zero project axioms. Four local algebraic hypotheses on
  the kernel values (bounded modulus, one per distance).
*)

Require Import Coq.Reals.Reals.
Require Import Lra.
Require Import Coq.micromega.Psatz.

Open Scope R_scope.

Section Level2Spectrum.

Variable a : R.
Hypothesis Ha : 1 < a.

(** The four kernel values at level-2 cell-midpoint distances. *)
Variables V_2_9 V_4_9 V_2_3 V_8_9 : R.

(** Uniform modulus bounds on each kernel value. *)
Hypothesis V_2_9_bnd : Rabs V_2_9 <= a / (a - 1).
Hypothesis V_4_9_bnd : Rabs V_4_9 <= a / (a - 1).
Hypothesis V_2_3_bnd : Rabs V_2_3 <= a / (a - 1).
Hypothesis V_8_9_bnd : Rabs V_8_9 <= a / (a - 1).

(* ============================================================ *)
(* The sym and antisym 2×2 sub-block entries                     *)
(* ============================================================ *)

Definition level2SymA : R := a / (a - 1) + V_8_9.
Definition level2SymC : R := a / (a - 1) + V_4_9.
Definition level2SymOffdiag : R := V_2_3 + V_2_9.

Definition level2AntiA : R := a / (a - 1) - V_8_9.
Definition level2AntiC : R := a / (a - 1) - V_4_9.
Definition level2AntiOffdiag : R := V_2_3 - V_2_9.

(* ============================================================ *)
(* The 4 level-2 eigenvalues (sym/antisym blocks)                *)
(* ============================================================ *)

(** **Level-2 sym block discriminant**: `(A_sym - C_sym)² + 4·B_sym²`. *)
Definition level2SymDisc : R :=
  (level2SymA - level2SymC)^2 + 4 * level2SymOffdiag^2.

Lemma level2SymDisc_nonneg : 0 <= level2SymDisc.
Proof.
  unfold level2SymDisc.
  apply Rplus_le_le_0_compat.
  - apply pow2_ge_0.
  - apply Rmult_le_pos; [lra | apply pow2_ge_0].
Qed.

(** **Level-2 antisym block discriminant**. *)
Definition level2AntiDisc : R :=
  (level2AntiA - level2AntiC)^2 + 4 * level2AntiOffdiag^2.

Lemma level2AntiDisc_nonneg : 0 <= level2AntiDisc.
Proof.
  unfold level2AntiDisc.
  apply Rplus_le_le_0_compat.
  - apply pow2_ge_0.
  - apply Rmult_le_pos; [lra | apply pow2_ge_0].
Qed.

(** **Level-2 sym block eigenvalues**:
    λ_sym^± := (1/8) · ((A_sym + C_sym) ± √D_sym). *)
Definition lambdaSymPlusLevel2 : R :=
  (1/8) * ((level2SymA + level2SymC) + sqrt level2SymDisc).

Definition lambdaSymMinusLevel2 : R :=
  (1/8) * ((level2SymA + level2SymC) - sqrt level2SymDisc).

(** **Level-2 antisym block eigenvalues**. *)
Definition lambdaAntiPlusLevel2 : R :=
  (1/8) * ((level2AntiA + level2AntiC) + sqrt level2AntiDisc).

Definition lambdaAntiMinusLevel2 : R :=
  (1/8) * ((level2AntiA + level2AntiC) - sqrt level2AntiDisc).

(* ============================================================ *)
(* Algebraic spectral identities per block                       *)
(* ============================================================ *)

(** **Sym block trace identity**: λ_sym⁺ + λ_sym⁻ = (1/4)·(A_sym + C_sym). *)
Theorem lambdaSymLevel2_trace :
    lambdaSymPlusLevel2 + lambdaSymMinusLevel2 =
    (1/4) * (level2SymA + level2SymC).
Proof.
  unfold lambdaSymPlusLevel2, lambdaSymMinusLevel2.
  lra.
Qed.

(** **Antisym block trace identity**: λ_anti⁺ + λ_anti⁻ = (1/4)·(A_anti + C_anti). *)
Theorem lambdaAntiLevel2_trace :
    lambdaAntiPlusLevel2 + lambdaAntiMinusLevel2 =
    (1/4) * (level2AntiA + level2AntiC).
Proof.
  unfold lambdaAntiPlusLevel2, lambdaAntiMinusLevel2.
  lra.
Qed.

(** **Sym block gap identity**: λ_sym⁺ − λ_sym⁻ = (1/4)·√D_sym. *)
Theorem lambdaSymLevel2_gap :
    lambdaSymPlusLevel2 - lambdaSymMinusLevel2 =
    (1/4) * sqrt level2SymDisc.
Proof.
  unfold lambdaSymPlusLevel2, lambdaSymMinusLevel2.
  lra.
Qed.

(** **Antisym block gap identity**. *)
Theorem lambdaAntiLevel2_gap :
    lambdaAntiPlusLevel2 - lambdaAntiMinusLevel2 =
    (1/4) * sqrt level2AntiDisc.
Proof.
  unfold lambdaAntiPlusLevel2, lambdaAntiMinusLevel2.
  lra.
Qed.

(** **Sym block determinant identity**:
    λ_sym⁺ · λ_sym⁻ = (1/16)·(A_sym·C_sym − B_sym²). *)
Theorem lambdaSymLevel2_det :
    lambdaSymPlusLevel2 * lambdaSymMinusLevel2 =
    (1/16) * (level2SymA * level2SymC - level2SymOffdiag^2).
Proof.
  unfold lambdaSymPlusLevel2, lambdaSymMinusLevel2.
  set (s := level2SymA + level2SymC).
  set (S := sqrt level2SymDisc).
  (* (1/8)(s + S)·(1/8)(s - S) = (1/64)(s² - S²) *)
  assert (Hexp : (1/8 * (s + S)) * (1/8 * (s - S)) = (1/64) * (s^2 - S^2)).
  { unfold pow. lra. }
  rewrite Hexp.
  (* S² = level2SymDisc = (A - C)² + 4·B² *)
  assert (HS2 : S^2 = level2SymDisc).
  { unfold S, pow. rewrite Rmult_1_r.
    apply sqrt_sqrt. apply level2SymDisc_nonneg. }
  rewrite HS2.
  unfold s, level2SymDisc.
  nra.
Qed.

(** **Antisym block determinant identity**. *)
Theorem lambdaAntiLevel2_det :
    lambdaAntiPlusLevel2 * lambdaAntiMinusLevel2 =
    (1/16) * (level2AntiA * level2AntiC - level2AntiOffdiag^2).
Proof.
  unfold lambdaAntiPlusLevel2, lambdaAntiMinusLevel2.
  set (s := level2AntiA + level2AntiC).
  set (S := sqrt level2AntiDisc).
  assert (Hexp : (1/8 * (s + S)) * (1/8 * (s - S)) = (1/64) * (s^2 - S^2)).
  { unfold pow. lra. }
  rewrite Hexp.
  assert (HS2 : S^2 = level2AntiDisc).
  { unfold S, pow. rewrite Rmult_1_r.
    apply sqrt_sqrt. apply level2AntiDisc_nonneg. }
  rewrite HS2.
  unfold s, level2AntiDisc.
  nra.
Qed.

(* ============================================================ *)
(* Cross-block trace identity                                    *)
(* ============================================================ *)

(** **Cross-block trace identity**:
    (λ_sym⁺ + λ_sym⁻) + (λ_anti⁺ + λ_anti⁻) = a/(a-1).

    The V_8_9 and V_4_9 cross-block terms CANCEL between sym and antisym
    block traces (because sym has +V, antisym has -V on the diagonals). *)
Theorem level2_full_trace_identity :
    (lambdaSymPlusLevel2 + lambdaSymMinusLevel2) +
    (lambdaAntiPlusLevel2 + lambdaAntiMinusLevel2) =
    a / (a - 1).
Proof.
  rewrite lambdaSymLevel2_trace, lambdaAntiLevel2_trace.
  unfold level2SymA, level2SymC, level2AntiA, level2AntiC.
  field. lra.
Qed.

(* ============================================================ *)
(* Block trace bounds (non-negativity + upper bound)             *)
(* ============================================================ *)

(** Helper: Rabs |V| ≤ B → -B ≤ V (sign extraction from modulus bound). *)
Lemma neg_bound_of_abs_le : forall V B : R,
    Rabs V <= B -> - B <= V.
Proof.
  intros V B Hb.
  destruct (Rle_or_lt 0 V) as [Hnn | Hng].
  - assert (HB_nn : 0 <= B) by (apply Rle_trans with (Rabs V); [apply Rabs_pos | exact Hb]).
    lra.
  - rewrite Rabs_left in Hb by exact Hng. lra.
Qed.

(** Helper: |V| ≤ B → V ≤ B. *)
Lemma pos_bound_of_abs_le : forall V B : R,
    Rabs V <= B -> V <= B.
Proof.
  intros V B Hb.
  apply Rle_trans with (Rabs V); [apply Rle_abs | exact Hb].
Qed.

(** **Sym block diagonal non-negativity**: A_sym, C_sym ≥ 0. *)
Theorem level2SymA_nonneg : 0 <= level2SymA.
Proof.
  unfold level2SymA.
  assert (Hlow := neg_bound_of_abs_le _ _ V_8_9_bnd).
  assert (Hd_pos : 0 < a/(a-1)) by (apply Rdiv_lt_0_compat; lra).
  lra.
Qed.

Theorem level2SymC_nonneg : 0 <= level2SymC.
Proof.
  unfold level2SymC.
  assert (Hlow := neg_bound_of_abs_le _ _ V_4_9_bnd).
  assert (Hd_pos : 0 < a/(a-1)) by (apply Rdiv_lt_0_compat; lra).
  lra.
Qed.

(** **Antisym block diagonal non-negativity**: A_anti, C_anti ≥ 0. *)
Theorem level2AntiA_nonneg : 0 <= level2AntiA.
Proof.
  unfold level2AntiA.
  assert (Hhigh := pos_bound_of_abs_le _ _ V_8_9_bnd).
  assert (Hd_pos : 0 < a/(a-1)) by (apply Rdiv_lt_0_compat; lra).
  lra.
Qed.

Theorem level2AntiC_nonneg : 0 <= level2AntiC.
Proof.
  unfold level2AntiC.
  assert (Hhigh := pos_bound_of_abs_le _ _ V_4_9_bnd).
  assert (Hd_pos : 0 < a/(a-1)) by (apply Rdiv_lt_0_compat; lra).
  lra.
Qed.

(** **Block traces non-negativity** (both block traces ≥ 0). *)
Theorem level2_block_traces_nonneg :
    (0 <= lambdaSymPlusLevel2 + lambdaSymMinusLevel2) /\
    (0 <= lambdaAntiPlusLevel2 + lambdaAntiMinusLevel2).
Proof.
  split.
  - rewrite lambdaSymLevel2_trace.
    pose proof (level2SymA_nonneg).
    pose proof (level2SymC_nonneg).
    lra.
  - rewrite lambdaAntiLevel2_trace.
    pose proof (level2AntiA_nonneg).
    pose proof (level2AntiC_nonneg).
    lra.
Qed.

(* ============================================================ *)
(* Conditional PSD via Sylvester                                 *)
(* ============================================================ *)

(** **Eigenvalue ordering** (always true, from disc ≥ 0):
    λ_sym⁻ ≤ λ_sym⁺. *)
Theorem lambdaSym_le_Level2 :
    lambdaSymMinusLevel2 <= lambdaSymPlusLevel2.
Proof.
  unfold lambdaSymPlusLevel2, lambdaSymMinusLevel2.
  pose proof (sqrt_pos level2SymDisc).
  pose proof (sqrt_positivity level2SymDisc level2SymDisc_nonneg).
  lra.
Qed.

Theorem lambdaAnti_le_Level2 :
    lambdaAntiMinusLevel2 <= lambdaAntiPlusLevel2.
Proof.
  unfold lambdaAntiPlusLevel2, lambdaAntiMinusLevel2.
  pose proof (sqrt_positivity level2AntiDisc level2AntiDisc_nonneg).
  lra.
Qed.

(** **Conditional sym PSD** (Sylvester): if B_sym² ≤ A_sym · C_sym,
    then 0 ≤ λ_sym⁻. *)
Theorem level2_sym_PSD_from_det
    (hdet : level2SymOffdiag^2 <= level2SymA * level2SymC) :
    0 <= lambdaSymMinusLevel2.
Proof.
  unfold lambdaSymMinusLevel2.
  set (s := level2SymA + level2SymC).
  set (S := sqrt level2SymDisc).
  (* Need: 0 ≤ (1/8)(s - S) iff s ≥ S. *)
  (* s ≥ 0 from level2Sym{A,C}_nonneg.
     Suffices to show S ≤ s, i.e., S² ≤ s² (since both non-neg).
     S² = (A-C)² + 4·B² ≤ (A+C)² ⟺ 4·A·C ≥ 4·B², which is hdet. *)
  assert (Hs_nn : 0 <= s).
  { unfold s. pose proof level2SymA_nonneg. pose proof level2SymC_nonneg. lra. }
  assert (HS_nn : 0 <= S).
  { unfold S. apply sqrt_pos. }
  assert (HS2 : S^2 = level2SymDisc).
  { unfold S, pow. rewrite Rmult_1_r. apply sqrt_sqrt. apply level2SymDisc_nonneg. }
  assert (Hkey : level2SymDisc <= s^2).
  { unfold level2SymDisc, s. nra. }
  assert (HSle : S <= s).
  { (* sqrt is monotone; sqrt(disc) ≤ sqrt(s²) = |s| = s. *)
    unfold S.
    apply Rle_trans with (sqrt (s^2)).
    - apply sqrt_le_1; [apply level2SymDisc_nonneg | apply pow2_ge_0 | exact Hkey ].
    - rewrite sqrt_pow2; [lra | exact Hs_nn]. }
  lra.
Qed.

(** **Conditional antisym PSD**. *)
Theorem level2_anti_PSD_from_det
    (hdet : level2AntiOffdiag^2 <= level2AntiA * level2AntiC) :
    0 <= lambdaAntiMinusLevel2.
Proof.
  unfold lambdaAntiMinusLevel2.
  set (s := level2AntiA + level2AntiC).
  set (S := sqrt level2AntiDisc).
  assert (Hs_nn : 0 <= s).
  { unfold s. pose proof level2AntiA_nonneg. pose proof level2AntiC_nonneg. lra. }
  assert (HS_nn : 0 <= S).
  { unfold S. apply sqrt_pos. }
  assert (HS2 : S^2 = level2AntiDisc).
  { unfold S, pow. rewrite Rmult_1_r. apply sqrt_sqrt. apply level2AntiDisc_nonneg. }
  assert (Hkey : level2AntiDisc <= s^2).
  { unfold level2AntiDisc, s. nra. }
  assert (HSle : S <= s).
  { (* sqrt is monotone; sqrt(disc) ≤ sqrt(s²) = |s| = s. *)
    unfold S.
    apply Rle_trans with (sqrt (s^2)).
    - apply sqrt_le_1; [apply level2AntiDisc_nonneg | apply pow2_ge_0 | exact Hkey ].
    - rewrite sqrt_pow2; [lra | exact Hs_nn]. }
  lra.
Qed.

(* ============================================================ *)
(* Frobenius / sum-of-squares identities                         *)
(* ============================================================ *)

(** **Level-2 sym block sum of squared eigenvalues**:
    λ_sym⁺² + λ_sym⁻² = (1/16) · (A_sym² + C_sym² + 2·B_sym²).

    Derived via Vieta from trace + determinant. *)
Theorem lambdaSymLevel2_sumSq :
    lambdaSymPlusLevel2^2 + lambdaSymMinusLevel2^2 =
    (1/16) * (level2SymA^2 + level2SymC^2 + 2 * level2SymOffdiag^2).
Proof.
  (* (λ⁺² + λ⁻²) = (λ⁺ + λ⁻)² − 2·(λ⁺·λ⁻) *)
  pose proof lambdaSymLevel2_trace as Htr.
  pose proof lambdaSymLevel2_det as Hdt.
  nra.
Qed.

(** **Level-2 antisym block sum of squared eigenvalues**. *)
Theorem lambdaAntiLevel2_sumSq :
    lambdaAntiPlusLevel2^2 + lambdaAntiMinusLevel2^2 =
    (1/16) * (level2AntiA^2 + level2AntiC^2 + 2 * level2AntiOffdiag^2).
Proof.
  pose proof lambdaAntiLevel2_trace as Htr.
  pose proof lambdaAntiLevel2_det as Hdt.
  nra.
Qed.

(** **Level-2 full sum-of-squared-eigenvalues** (cross-block):
    Σ all 4 squared eigenvalues = (1/16)·(sym + antisym sums). *)
Theorem level2_full_sumSq :
    (lambdaSymPlusLevel2^2 + lambdaSymMinusLevel2^2) +
    (lambdaAntiPlusLevel2^2 + lambdaAntiMinusLevel2^2) =
    (1/16) * (level2SymA^2 + level2SymC^2 + 2 * level2SymOffdiag^2 +
              (level2AntiA^2 + level2AntiC^2 + 2 * level2AntiOffdiag^2)).
Proof.
  rewrite lambdaSymLevel2_sumSq.
  rewrite lambdaAntiLevel2_sumSq.
  lra.
Qed.

(* ============================================================ *)
(* Frobenius bound + spectral radius                             *)
(* ============================================================ *)

(** **Level-2 Frobenius bound** (a > 1):
    ‖M^(2)‖_F² ≤ (a/(a-1))² (sum of squared eigenvalues bounded).

    Algebraic proof: the full sum is (1/16)·(weighted V_d² sum), and
    each V_d² ≤ d² where d = a/(a-1). Coefficients sum to 1, so total ≤ d². *)
(** Helper lemma: |V| ≤ B → V² ≤ B². *)
Lemma sq_le_of_abs_le (V B : R) (h : Rabs V <= B) : V^2 <= B^2.
Proof.
  assert (Hlow : - B <= V) by (apply neg_bound_of_abs_le; exact h).
  assert (Hhigh : V <= B) by (apply pos_bound_of_abs_le; exact h).
  assert (HB_nn : 0 <= B) by (apply Rle_trans with (Rabs V); [apply Rabs_pos | exact h]).
  nra.
Qed.

Theorem level2_sumSq_le_level0 :
    (lambdaSymPlusLevel2^2 + lambdaSymMinusLevel2^2) +
    (lambdaAntiPlusLevel2^2 + lambdaAntiMinusLevel2^2) <=
    (a / (a - 1))^2.
Proof.
  rewrite lambdaSymLevel2_sumSq, lambdaAntiLevel2_sumSq.
  unfold level2SymA, level2SymC, level2SymOffdiag,
         level2AntiA, level2AntiC, level2AntiOffdiag.
  set (d := a / (a - 1)).
  (* Each V² ≤ d² from |V| ≤ d *)
  pose proof (sq_le_of_abs_le V_2_9 d V_2_9_bnd) as HV_2_9.
  pose proof (sq_le_of_abs_le V_4_9 d V_4_9_bnd) as HV_4_9.
  pose proof (sq_le_of_abs_le V_2_3 d V_2_3_bnd) as HV_2_3.
  pose proof (sq_le_of_abs_le V_8_9 d V_8_9_bnd) as HV_8_9.
  nra.
Qed.

End Level2Spectrum.

(* ============================================================ *)
(* Cross-prover parity note                                      *)
(* ============================================================ *)

(** This Coq port mirrors the Lean-side level-2 IFS-reflection block
    decomposition (PF/Analytic/MatrixEntry.lean):

    * lambdaSym± , lambdaAnti± — 4 explicit level-2 eigenvalues
    * lambdaSym/AntiLevel2_trace — per-block traces
    * lambdaSym/AntiLevel2_gap — per-block spectral gaps in closed form
    * lambdaSym/AntiLevel2_det — per-block determinants
    * level2_full_trace_identity — cross-block trace = a/(a-1)
    * level2Sym/AntiA_nonneg, level2Sym/AntiC_nonneg — diagonal non-negativity
    * level2_block_traces_nonneg — block traces ≥ 0

    The Coq side takes the 4 kernel values at the level-2 distances
    {2/9, 4/9, 2/3, 8/9} as parameters with modulus bounds; on the
    Lean side, all 4 are theorems for the concrete fractal kernel.

    Zero project axioms in this file. *)
