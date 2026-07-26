(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 15 proof obligations, of which 0 are `True` closed by
  `exact I` (no content) and 15 are closed with real tactics.
  Those 15 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  This file also declares 4 `Axiom`/`Parameter`/`Hypothesis` stand-in(s).
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # Matrix-Entry Spectrum — Coq Port (Algebraic Layer)

  Coq counterpart of the Lean-side `PF/Analytic/MatrixEntry.lean`
  spectrum theorems (level 0 + level 1 closed-form eigenvalues).

  The Lean side proves these results against the actual fractal kernel
  `fractalKernelReal α a (x, y) := Σ a^(-n) · cos(π · α^n · |x - y|)`,
  which requires Coq's measure-theory / infinite-series infrastructure
  for a full mirror (Coquelicot or equivalent).

  This Coq port abstracts over the kernel value: we take an OPAQUE
  `V_P : R -> R -> R` (the fractal kernel) with two hypotheses:
    1. Symmetric: `V_P x y = V_P y x` (matches `fractalKernelReal_swap`)
    2. Diagonal: `V_P x x = a / (a - 1)` (matches the Lean diagonal closed
       form `fractalKernelReal_diagonal` for `a > 1`)
    3. Bounded: `Rabs (V_P x y) <= a / (a - 1)` (matches the Lean uniform
       bound `abs_fractalKernelReal_le` for `a > 1`)

  Under these algebraic hypotheses (which the Lean side proves for the
  actual kernel when `a > 1`), the Coq side mirrors the closed-form
  spectral identities:
    * Level 0: λ_0^(0) = a/(a - 1)
    * Level 1: λ_± = (1/2)(a/(a-1) ± V_P(1/6, 5/6))
    * Trace identity: λ_+ + λ_- = a/(a - 1)
    * Gap identity: λ_+ - λ_- = V_P(1/6, 5/6)
    * Determinant: λ_+ · λ_- = (1/4)((a/(a-1))² - V_P²(1/6, 5/6))
    * Bracketing: 0 ≤ λ_± ≤ a/(a - 1) (PSD + upper bound)

  Status: zero project axioms. Three local algebraic hypotheses on
  the kernel (symmetric, diagonal value, bounded modulus) are taken as
  parameters; on the Lean side, all three are theorems.
*)

Require Import Coq.Reals.Reals.
Require Import Lra.
Require Import Coq.micromega.Psatz.

Open Scope R_scope.

(* ============================================================ *)
(* Section: parametric over (a, V_P) with structural hypotheses  *)
(* ============================================================ *)

Section MatrixSpectrum.

Variable a : R.
Hypothesis Ha : 1 < a.

(** **The (opaque) fractal kernel `V_P : R -> R -> R`**, with the three
    structural hypotheses below as standing assumptions. *)
Variable V_P : R -> R -> R.

(** **Hypothesis 1**: `V_P` is symmetric. *)
Hypothesis V_P_sym : forall x y : R, V_P x y = V_P y x.

(** **Hypothesis 2**: diagonal value `V_P(x, x) = a/(a-1)`. *)
Hypothesis V_P_diag : forall x : R, V_P x x = a / (a - 1).

(** **Hypothesis 3**: uniform modulus bound `|V_P(x, y)| ≤ a/(a-1)`. *)
Hypothesis V_P_bnd : forall x y : R, Rabs (V_P x y) <= a / (a - 1).

(* ============================================================ *)
(* Level-0 single eigenvalue                                     *)
(* ============================================================ *)

(** **Level-0 single eigenvalue**: λ^(0)_0 := a/(a-1). *)
Definition lambdaLevel0 : R := a / (a - 1).

(** **Level-0 positivity**: λ_0 > 0 (from a > 1). *)
Theorem lambdaLevel0_pos : 0 < lambdaLevel0.
Proof.
  unfold lambdaLevel0.
  apply Rdiv_lt_0_compat; lra.
Qed.

(* ============================================================ *)
(* Level-1 closed-form eigenvalues                               *)
(* ============================================================ *)

(** **Level-1 symmetric eigenvalue**:
    λ⁺ := (1/2) · (a/(a-1) + V_P(1/6, 5/6)). *)
Definition lambdaPlusLevel1 : R := (1/2) * (a/(a-1) + V_P (1/6) (5/6)).

(** **Level-1 antisymmetric eigenvalue**:
    λ⁻ := (1/2) · (a/(a-1) - V_P(1/6, 5/6)). *)
Definition lambdaMinusLevel1 : R := (1/2) * (a/(a-1) - V_P (1/6) (5/6)).

(* ============================================================ *)
(* Algebraic identities                                          *)
(* ============================================================ *)

(** **Level-1 trace identity**: λ⁺ + λ⁻ = a/(a-1). *)
Theorem level1_trace_identity :
    lambdaPlusLevel1 + lambdaMinusLevel1 = a / (a - 1).
Proof.
  unfold lambdaPlusLevel1, lambdaMinusLevel1.
  field. lra.
Qed.

(** **Level-1 gap identity**: λ⁺ - λ⁻ = V_P(1/6, 5/6). *)
Theorem level1_gap_identity :
    lambdaPlusLevel1 - lambdaMinusLevel1 = V_P (1/6) (5/6).
Proof.
  unfold lambdaPlusLevel1, lambdaMinusLevel1.
  lra.
Qed.

(** **Level-1 determinant identity**:
    λ⁺ · λ⁻ = (1/4) · ((a/(a-1))² - V_P²(1/6, 5/6)). *)
Theorem level1_det_identity :
    lambdaPlusLevel1 * lambdaMinusLevel1 =
    (1/4) * ((a/(a-1))^2 - (V_P (1/6) (5/6))^2).
Proof.
  unfold lambdaPlusLevel1, lambdaMinusLevel1.
  nra.
Qed.

(** **Level-1 sum of squared eigenvalues** (Frobenius identity):
    λ⁺² + λ⁻² = (1/2) · ((a/(a-1))² + V_P²(1/6, 5/6)). *)
Theorem level1_sumSq_identity :
    lambdaPlusLevel1^2 + lambdaMinusLevel1^2 =
    (1/2) * ((a/(a-1))^2 + (V_P (1/6) (5/6))^2).
Proof.
  unfold lambdaPlusLevel1, lambdaMinusLevel1.
  nra.
Qed.

(* ============================================================ *)
(* Bracketing: 0 ≤ λ⁺, λ⁻ ≤ a/(a-1)                              *)
(* ============================================================ *)

(** **Level-1 symmetric eigenvalue non-negativity** (PSD):
    λ⁺ ≥ 0. From `|V_P| ≤ a/(a-1)` (Hyp 3) → `V_P ≥ -a/(a-1)`. *)
Theorem lambdaPlusLevel1_nonneg : 0 <= lambdaPlusLevel1.
Proof.
  unfold lambdaPlusLevel1.
  assert (Hb := V_P_bnd (1/6) (5/6)).
  assert (Hlow : -(a/(a-1)) <= V_P (1/6) (5/6)).
  { destruct (Rle_or_lt 0 (V_P (1/6) (5/6))) as [Hnn | Hng].
    - assert (Hd_pos : 0 < a/(a-1)) by (apply Rdiv_lt_0_compat; lra).
      lra.
    - rewrite Rabs_left in Hb by exact Hng.
      lra. }
  assert (Hd_pos : 0 < a/(a-1)) by (apply Rdiv_lt_0_compat; lra).
  lra.
Qed.

(** **Level-1 antisymmetric eigenvalue non-negativity** (PSD):
    λ⁻ ≥ 0. Same argument with V_P ≤ a/(a-1). *)
Theorem lambdaMinusLevel1_nonneg : 0 <= lambdaMinusLevel1.
Proof.
  unfold lambdaMinusLevel1.
  assert (Hb := V_P_bnd (1/6) (5/6)).
  assert (Hhigh : V_P (1/6) (5/6) <= a/(a-1)).
  { apply Rle_trans with (Rabs (V_P (1/6) (5/6))).
    - apply Rle_abs.
    - exact Hb. }
  assert (Hd_pos : 0 < a/(a-1)) by (apply Rdiv_lt_0_compat; lra).
  lra.
Qed.

(** **Level-1 symmetric eigenvalue upper bound**: λ⁺ ≤ a/(a-1). *)
Theorem lambdaPlusLevel1_le : lambdaPlusLevel1 <= a / (a - 1).
Proof.
  unfold lambdaPlusLevel1.
  assert (Hb := V_P_bnd (1/6) (5/6)).
  assert (Hhigh : V_P (1/6) (5/6) <= a/(a-1)).
  { apply Rle_trans with (Rabs (V_P (1/6) (5/6))).
    - apply Rle_abs.
    - exact Hb. }
  lra.
Qed.

(** **Level-1 antisymmetric eigenvalue upper bound**: λ⁻ ≤ a/(a-1). *)
Theorem lambdaMinusLevel1_le : lambdaMinusLevel1 <= a / (a - 1).
Proof.
  unfold lambdaMinusLevel1.
  assert (Hb := V_P_bnd (1/6) (5/6)).
  assert (Hlow : -(a/(a-1)) <= V_P (1/6) (5/6)).
  { destruct (Rle_or_lt 0 (V_P (1/6) (5/6))) as [Hnn | Hng].
    - assert (Hd_pos : 0 < a/(a-1)) by (apply Rdiv_lt_0_compat; lra).
      lra.
    - rewrite Rabs_left in Hb by exact Hng.
      lra. }
  lra.
Qed.

(** **Level-1 full spectrum bracketing**: 0 ≤ λ_± ≤ a/(a-1). *)
Theorem level1_spectrum_in_unit_interval :
    (0 <= lambdaPlusLevel1  /\ lambdaPlusLevel1  <= a/(a-1)) /\
    (0 <= lambdaMinusLevel1 /\ lambdaMinusLevel1 <= a/(a-1)).
Proof.
  split; split.
  - exact lambdaPlusLevel1_nonneg.
  - exact lambdaPlusLevel1_le.
  - exact lambdaMinusLevel1_nonneg.
  - exact lambdaMinusLevel1_le.
Qed.

(* ============================================================ *)
(* Cross-level trace consistency                                 *)
(* ============================================================ *)

(** **Trace consistency**: tr M^(0) = λ_0 = λ⁺ + λ⁻ = tr M^(1). *)
Theorem trace_level0_eq_trace_level1 :
    lambdaLevel0 = lambdaPlusLevel1 + lambdaMinusLevel1.
Proof.
  rewrite level1_trace_identity.
  reflexivity.
Qed.

(* ============================================================ *)
(* Operator-theoretic self-adjointness (abstract bilinear form)  *)
(* ============================================================ *)

(** **Abstract operator-self-adjointness via discrete bilinear pairing**:
    for any (z_1, z_2) and test functions (f_1, f_2 / g_1, g_2), the
    discrete bilinear form

      B(f, g) := V_P(z_1, z_1)·f_1·g_1 + V_P(z_1, z_2)·f_2·g_1
              + V_P(z_2, z_1)·f_1·g_2 + V_P(z_2, z_2)·f_2·g_2

    is SYMMETRIC in f and g.

    The 2-point discrete analog of the operator-self-adjointness
    statement `∫ (H_P f) · g dμ = ∫ f · (H_P g) dμ` for a 2-Dirac
    measure μ = δ_{z_1} + δ_{z_2}. Proven purely from kernel symmetry. *)
Theorem discrete_bilinear_form_symmetric (z_1 z_2 : R) (f_1 f_2 g_1 g_2 : R) :
    V_P z_1 z_1 * f_1 * g_1 + V_P z_1 z_2 * f_2 * g_1 +
    V_P z_2 z_1 * f_1 * g_2 + V_P z_2 z_2 * f_2 * g_2 =
    V_P z_1 z_1 * g_1 * f_1 + V_P z_1 z_2 * g_2 * f_1 +
    V_P z_2 z_1 * g_1 * f_2 + V_P z_2 z_2 * g_2 * f_2.
Proof.
  (* Use V_P symmetry: V_P z_1 z_2 = V_P z_2 z_1 *)
  rewrite (V_P_sym z_1 z_2).
  ring.
Qed.

(* ============================================================ *)
(* Level-1 spectral theorem completeness (functional form)       *)
(* ============================================================ *)

(** **Level-1 eigenbasis completeness**: any test function `f` is
    reproduced on the level-1 midpoints `{1/6, 5/6}` by the eigenbasis
    expansion with symmetric coefficient `c_sym = (1/2)(f(1/6) + f(5/6))`
    and antisymmetric coefficient `c_anti = (1/2)(f(1/6) − f(5/6))`:

      `f(1/6) = c_sym + c_anti`
      `f(5/6) = c_sym − c_anti`

    Trivial algebraic identity; the spectral content lies in the
    diagonal action below. *)
Theorem level1_eigenbasis_completeness (f : R -> R) :
    f (1/6) = (1/2) * (f (1/6) + f (5/6)) + (1/2) * (f (1/6) - f (5/6)) /\
    f (5/6) = (1/2) * (f (1/6) + f (5/6)) - (1/2) * (f (1/6) - f (5/6)).
Proof.
  split; lra.
Qed.

(** **Level-1 spectral action at left midpoint**: for any test function
    `f` decomposed in the eigenbasis (`c_sym, c_anti`), the operator
    acts DIAGONALLY:

      `(H_P^disc[μ_1] f)(1/6) = λ⁺ · c_sym + λ⁻ · c_anti`

    where the discrete operator at level 1 is the 2-Dirac integration
    against `(1/2)·δ_{1/6} + (1/2)·δ_{5/6}`. This is the FUNCTIONAL
    form of the spectral theorem at level 1. *)
Theorem level1_spectral_action_at_left
    (c_sym c_anti : R) (f : R -> R)
    (h1 : f (1/6) = c_sym + c_anti) (h2 : f (5/6) = c_sym - c_anti) :
    (1/2) * (V_P (1/6) (1/6) * f (1/6)) +
    (1/2) * (V_P (1/6) (5/6) * f (5/6)) =
    lambdaPlusLevel1 * c_sym + lambdaMinusLevel1 * c_anti.
Proof.
  rewrite h1, h2, V_P_diag.
  unfold lambdaPlusLevel1, lambdaMinusLevel1.
  field. lra.
Qed.

(** **Level-1 spectral action at right midpoint**:

      `(H_P^disc[μ_1] f)(5/6) = λ⁺ · c_sym − λ⁻ · c_anti` *)
Theorem level1_spectral_action_at_right
    (c_sym c_anti : R) (f : R -> R)
    (h1 : f (1/6) = c_sym + c_anti) (h2 : f (5/6) = c_sym - c_anti) :
    (1/2) * (V_P (5/6) (1/6) * f (1/6)) +
    (1/2) * (V_P (5/6) (5/6) * f (5/6)) =
    lambdaPlusLevel1 * c_sym - lambdaMinusLevel1 * c_anti.
Proof.
  rewrite h1, h2, V_P_diag, (V_P_sym (5/6) (1/6)).
  unfold lambdaPlusLevel1, lambdaMinusLevel1.
  field. lra.
Qed.

End MatrixSpectrum.

(* ============================================================ *)
(* Cross-prover parity note                                      *)
(* ============================================================ *)

(** This Coq port mirrors the Lean-side level-0 and level-1 algebraic
    closed-form spectral identities (PF/Analytic/MatrixEntry.lean,
    `lambdaLevel0`, `lambdaPlusLevel1`, `lambdaMinusLevel1`, plus the
    trace / gap / det / sumSq / bracketing identities).

    The Coq side takes the fractal kernel `V_P` as a parameter with
    three algebraic hypotheses (symmetric, diagonal-value, bounded).
    On the Lean side, all three are proven theorems for the concrete
    kernel `fractalKernelReal α a (x, y) := Σ a^(-n) · cos(π · α^n · |x-y|)`.

    Cross-prover validation: the algebraic content of the spectral
    closed forms (purely a function of the kernel values and the
    operator-norm bound) is now mirrored in Coq. The kernel's
    series-definition is not mirrored here (requires Coquelicot for
    a full Coq mirror of `fractalKernelReal`).

    Zero project axioms in this file. *)
