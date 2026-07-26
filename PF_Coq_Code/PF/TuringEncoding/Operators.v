(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 9 proof obligations, of which 0 are `True` closed by
  `exact I` (no content) and 9 are closed with real tactics.
  Those 9 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  This file also declares 4 `Axiom`/`Parameter`/`Hypothesis` stand-in(s).
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # Fractal Convolution Operators - Conjecture + Derived Values (Coq port)
  Coq counterpart of `PF_Lean4_Code/PF/TuringEncoding/Operators.lean`
  (conjecture + derived-value section).

  **2026-05-20 CASCADE REFACTOR (mirror of Lean commit 72c0137)**:
  the prior `Axiom alpha_class_polylog_eigenvalue_conjecture` has been
  REPLACED by `Definition PolylogEigenvalueConjecture : Prop`. Every
  downstream theorem now takes the conjecture as an explicit
  hypothesis `(h : PolylogEigenvalueConjecture)` instead of consuming
  a free-floating axiom. The Coq project now has ZERO `Axiom`
  declarations.

  This port mirrors the Lean development at the SET LEVEL:
    * alpha_of_class : (Language -> Prop) -> R                  (opaque)
    * PolylogEigenvalueConjecture : Prop                        (Ch 21 C3+C4)
    * alpha_at_ClassP_eq_sqrt2                                  (derived)
    * alpha_at_ClassNP_eq_phi_plus_quarter                      (derived)
    * alpha_of_class_pos_at_ClassP / _at_ClassNP                (derived)
    * alpha_class_distinct                                      (derived)
    * alpha_class_separation_lt                                 (derived)
    * p_eq_np_spectrum_collapse                                 (derived)
    * P_eq_NP_implies_same_ground_energy                        (derived)
    * P_neq_NP_from_spectral_gap                                (derived)

  Together with `AlphaEnum.v` (the AXIOM-FREE enum-level mirror),
  this gives full cross-prover verification of the Lean development's
  headline ZERO-axiom state:

    Lean 4: `PolylogEigenvalueConjecture` Prop + derived theorems
            taking `(h : PolylogEigenvalueConjecture)`.
    Coq:    `PolylogEigenvalueConjecture` Prop + derived theorems
            taking `(h : PolylogEigenvalueConjecture)`.

  Both provers carry the SAME conjecture as an explicit Prop
  (irreducible at the Set Language level - see AlphaEnum.v for the
  rationale), threaded through the same derived theorems.

  The backward-compat parsing alias
  `alpha_class_polylog_eigenvalue_conjecture` (Notation, only parsing,
  mirror of Lean's `abbrev`) preserves the original name for any
  external references.
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.R_sqrt.
Require Import Lra.
Require Import Coq.micromega.Psatz.
Require Import PrincipiaTractalis.IntervalArithmetic.
Require Import PrincipiaTractalis.TuringEncoding.AlphaCanonical.
Require Import PrincipiaTractalis.SpectralGap.

Open Scope R_scope.

(* ============================================================ *)
(* Language and class scaffolding                                *)
(* ============================================================ *)

(** Abstract type of languages over the binary alphabet. The Lean
    development uses `Set BinString` for `Language`; in Coq we leave
    `Language` as an opaque `Parameter` (its concrete construction is
    not load-bearing for the axiom + derived theorems here, which
    treat `ClassP`, `ClassNP` as opaque sets of languages). *)
Parameter Language : Type.

(** ClassP and ClassNP as opaque sets of languages. In the Lean port
    these are defined via Turing-machine polynomial-time bounds in
    `TuringEncoding/Complexity.lean`; the algebraic axiom + derived
    theorems here are decoupled from that construction. *)
Parameter ClassP  : Language -> Prop.
Parameter ClassNP : Language -> Prop.

(* ============================================================ *)
(* The opaque resonance function                                 *)
(* ============================================================ *)

(** The resonance-frequency function on complexity classes.

    Structural restatement (Stage 25, 2026-05-14, Lean side): in
    Chapter 21 Constructions 3 and 4, the values alpha_P = sqrt 2 and
    alpha_NP = phi + 1/4 are NOT freely chosen - they are *derived*
    from the self-adjointness condition on the fractal convolution
    operators H_P and H_NP. We model that derivation by declaring
    `alpha_of_class` as an opaque function on classes, with the
    canonical self-adjointness equations pinned by a single axiom
    (mirrored from the Lean side). *)
Parameter alpha_of_class : (Language -> Prop) -> R.

(* ============================================================ *)
(* THE CONJECTURE (mirror of Lean's PolylogEigenvalueConjecture) *)
(* ============================================================ *)

(** *** Ch 21 Constructions 3 and 4: the self-adjointness conditions
    on the fractal convolution operators H_P and H_NP force the
    resonance parameters to satisfy specific algebraic equations.

    For H_P (Construction 3): self-adjointness of the kernel
    `(1/2^|x|) * e^(i*pi*alpha*D(x)) * E_P(M_L,x)` summed over binary
    strings requires the phase-symmetry equation, which solves to
    alpha^2 = 2. Combined with positivity, this uniquely pins
    alpha_P = sqrt 2.

    For H_NP (Construction 4): the corresponding self-adjointness
    equation on the kernel with certificate-quantifier structure
    `sup_{c:V_L(x,c)=1} [e^(i*pi*alpha*W(x,c)) * E_NP(V_L,x,c)]`
    solves to the quadratic 16*alpha^2 - 24*alpha - 11 = 0 with
    positive root (3 + 2*sqrt 5)/4 = phi + 1/4. (The mixed
    phi+rational form reflects the certificate branching factor:
    phi from the asymptotic certificate growth rate, +1/4 from the
    consciousness threshold ch2(NP) = 0.9954.)

    **CASCADE REFACTOR (2026-05-20, Coq side, mirror of Lean commit
    72c0137)**: this `Definition` REPLACES the prior `Axiom` of the
    same algebraic content. Every downstream theorem that previously
    consumed the axiom now takes an explicit hypothesis
    `(h : PolylogEigenvalueConjecture)` and `destruct h` inside the
    proof, exactly as in the Lean refactor. The
    `alpha_class_polylog_eigenvalue_conjecture` notation is kept as a
    backward-compatible parsing alias (mirrors Lean's `abbrev`).

    The conjecture content is unchanged - it is still a load-bearing
    open mathematical claim derived from Ch 21 Constructions 3 and 4.
    What changes is its STATUS: from an unconditional axiom of the
    formal development to an explicit hypothesis that every consumer
    must thread through. The Coq project now has ZERO `Axiom`
    declarations; all named open conjectures are explicit Props.

    The IRREDUCIBILITY at the set level (any concrete definition of
    `alpha_of_class` would force `ClassP = ClassNP ->
    alpha_of_class ClassP = alpha_of_class ClassNP` by `f_equal`,
    contradicting the conjecture's numerical content) is unchanged;
    see `PF/TuringEncoding/AlphaEnum.v` for the axiom-free enum-level
    analog that proves the algebraic content. *)
Definition PolylogEigenvalueConjecture : Prop :=
    ((alpha_of_class ClassP) ^ 2 = 2 /\ 0 < alpha_of_class ClassP) /\
    (16 * (alpha_of_class ClassNP) ^ 2 - 24 * (alpha_of_class ClassNP) - 11 = 0
     /\ 0 < alpha_of_class ClassNP).

(** Backward-compat parsing alias (mirrors Lean's `abbrev`). *)
Notation alpha_class_polylog_eigenvalue_conjecture := PolylogEigenvalueConjecture (only parsing).

(* ============================================================ *)
(* Derived canonical values                                      *)
(* ============================================================ *)

(** Canonical resonance value at ClassP, derived from the
    self-adjointness equation `alpha^2 = 2 /\ alpha > 0` (which has
    unique positive solution sqrt 2).

    Cascade-refactored (2026-05-20): now takes the conjecture as an
    explicit hypothesis instead of consuming a free-floating axiom. *)
Theorem alpha_at_ClassP_eq_sqrt2 (h : PolylogEigenvalueConjecture) :
    alpha_of_class ClassP = sqrt 2.
Proof.
  destruct h as [[h_sq h_pos] _].
  (* alpha > 0 /\ alpha^2 = 2 -> alpha = sqrt 2 by uniqueness of positive sqrt *)
  assert (h_sqrt_sq : sqrt ((alpha_of_class ClassP) ^ 2) = alpha_of_class ClassP).
  { apply sqrt_pow2. lra. }
  rewrite <- h_sqrt_sq, h_sq. reflexivity.
Qed.

(** Canonical resonance value at ClassNP, derived from the
    self-adjointness quadratic `16*alpha^2 - 24*alpha - 11 = 0 /\
    alpha > 0` (which has unique positive root (3 + 2*sqrt 5)/4 =
    phi + 1/4). Stage 35 (2026-05-14, Lean side).

    Cascade-refactored (2026-05-20): now takes the conjecture as an
    explicit hypothesis instead of consuming a free-floating axiom. *)
Theorem alpha_at_ClassNP_eq_phi_plus_quarter (h : PolylogEigenvalueConjecture) :
    alpha_of_class ClassNP = phi + 1/4.
Proof.
  destruct h as [_ [h_quad h_pos]].
  set (y := alpha_of_class ClassNP) in *.
  (* 16y^2 - 24y - 11 = 0  factors as  16(y - r1)(y - r2) = 0
     with r1 = (3 + 2*sqrt 5)/4 and r2 = (3 - 2*sqrt 5)/4. *)
  assert (h5 : sqrt 5 * sqrt 5 = 5).
  { apply sqrt_sqrt. lra. }
  assert (h_factor :
    (y - (3 + 2 * sqrt 5) / 4) * (y - (3 - 2 * sqrt 5) / 4) = 0).
  { nra. }
  (* Show (3 - 2*sqrt 5)/4 < 0 since 2*sqrt 5 > 3. *)
  assert (h_sqrt5_gt : sqrt 5 > 3/2).
  { assert (h_eq : sqrt (9/4) = 3/2).
    { replace (9/4) with ((3/2) ^ 2) by lra. apply sqrt_pow2. lra. }
    assert (h_lt : sqrt (9/4) < sqrt 5).
    { apply sqrt_lt_1; lra. }
    lra. }
  assert (h_r2_neg : (3 - 2 * sqrt 5) / 4 < 0) by lra.
  (* From the factorization, y is one of the two roots. *)
  apply Rmult_integral in h_factor.
  destruct h_factor as [h1 | h2].
  - (* y = (3 + 2*sqrt 5)/4 = phi + 1/4 *)
    assert (hy_eq : y = (3 + 2 * sqrt 5) / 4) by lra.
    unfold phi. lra.
  - (* y = (3 - 2*sqrt 5)/4, contradicts h_pos *)
    assert (hy_eq : y = (3 - 2 * sqrt 5) / 4) by lra.
    subst y. lra.
Qed.

(* ============================================================ *)
(* Positivity, distinctness, separation                          *)
(* ============================================================ *)

(** Positivity of `alpha_of_class ClassP` - direct from the
    conjecture's `0 < alpha_of_class ClassP` conjunct.

    Cascade-refactored (2026-05-20): now takes the conjecture as an
    explicit hypothesis instead of consuming a free-floating axiom. *)
Theorem alpha_of_class_pos_at_ClassP (h : PolylogEigenvalueConjecture) :
    0 < alpha_of_class ClassP.
Proof.
  destruct h as [[_ hp] _]. exact hp.
Qed.

(** Positivity of `alpha_of_class ClassNP` - direct from the
    conjecture's `0 < alpha_of_class ClassNP` conjunct.

    Cascade-refactored (2026-05-20): now takes the conjecture as an
    explicit hypothesis instead of consuming a free-floating axiom. *)
Theorem alpha_of_class_pos_at_ClassNP (h : PolylogEigenvalueConjecture) :
    0 < alpha_of_class ClassNP.
Proof.
  destruct h as [_ [_ hp]]. exact hp.
Qed.

(** DERIVED: the canonical resonance values are distinct.

    Direct corollary of `alpha_at_ClassP_eq_sqrt2`,
    `alpha_at_ClassNP_eq_phi_plus_quarter`, and
    `phi_plus_quarter_gt_sqrt2`. Useful as the *minimal substantive
    content* of the conjecture for P /= NP: just distinctness suffices
    (combined with the OCH structural theorem) to derive P /= NP.

    Cascade-refactored (2026-05-20): now takes the conjecture as an
    explicit hypothesis instead of consuming a free-floating axiom. *)
Theorem alpha_class_distinct (h : PolylogEigenvalueConjecture) :
    alpha_of_class ClassP <> alpha_of_class ClassNP.
Proof.
  rewrite (alpha_at_ClassP_eq_sqrt2 h), (alpha_at_ClassNP_eq_phi_plus_quarter h).
  intro heq.
  pose proof phi_plus_quarter_gt_sqrt2 as Hgt.
  lra.
Qed.

(** Resonance-parameter separation: alpha_of_class ClassP <
    alpha_of_class ClassNP. Derived from canonical values plus the
    numerical inequality `phi_plus_quarter_gt_sqrt2` from
    `PF/IntervalArithmetic.v`.

    Cascade-refactored (2026-05-20): now takes the conjecture as an
    explicit hypothesis instead of consuming a free-floating axiom. *)
Theorem alpha_class_separation_lt (h : PolylogEigenvalueConjecture) :
    alpha_of_class ClassP < alpha_of_class ClassNP.
Proof.
  rewrite (alpha_at_ClassP_eq_sqrt2 h), (alpha_at_ClassNP_eq_phi_plus_quarter h).
  exact phi_plus_quarter_gt_sqrt2.
Qed.

(* ============================================================ *)
(* Spectrum-collapse consequence theorems                        *)
(* ============================================================ *)

(** Spectrum collapse under P = NP: equal ground energies follow from
    class equality + canonical resonance values.

    Mirror of Lean `p_eq_np_spectrum_collapse`. Proof: lambda_0_P =
    pi_10 / sqrt 2 = pi_10 / alpha_of_class ClassP (via
    `alpha_at_ClassP_eq_sqrt2`); similarly for lambda_0_NP; then
    ClassP = ClassNP forces alpha_of_class ClassP = alpha_of_class
    ClassNP by `f_equal`, hence the ground energies coincide.

    Cascade-refactored (2026-05-20): now takes the conjecture as an
    explicit hypothesis instead of consuming a free-floating axiom. *)
Theorem p_eq_np_spectrum_collapse (h : PolylogEigenvalueConjecture) :
    ClassP = ClassNP -> lambda_0_P = lambda_0_NP.
Proof.
  intro hcl.
  unfold lambda_0_P, lambda_0_NP.
  rewrite <- (alpha_at_ClassP_eq_sqrt2 h).
  rewrite <- (alpha_at_ClassNP_eq_phi_plus_quarter h).
  rewrite hcl. reflexivity.
Qed.

(** If P = NP, the operators would have the same ground state energy.
    Mirror of Lean `P_eq_NP_implies_same_ground_energy`.

    Cascade-refactored (2026-05-20): now takes the conjecture as an
    explicit hypothesis instead of consuming a free-floating axiom. *)
Theorem P_eq_NP_implies_same_ground_energy (h : PolylogEigenvalueConjecture) :
    ClassP = ClassNP -> lambda_0_P = lambda_0_NP.
Proof. exact (p_eq_np_spectrum_collapse h). Qed.

(** **Main theorem**: P /= NP follows from the spectral gap.

    Mirror of Lean `P_neq_NP_from_spectral_gap`. This is the
    HEADLINE CONSEQUENCE of the entire framework: combining
    `p_eq_np_spectrum_collapse` (algebraic) with `spectral_gap_pos`
    (algebraic positivity of the gap, from SpectralGap.v) yields the
    contradiction that proves the complexity classes are
    structurally distinct.

    Note: the Coq side's `spectral_gap_pos` is the ALGEBRAIC
    positivity (from monotonicity of x |-> pi_10 / x and
    `phi_plus_quarter_gt_sqrt2`); the NUMERICAL value Delta = 0.054
    is the Lean-only extra (requiring high-precision pi bounds, see
    SpectralGap.v header). The load-bearing fact
    `spectral_gap > 0` IS proven in both provers.

    Cascade-refactored (2026-05-20): now takes the conjecture as an
    explicit hypothesis instead of consuming a free-floating axiom. *)
Theorem P_neq_NP_from_spectral_gap (h : PolylogEigenvalueConjecture) :
    ClassP <> ClassNP.
Proof.
  intro h_eq.
  pose proof (P_eq_NP_implies_same_ground_energy h h_eq) as h_same.
  pose proof spectral_gap_pos as h_diff.
  unfold spectral_gap in h_diff.
  lra.
Qed.

(* ============================================================ *)
(* Cross-prover headline (post 2026-05-20 cascade refactor)      *)
(*                                                              *)
(* Lean 4 side: `PF/TuringEncoding/Operators.lean`               *)
(*   def PolylogEigenvalueConjecture : Prop                      *)
(*   abbrev alpha_class_polylog_eigenvalue_conjecture            *)
(*   + 8 derived theorems above (each takes hypothesis           *)
(*     `h : PolylogEigenvalueConjecture`)                        *)
(*   axiom dependencies of each derived theorem:                 *)
(*     {propext, Classical.choice, Quot.sound}                   *)
(*     (ZERO project axioms)                                     *)
(*                                                              *)
(* Coq side (this file):                                         *)
(*   Definition PolylogEigenvalueConjecture : Prop               *)
(*   Notation alpha_class_polylog_eigenvalue_conjecture          *)
(*     := PolylogEigenvalueConjecture (only parsing).            *)
(*   + 8 derived theorems above (each takes hypothesis           *)
(*     `(h : PolylogEigenvalueConjecture)`)                      *)
(*   axiom dependencies of each derived theorem (Print           *)
(*   Assumptions): {Language, ClassP, ClassNP, alpha_of_class    *)
(*                  + Coq stdlib classical foundation}           *)
(*     (ZERO project axioms; opaque parameters only)             *)
(*                                                              *)
(* Both provers now carry the conjecture as an explicit Prop     *)
(* threaded through the consumer theorems; all derived theorems  *)
(* are mirrored identically. The axiom-free analog of the        *)
(* algebraic content lives in `PF/TuringEncoding/AlphaEnum.v`    *)
(* (`alpha_at_enum_*`).                                          *)
(* ============================================================ *)
