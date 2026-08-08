/-
# r213: Finite two-state transfer systems — partition function, matrix product,
#       the zero-cooperativity limit, and reversal invariance.

## WHAT THIS FILE IS — AND WHAT IT IS NOT

This file is PURE MATHEMATICS about finite two-state chains.

Everything below is a theorem about a finite chain of `n+1` sites, each site
carrying an ABSTRACT real weight pair `w i false, w i true : ℝ`, with an
ABSTRACT real junction weight `J : ℝ` charged once at every adjacent
disagreement.

There is, BY DESIGN, no biological constant, no energy, no temperature, no
sequence, and no biological claim anywhere in this file.  The weights are
symbols.  Nothing here converts to a number until someone supplies external,
experimentally grounded inputs, and this file supplies none.

**THIS FILE MUST NOT BE CITED AS SUPPORT FOR ANY CLAIM ABOUT B→Z TRANSITIONS,
Z-DNA, OR ANY NUCLEOTIDE SEQUENCE.**  It proves nothing whatsoever about them.
It is a statement about a class of models, not about the world.  Any biological
parameter claim stays explicitly external.

## The object

For a configuration `s : Fin (n+1) → Bool` of a chain with sites `0, …, n`:

    cfgWeight J w s  =  (∏ i, w i (s i)) · J ^ #{ junctions where s disagrees }
    Zpf J w n        =  ∑ over all 2^(n+1) configurations s of cfgWeight J w s

`Fin (n+1) → Bool` is a `Fintype`, so the sum is a genuine finite sum.
The junction-count form is `prod_bond_eq_pow` (§1); the definition itself uses
the equivalent product of per-junction factors, which is what induction wants.

We work over plain `ℝ`, not `ℝ≥0`.  Nonnegativity is never used: every theorem
below is an algebraic identity (or, in §4, an inequality between two explicit
rational numbers), and none of them needs a sign hypothesis.  Restricting to
positive weights would only weaken the statements.

## What is proved

* §1  definitions: `bond`, `cfgTail`, `cfgWeight`, `Zpf`, the transfer matrices
      `Mat`/`Mstep`, their ordered product `Mprod`, and `prod_bond_eq_pow`
      showing the definition really is `J ^ (number of disagreeing junctions)`.

* §2  `Zpf_eq_vecMul` — THE MAIN THEOREM.  The configuration sum equals the
      ordered matrix product contracted with the boundary vector `w 0`:

          Zpf J w n  =  ∑_b ( w 0 ᵥ* (M₀ M₁ ⋯ M_{n-1}) )_b ,
          (M_k)_{a b} = bond J a b · w (k+1) b .

      Proved by induction on `n` from the master lemma `sum_cfgTail_eq`, which
      is stated with a general boundary kernel `K : Bool → Bool → ℝ` precisely
      so that the cyclic case (§6) falls out of the same induction.
      This is the "transfer operator = conventional partition function"
      identity.

* §3  `Zpf_one_eq_prod` — THE ZERO-COOPERATIVITY LIMIT.

          Zpf 1 w n = ∏ i, ( w i false + w i true ).

      At `J = 1` every transfer matrix becomes rank one, the sum factorizes
      over sites, and the chain is a collection of independent sites.
      **This is the theorem that says: the additive nearest-neighbour model is
      exactly the `J = 1` limit of the transfer model.**  Proved straight from
      the definition via `Finset.prod_univ_sum` / `Fintype.piFinset_univ`; it
      does not use §2.

* §4  `Zpf_one_perm` — THE COROLLARY THAT MATTERS.  At `J = 1`, permuting the
      site weights does not change `Zpf`.  Only the MULTISET of site weights
      survives.  Consequently a `J = 1` model cannot distinguish two arrangements
      of the same collection of sites — the ORDER of the sites is invisible to it.

      **And the sharpness witness, `Zpf_two_AAB_ne_ABA`:** with three sites, two
      distinct weight pairs `A = (1,2)` and `B = (1,3)` (giving `false`- and
      `true`-weights), and `J = 2`,

          Zpf 2 (A,A,B) 2 = 75   ≠   73 = Zpf 2 (A,B,A) 2 ,

      while at `J = 1` both equal `36` (`Zpf_one_AAB_eq_ABA`, `= 3·3·4`).
      The two weight functions are literally a transposition of each other
      (`wABA_perm_wAAB`), so this is exactly the failure of §4 off `J = 1`.
      Non-commutativity of the transfer matrices IS the cooperativity.

      **Reading of §3 + §4 together.**  Any model in this class that
      distinguishes two arrangements of the same multiset of sites does so
      through `J ≠ 1` cooperativity, and NOT through any word structure,
      grammar, or higher-order pattern in the arrangement.  A separation
      observed in such a model is evidence for nearest-neighbour cooperativity,
      nothing more.  Whether a real system is in this class is an external
      empirical question this file does not touch.

* §5  `Zpf_reverse` — reversal invariance.  Reindexing the site weights by
      `Fin.rev` leaves `Zpf` unchanged, for every `J`.  The configuration sum
      is reindexed by `Fin.rev` and the junction set is symmetric under
      adjacency (`Fin.rev_castSucc`, `Fin.rev_succ`, `bond_comm`).

* §6  (stretch) the cyclic chain: `ZpfCyc_eq_trace` puts the extra wrap-around
      junction into a trace, `ZpfCyc J w n = trace (Mprod J n w * Mat J (w 0))`,
      and `ZpfCyc_rotate` is cyclic invariance of the site labelling, proved
      from `Matrix.trace_mul_comm`.

## Cross-reference

`codex/bz_cooperativity_test_2026-08-06.py` is a numerical script that
instantiates this same model class with ILLUSTRATIVE, EXTERNAL parameters and
sweeps them.  Its own header says the parameters are not literature values.
That script is the motivation for formalizing the model class; it is not
evidence for anything, and neither is this file.  In particular the script's
self-falsifier ("at zero junction penalty the two sequences must come out
exactly equal, because at zero cooperativity the partition function depends
only on composition") is precisely §3 + §4 here, now a theorem rather than an
assertion.

## Indexing convention

`Zpf J w n` is the chain with `n+1` SITES `0, …, n` and `n` JUNCTIONS.
Site weights are supplied as a total function `w : ℕ → Bool → ℝ`; only the
values `w 0, …, w n` are ever read.  A `Fin`-indexed weight family is used by
extending it arbitrarily; every theorem whose statement compares two weight
functions does so through a hypothesis quantified over `i : Fin (n+1)`, so the
extension is irrelevant.  The ℕ-indexing is deliberate: peeling the head site
off the chain then shifts `w` by `+1` with no dependent-type transport, which
is what makes every induction below go through.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.
Axiom audit at the end of the file.
-/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

namespace PrincipiaTractalis.TwoStateTransfer

open scoped BigOperators
open Matrix

/-! ## §1  The finite two-state transfer system -/

/-- The junction factor: `1` if the two adjacent sites agree, `J` if they
disagree.  `J` is an abstract real number. -/
def bond (J : ℝ) (a b : Bool) : ℝ := if a = b then 1 else J

@[simp] lemma bond_self (J : ℝ) (a : Bool) : bond J a a = 1 := by simp [bond]

/-- The junction factor is symmetric: a junction has no orientation. -/
lemma bond_comm (J : ℝ) (a b : Bool) : bond J a b = bond J b a := by
  cases a <;> cases b <;> simp [bond]

/-- At `J = 1` every junction is free.  This is the zero-cooperativity point. -/
@[simp] lemma bond_one (a b : Bool) : bond 1 a b = 1 := by
  cases a <;> cases b <;> simp [bond]

/-- Shift the site-weight family by one site.  Peeling the head site off a
chain replaces `w` by `shift w`. -/
def shift (w : ℕ → Bool → ℝ) : ℕ → Bool → ℝ := fun k => w (k + 1)

@[simp] lemma shift_apply (w : ℕ → Bool → ℝ) (k : ℕ) : shift w k = w (k + 1) := rfl

/-- The configuration weight WITHOUT the site-`0` factor: the product of the
site weights of sites `1, …, n` times the product of all `n` junction factors.
Splitting the site-`0` factor off is what lets the induction carry a boundary
vector. -/
def cfgTail (J : ℝ) (w : ℕ → Bool → ℝ) {n : ℕ} (s : Fin (n + 1) → Bool) : ℝ :=
  (∏ i : Fin n, w ((i : ℕ) + 1) (s i.succ)) *
    ∏ i : Fin n, bond J (s i.castSucc) (s i.succ)

/-- The weight of a single configuration `s` of the chain with sites `0, …, n`:
the product of the site weights times the product of the junction factors. -/
def cfgWeight (J : ℝ) (w : ℕ → Bool → ℝ) {n : ℕ} (s : Fin (n + 1) → Bool) : ℝ :=
  w 0 (s 0) * cfgTail J w s

/-- The partition function: the sum of `cfgWeight` over all `2^(n+1)`
configurations.  `Fin (n+1) → Bool` is a `Fintype`. -/
def Zpf (J : ℝ) (w : ℕ → Bool → ℝ) (n : ℕ) : ℝ :=
  ∑ s : Fin (n + 1) → Bool, cfgWeight J w s

/-- `cfgWeight` in the advertised form: site product times junction product. -/
lemma cfgWeight_eq (J : ℝ) (w : ℕ → Bool → ℝ) {n : ℕ} (s : Fin (n + 1) → Bool) :
    cfgWeight J w s =
      (∏ i : Fin (n + 1), w (i : ℕ) (s i)) *
        ∏ i : Fin n, bond J (s i.castSucc) (s i.succ) := by
  rw [cfgWeight, cfgTail, Fin.prod_univ_succ]
  simp only [Fin.val_succ, Fin.val_zero]
  ring

/-- The junction product really is `J` raised to the number of adjacent
disagreements.  This is the `J ^ card {i : s i ≠ s (i+1)}` of the informal
statement. -/
lemma prod_bond_eq_pow (J : ℝ) {n : ℕ} (s : Fin (n + 1) → Bool) :
    (∏ i : Fin n, bond J (s i.castSucc) (s i.succ)) =
      J ^ ({i : Fin n | s i.castSucc ≠ s i.succ} : Finset (Fin n)).card := by
  classical
  rw [show (∏ i : Fin n, bond J (s i.castSucc) (s i.succ)) =
      ∏ i : Fin n, if s i.castSucc = s i.succ then (1 : ℝ) else J from rfl]
  rw [Finset.prod_ite]
  simp [Finset.prod_const, Finset.filter_not]

/-- The one-step transfer matrix attached to a site weight `u`. -/
def Mat (J : ℝ) (u : Bool → ℝ) : Matrix Bool Bool ℝ := fun a b => bond J a b * u b

@[simp] lemma Mat_apply (J : ℝ) (u : Bool → ℝ) (a b : Bool) :
    Mat J u a b = bond J a b * u b := rfl

/-- The `k`-th transfer matrix of the chain: it carries the junction between
sites `k` and `k+1` and the site weight of site `k+1`. -/
def Mstep (J : ℝ) (w : ℕ → Bool → ℝ) (k : ℕ) : Matrix Bool Bool ℝ := Mat J (w (k + 1))

@[simp] lemma Mstep_apply (J : ℝ) (w : ℕ → Bool → ℝ) (k : ℕ) (a b : Bool) :
    Mstep J w k a b = bond J a b * w (k + 1) b := rfl

lemma Mstep_shift (J : ℝ) (w : ℕ → Bool → ℝ) (k : ℕ) :
    Mstep J (shift w) k = Mstep J w (k + 1) := rfl

/-- The ORDERED product `M₀ M₁ ⋯ M_{n-1}` of the transfer matrices.
Matrices do not commute, so this is a genuine ordered product, defined by
recursion peeling the leftmost factor. -/
def Mprod (J : ℝ) : ℕ → (ℕ → Bool → ℝ) → Matrix Bool Bool ℝ
  | 0, _ => 1
  | (k + 1), w => Mstep J w 0 * Mprod J k (shift w)

@[simp] lemma Mprod_zero (J : ℝ) (w : ℕ → Bool → ℝ) : Mprod J 0 w = 1 := rfl

@[simp] lemma Mprod_succ (J : ℝ) (k : ℕ) (w : ℕ → Bool → ℝ) :
    Mprod J (k + 1) w = Mstep J w 0 * Mprod J k (shift w) := rfl

/-- `Mprod J n w` reads only `w 1, …, w n`. -/
lemma Mprod_congr (J : ℝ) :
    ∀ (n : ℕ) (w₁ w₂ : ℕ → Bool → ℝ), (∀ k : ℕ, k < n → w₁ (k + 1) = w₂ (k + 1)) →
      Mprod J n w₁ = Mprod J n w₂ := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ m ih =>
      intro w₁ w₂ h
      rw [Mprod_succ, Mprod_succ, Mstep, Mstep, h 0 (Nat.succ_pos m)]
      congr 1
      exact ih (shift w₁) (shift w₂) (fun k hk => h (k + 1) (by omega))

/-- Peeling the RIGHTMOST factor instead of the leftmost. -/
lemma Mprod_succ_right (J : ℝ) :
    ∀ (n : ℕ) (w : ℕ → Bool → ℝ),
      Mprod J (n + 1) w = Mprod J n w * Mat J (w (n + 1)) := by
  intro n
  induction n with
  | zero => intro w; simp [Mprod, Mstep]
  | succ m ih =>
      intro w
      rw [Mprod_succ, ih (shift w), ← mul_assoc, ← Mprod_succ]
      rfl

/-! ### Reindexing configurations -/

/-- Splitting a configuration into (head spin, tail configuration). -/
def consEquiv (m : ℕ) : Bool × (Fin m → Bool) ≃ (Fin (m + 1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun s := (s 0, Fin.tail s)
  left_inv p := by simp
  right_inv s := Fin.cons_self_tail s

/-- Sum over configurations of a chain, split on the head spin. -/
lemma sum_cfg_succ {m : ℕ} (F : (Fin (m + 1) → Bool) → ℝ) :
    (∑ s : Fin (m + 1) → Bool, F s) =
      ∑ a : Bool, ∑ t : Fin m → Bool, F (Fin.cons a t) := by
  have h := Fintype.sum_equiv (consEquiv m)
      (fun p : Bool × (Fin m → Bool) => F (Fin.cons p.1 p.2)) F (fun _ => rfl)
  rw [← h, Fintype.sum_prod_type]

/-- A one-site chain has exactly two configurations. -/
lemma sum_cfg_one (F : (Fin 1 → Bool) → ℝ) :
    (∑ s : Fin 1 → Bool, F s) = ∑ a : Bool, F (fun _ => a) := by
  exact (Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool).symm
    (fun a : Bool => F (fun _ => a)) F (fun _ => rfl)).symm

/-! ### Peeling the head site off `cfgTail` -/

lemma cfgTail_one (J : ℝ) (w : ℕ → Bool → ℝ) (s : Fin 1 → Bool) :
    cfgTail J w s = 1 := by
  simp [cfgTail]

lemma cfgTail_succ (J : ℝ) (w : ℕ → Bool → ℝ) {m : ℕ} (s : Fin (m + 2) → Bool) :
    cfgTail J w s = Mstep J w 0 (s 0) (Fin.tail s 0) * cfgTail J (shift w) (Fin.tail s) := by
  have hsite : (∏ i : Fin (m + 1), w ((i : ℕ) + 1) (s i.succ)) =
      w 1 (Fin.tail s 0) * ∏ i : Fin m, shift w ((i : ℕ) + 1) (Fin.tail s i.succ) := by
    rw [Fin.prod_univ_succ]
    congr 1
  have hbond : (∏ i : Fin (m + 1), bond J (s i.castSucc) (s i.succ)) =
      bond J (s 0) (Fin.tail s 0) *
        ∏ i : Fin m, bond J (Fin.tail s i.castSucc) (Fin.tail s i.succ) := by
    rw [Fin.prod_univ_succ]
    congr 1
  rw [cfgTail, hsite, hbond, cfgTail, Mstep_apply]
  ring

/-! ## §2  MAIN THEOREM — the partition function is an ordered matrix product -/

/-- **Master lemma.**  For an arbitrary boundary kernel `K` coupling the first
and last spins, the configuration sum collapses to the ordered matrix product.
Stated with a general `K` so that both the open chain (§2) and the cyclic chain
(§6) are instances of the same induction. -/
lemma sum_cfgTail_eq (J : ℝ) :
    ∀ (n : ℕ) (w : ℕ → Bool → ℝ) (K : Bool → Bool → ℝ),
      (∑ s : Fin (n + 1) → Bool, K (s 0) (s (Fin.last n)) * cfgTail J w s) =
        ∑ a : Bool, ∑ b : Bool, K a b * Mprod J n w a b := by
  intro n
  induction n with
  | zero =>
      intro w K
      rw [sum_cfg_one]
      simp [cfgTail_one, Matrix.one_apply]
  | succ m ih =>
      intro w K
      rw [sum_cfg_succ]
      have step : ∀ (a : Bool) (t : Fin (m + 1) → Bool),
          K ((Fin.cons a t : Fin (m + 2) → Bool) 0)
              ((Fin.cons a t : Fin (m + 2) → Bool) (Fin.last (m + 1))) *
            cfgTail J w (Fin.cons a t) =
          K a (t (Fin.last m)) * Mstep J w 0 a (t 0) * cfgTail J (shift w) t := by
        intro a t
        rw [cfgTail_succ]
        have h0 : (Fin.cons a t : Fin (m + 2) → Bool) 0 = a := by simp
        have ht : Fin.tail (Fin.cons a t : Fin (m + 2) → Bool) = t := by simp
        have hl : (Fin.cons a t : Fin (m + 2) → Bool) (Fin.last (m + 1))
            = t (Fin.last m) := by
          rw [← Fin.succ_last, Fin.cons_succ]
        rw [h0, ht, hl]
        ring
      -- Collapse the head spin into a new boundary kernel, then apply the IH.
      have e1 : (∑ a : Bool, ∑ t : Fin (m + 1) → Bool,
                  K ((Fin.cons a t : Fin (m + 2) → Bool) 0)
                    ((Fin.cons a t : Fin (m + 2) → Bool) (Fin.last (m + 1))) *
                      cfgTail J w (Fin.cons a t))
          = ∑ t : Fin (m + 1) → Bool,
              (fun c d => ∑ a : Bool, K a d * Mstep J w 0 a c) (t 0) (t (Fin.last m)) *
                cfgTail J (shift w) t := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => step a t
      rw [e1, ih (shift w) (fun c d => ∑ a : Bool, K a d * Mstep J w 0 a c), Mprod_succ]
      simp only [Matrix.mul_apply, Fintype.sum_bool]
      ring

/-- **THE MAIN THEOREM (§2).**  The conventional partition function — a sum over
all `2^(n+1)` configurations — equals the boundary vector `w 0` pushed through
the ORDERED product of the transfer matrices.

This is the "transfer operator = partition function" identity for the finite
two-state chain, with abstract weights. -/
theorem Zpf_eq_vecMul (J : ℝ) (w : ℕ → Bool → ℝ) (n : ℕ) :
    Zpf J w n = ∑ b : Bool, (Matrix.vecMul (w 0) (Mprod J n w)) b := by
  have h := sum_cfgTail_eq J n w (fun a _ => w 0 a)
  rw [Zpf]
  rw [show (∑ s : Fin (n + 1) → Bool, cfgWeight J w s) =
      ∑ s : Fin (n + 1) → Bool, (fun a _ => w 0 a) (s 0) (s (Fin.last n)) * cfgTail J w s from
    Finset.sum_congr rfl fun s _ => rfl]
  rw [h, Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => rfl

/-- The same identity in dot-product form: `Zpf = (w 0) ᵥ* (M₀⋯M_{n-1}) ⬝ᵥ 𝟙`. -/
theorem Zpf_eq_dotProduct (J : ℝ) (w : ℕ → Bool → ℝ) (n : ℕ) :
    Zpf J w n = dotProduct (Matrix.vecMul (w 0) (Mprod J n w)) (fun _ => 1) := by
  rw [Zpf_eq_vecMul, dotProduct]
  exact Finset.sum_congr rfl fun b _ => by ring

/-! ## §3  ZERO-COOPERATIVITY LIMIT: at `J = 1` the chain factorizes -/

/-- **THE ZERO-COOPERATIVITY LIMIT (§3).**  At `J = 1` all junction factors are
`1`, the transfer matrices become rank one, and the partition function is the
product of the independent single-site partition functions:

    Zpf 1 w n = ∏ i, (w i false + w i true).

**This is the theorem saying that the additive nearest-neighbour model is
exactly the commuting `J = 1` limit of the transfer model.** -/
theorem Zpf_one_eq_prod (w : ℕ → Bool → ℝ) (n : ℕ) :
    Zpf 1 w n = ∏ i : Fin (n + 1), (w (i : ℕ) false + w (i : ℕ) true) := by
  classical
  have hcfg : ∀ s : Fin (n + 1) → Bool,
      cfgWeight 1 w s = ∏ i : Fin (n + 1), w (i : ℕ) (s i) := by
    intro s
    rw [cfgWeight_eq]
    simp
  have hsum : Zpf 1 w n = ∑ s : Fin (n + 1) → Bool, ∏ i : Fin (n + 1), w (i : ℕ) (s i) := by
    rw [Zpf]
    exact Finset.sum_congr rfl fun s _ => hcfg s
  rw [hsum]
  have hprod :
      (∏ i : Fin (n + 1), ∑ b ∈ (Finset.univ : Finset Bool), w (i : ℕ) b) =
        ∑ x ∈ Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ : Finset Bool)),
          ∏ i : Fin (n + 1), w (i : ℕ) (x i) :=
    Finset.prod_univ_sum _ _
  rw [Fintype.piFinset_univ] at hprod
  rw [← hprod]
  exact Finset.prod_congr rfl fun i _ => by
    rw [Fintype.sum_bool]; ring

/-! ## §4  THE COROLLARY THAT MATTERS, AND ITS SHARPNESS WITNESS -/

/-- **§4, the corollary.**  At `J = 1`, permuting the site weights leaves the
partition function unchanged: only the MULTISET of site weights matters.

So a `J = 1` (additive, zero-cooperativity) model is BLIND to the arrangement
of the sites.  It cannot separate two arrangements of the same collection of
site weights, no matter what pattern they form. -/
theorem Zpf_one_perm (w w' : ℕ → Bool → ℝ) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (h : ∀ i : Fin (n + 1), w' (i : ℕ) = w ((σ i : Fin (n + 1)) : ℕ)) :
    Zpf 1 w' n = Zpf 1 w n := by
  rw [Zpf_one_eq_prod, Zpf_one_eq_prod]
  exact Fintype.prod_equiv σ _ _ fun i => by rw [h i]

/-! ### The sharpness witness: §4 FAILS for `J ≠ 1`

Three sites, two distinct site weight pairs

    A : false ↦ 1, true ↦ 2        B : false ↦ 1, true ↦ 3

arranged as `A A B` and `A B A`.  These are the same multiset — literally a
transposition of each other — so §4 forces them equal at `J = 1`.
At `J = 2` they are `75` and `73`.
-/

/-- A site with `false`-weight `1` and `true`-weight `x`. -/
def site (x : ℝ) : Bool → ℝ := fun b => if b then x else 1

@[simp] lemma site_false (x : ℝ) : site x false = 1 := rfl
@[simp] lemma site_true (x : ℝ) : site x true = x := rfl

/-- Sites `A, A, B`. -/
def wAAB : ℕ → Bool → ℝ := fun k => if k = 2 then site 3 else site 2

/-- Sites `A, B, A`. -/
def wABA : ℕ → Bool → ℝ := fun k => if k = 1 then site 3 else site 2

@[simp] lemma wAAB_zero : wAAB 0 = site 2 := rfl
@[simp] lemma wAAB_one : wAAB 1 = site 2 := rfl
@[simp] lemma wAAB_two : wAAB 2 = site 3 := rfl
@[simp] lemma wABA_zero : wABA 0 = site 2 := rfl
@[simp] lemma wABA_one : wABA 1 = site 3 := rfl
@[simp] lemma wABA_two : wABA 2 = site 2 := rfl

/-- `wABA` is `wAAB` reindexed by the transposition `(1 2)`: same multiset of
site weights, different arrangement. -/
lemma wABA_perm_wAAB :
    ∀ i : Fin 3, wABA (i : ℕ) = wAAB ((Equiv.swap (1 : Fin 3) (2 : Fin 3) i : Fin 3) : ℕ) := by
  intro i
  fin_cases i <;> rfl

/-- Closed form of `Zpf` for a three-site chain, from the §2 matrix product. -/
lemma Zpf_two_closed (J : ℝ) (w : ℕ → Bool → ℝ) :
    Zpf J w 2 =
      ∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
        w 0 a * bond J a b * w 1 b * bond J b c * w 2 c := by
  rw [Zpf_eq_vecMul]
  simp only [Mprod_succ, Mprod_zero, mul_one, Matrix.vecMul, Matrix.mul_apply,
    dotProduct, Mstep_apply, shift_apply, Fintype.sum_bool]
  ring

/-- At `J = 1` the two arrangements agree (both `= 3 · 3 · 4 = 36`), exactly as
§4 requires. -/
theorem Zpf_one_AAB_eq_ABA : Zpf 1 wAAB 2 = 36 ∧ Zpf 1 wABA 2 = 36 := by
  constructor <;>
  · rw [Zpf_two_closed]
    simp only [Fintype.sum_bool, bond_one, wAAB_zero, wAAB_one, wAAB_two,
      wABA_zero, wABA_one, wABA_two, site_false, site_true]
    norm_num

/-- **THE SHARPNESS WITNESS (§4).**  At `J = 2` the two arrangements — the same
multiset of site weights, differing only by the transposition `(1 2)` — have
DIFFERENT partition functions: `75 ≠ 73`.

So the invariance of `Zpf_one_perm` is exactly a `J = 1` phenomenon.  The
non-commutativity of the transfer matrices IS the cooperativity, and it is the
only thing in this model class that can see the arrangement of the sites. -/
theorem Zpf_two_AAB_ne_ABA : Zpf 2 wAAB 2 = 75 ∧ Zpf 2 wABA 2 = 73 := by
  constructor <;>
  · rw [Zpf_two_closed]
    simp only [Fintype.sum_bool, bond, wAAB_zero, wAAB_one, wAAB_two,
      wABA_zero, wABA_one, wABA_two, site_false, site_true]
    norm_num

/-- The witness, stated as the failure it is. -/
theorem Zpf_perm_fails_off_one : Zpf 2 wAAB 2 ≠ Zpf 2 wABA 2 := by
  rw [Zpf_two_AAB_ne_ABA.1, Zpf_two_AAB_ne_ABA.2]
  norm_num

/-! ## §5  REVERSAL INVARIANCE -/

/-- Reversing a configuration of the chain. -/
def revEquiv (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Fin (n + 1) → Bool) where
  toFun s := fun i => s i.rev
  invFun s := fun i => s i.rev
  left_inv s := by funext i; simp
  right_inv s := by funext i; simp

/-- **REVERSAL INVARIANCE (§5).**  Reading the chain backwards — reindexing the
site weights by `Fin.rev` — does not change the partition function, for any
junction weight `J`.  The site product is reindexed by `Fin.rev`, and the
junction set is symmetric under adjacency: `rev` swaps `castSucc` and `succ`,
and `bond` is symmetric in its two spins. -/
theorem Zpf_reverse (J : ℝ) (w w' : ℕ → Bool → ℝ) (n : ℕ)
    (h : ∀ i : Fin (n + 1), w' (i : ℕ) = w ((i.rev : Fin (n + 1)) : ℕ)) :
    Zpf J w' n = Zpf J w n := by
  refine Fintype.sum_equiv (revEquiv n) _ _ ?_
  intro s
  rw [cfgWeight_eq, cfgWeight_eq]
  have hsite : (∏ i : Fin (n + 1), w' (i : ℕ) (s i)) =
      ∏ i : Fin (n + 1), w (i : ℕ) ((revEquiv n s) i) := by
    refine Fintype.prod_equiv (Fin.revPerm) _ _ ?_
    intro i
    rw [h i]
    simp [revEquiv, Fin.revPerm]
  have hbond : (∏ i : Fin n, bond J (s i.castSucc) (s i.succ)) =
      ∏ i : Fin n, bond J ((revEquiv n s) i.castSucc) ((revEquiv n s) i.succ) := by
    refine Fintype.prod_equiv (Fin.revPerm) _ _ ?_
    intro i
    show bond J (s i.castSucc) (s i.succ) =
      bond J (s ((Fin.revPerm i : Fin n).castSucc).rev) (s ((Fin.revPerm i : Fin n).succ).rev)
    have h1 : ((Fin.revPerm i : Fin n).castSucc).rev = (Fin.revPerm i : Fin n).rev.succ :=
      Fin.rev_castSucc _
    have h2 : ((Fin.revPerm i : Fin n).succ).rev = (Fin.revPerm i : Fin n).rev.castSucc :=
      Fin.rev_succ _
    rw [h1, h2]
    have h3 : (Fin.revPerm i : Fin n).rev = i := by simp [Fin.revPerm]
    rw [h3]
    exact bond_comm J _ _
  rw [hsite, hbond]

/-! ## §6  (stretch) The cyclic chain and the trace formula -/

/-- The cyclic configuration weight: the open-chain weight times one extra
junction factor between the last site and site `0`. -/
def cfgWeightCyc (J : ℝ) (w : ℕ → Bool → ℝ) {n : ℕ} (s : Fin (n + 1) → Bool) : ℝ :=
  w 0 (s 0) * bond J (s (Fin.last n)) (s 0) * cfgTail J w s

/-- The cyclic partition function. -/
def ZpfCyc (J : ℝ) (w : ℕ → Bool → ℝ) (n : ℕ) : ℝ :=
  ∑ s : Fin (n + 1) → Bool, cfgWeightCyc J w s

/-- **§6.**  The cyclic partition function is the TRACE of the ordered product
of all `n+1` transfer matrices.  The wrap-around junction is exactly what turns
the boundary contraction of §2 into a trace. -/
theorem ZpfCyc_eq_trace (J : ℝ) (w : ℕ → Bool → ℝ) (n : ℕ) :
    ZpfCyc J w n = Matrix.trace (Mprod J n w * Mat J (w 0)) := by
  have h := sum_cfgTail_eq J n w (fun a b => w 0 a * bond J b a)
  rw [ZpfCyc]
  rw [show (∑ s : Fin (n + 1) → Bool, cfgWeightCyc J w s) =
      ∑ s : Fin (n + 1) → Bool,
        (fun a b => w 0 a * bond J b a) (s 0) (s (Fin.last n)) * cfgTail J w s from
    Finset.sum_congr rfl fun s _ => by rw [cfgWeightCyc]]
  rw [h, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Mat_apply]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- The trace form immediately gives the matrix-level cyclic symmetry. -/
theorem ZpfCyc_eq_trace_comm (J : ℝ) (w : ℕ → Bool → ℝ) (n : ℕ) :
    ZpfCyc J w n = Matrix.trace (Mat J (w 0) * Mprod J n w) := by
  rw [ZpfCyc_eq_trace, Matrix.trace_mul_comm]

/-- **CYCLIC INVARIANCE (§6).**  Rotating the site labelling of the ring by one
step — new site `k` is old site `k+1` for `k ≤ m`, and new site `m+1` is old
site `0` — leaves the cyclic partition function unchanged.  This is
`Matrix.trace_mul_comm` at the level of the transfer matrices. -/
theorem ZpfCyc_rotate (J : ℝ) (w w' : ℕ → Bool → ℝ) (m : ℕ)
    (h : ∀ k : ℕ, k ≤ m → w' k = w (k + 1)) (hlast : w' (m + 1) = w 0) :
    ZpfCyc J w' (m + 1) = ZpfCyc J w (m + 1) := by
  rw [ZpfCyc_eq_trace, ZpfCyc_eq_trace]
  have hw'0 : w' 0 = w 1 := h 0 (Nat.zero_le m)
  have hmid : Mprod J m w' = Mprod J m (shift w) := by
    refine Mprod_congr J m w' (shift w) fun k hk => ?_
    rw [shift_apply, h (k + 1) (by omega)]
  have hleft : Mprod J (m + 1) w' = Mprod J m (shift w) * Mat J (w 0) := by
    rw [Mprod_succ_right, hmid, hlast]
  have hright : Mprod J (m + 1) w = Mat J (w 1) * Mprod J m (shift w) := by
    rw [Mprod_succ]; rfl
  rw [hleft, hright, hw'0,
    show Mat J (w 1) * Mprod J m (shift w) * Mat J (w 0)
        = Mat J (w 1) * (Mprod J m (shift w) * Mat J (w 0)) from mul_assoc _ _ _]
  exact Matrix.trace_mul_comm _ _

/-! ## Axiom audit

House rule: an axiom claim that `lake env lean` does not re-run is not a
verified claim.  Every main theorem of this file is listed below.  All must
report only `[propext, Classical.choice, Quot.sound]`. -/

-- §1 definitions and their basic identities
#print axioms PrincipiaTractalis.TwoStateTransfer.bond_comm
#print axioms PrincipiaTractalis.TwoStateTransfer.bond_one
#print axioms PrincipiaTractalis.TwoStateTransfer.cfgWeight_eq
#print axioms PrincipiaTractalis.TwoStateTransfer.prod_bond_eq_pow
#print axioms PrincipiaTractalis.TwoStateTransfer.Mstep_shift
#print axioms PrincipiaTractalis.TwoStateTransfer.Mprod_congr
#print axioms PrincipiaTractalis.TwoStateTransfer.Mprod_succ_right
#print axioms PrincipiaTractalis.TwoStateTransfer.sum_cfg_succ
#print axioms PrincipiaTractalis.TwoStateTransfer.sum_cfg_one
#print axioms PrincipiaTractalis.TwoStateTransfer.cfgTail_one
#print axioms PrincipiaTractalis.TwoStateTransfer.cfgTail_succ

-- §2 main theorem
#print axioms PrincipiaTractalis.TwoStateTransfer.sum_cfgTail_eq
#print axioms PrincipiaTractalis.TwoStateTransfer.Zpf_eq_vecMul
#print axioms PrincipiaTractalis.TwoStateTransfer.Zpf_eq_dotProduct

-- §3 zero-cooperativity limit
#print axioms PrincipiaTractalis.TwoStateTransfer.Zpf_one_eq_prod

-- §4 the corollary and its sharpness witness
#print axioms PrincipiaTractalis.TwoStateTransfer.Zpf_one_perm
#print axioms PrincipiaTractalis.TwoStateTransfer.wABA_perm_wAAB
#print axioms PrincipiaTractalis.TwoStateTransfer.Zpf_two_closed
#print axioms PrincipiaTractalis.TwoStateTransfer.Zpf_one_AAB_eq_ABA
#print axioms PrincipiaTractalis.TwoStateTransfer.Zpf_two_AAB_ne_ABA
#print axioms PrincipiaTractalis.TwoStateTransfer.Zpf_perm_fails_off_one

-- §5 reversal invariance
#print axioms PrincipiaTractalis.TwoStateTransfer.Zpf_reverse

-- §6 cyclic chain
#print axioms PrincipiaTractalis.TwoStateTransfer.ZpfCyc_eq_trace
#print axioms PrincipiaTractalis.TwoStateTransfer.ZpfCyc_eq_trace_comm
#print axioms PrincipiaTractalis.TwoStateTransfer.ZpfCyc_rotate

end PrincipiaTractalis.TwoStateTransfer
