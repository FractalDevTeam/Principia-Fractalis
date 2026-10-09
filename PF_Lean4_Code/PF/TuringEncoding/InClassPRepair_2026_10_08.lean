/-
# PF.TuringEncoding.InClassPRepair_2026_10_08

**Additive repair of the `InClassP` specification defect.**

This file changes nothing. It (i) proves the defect in
`PrincipiaTractalis.TuringEncoding.InClassP`, (ii) proves that merely deleting
the offending clause does not repair it, and (iii) supplies a replacement
definition built on an actual model of computation, with a non-vacuity witness.

## (i) The defect, proved

`InClassP` carries the clause

    (∀ x c : BinString, M.accepts (x ++ c) ↔ M.accepts x)

Instantiating `x := []` and using `[] ++ c = c` gives
`∀ c, M.accepts c ↔ M.accepts []`, i.e. the decider's accept predicate is
constant. Composed with the decision clause `∀ x, x ∈ L ↔ M.accepts x`, every
language in `ClassP` is `∅` or `Set.univ`:

* `legacy_InClassP_trivial` — `InClassP L → L = ∅ ∨ L = univ`
* `legacy_ClassP_eq_pair` — `ClassP = {∅, univ}` (both inclusions)
* `Lfirst_mem_legacy_ClassNP` — a language that IS in `ClassNP` and is neither
  `∅` nor `univ`
* `legacy_ClassP_ne_ClassNP` — therefore `ClassP ≠ ClassNP` **unconditionally**,
  with no spectral hypothesis of any kind
* `legacy_PvsNP_Question_refuted` — `¬ PvsNP_Question`

The last two are the sharp form of the finding: on the current definitions the
`P ≠ NP` statement is not merely about a proxy, it is a one-line consequence of
the specification defect. Nothing in the fractal-operator route is doing any
work.

A second, smaller defect of the same specification is recorded here too:
`legacy_IsPolynomialBounded_forces_zero` shows `IsPolynomialBounded T → T 0 = 0`
(because `k > 0` makes the bound `c * 0 ^ k = 0` at `n = 0`), so every legacy
P-decider is additionally required to take zero steps on the empty input.

## (ii) Deleting the clause is not the repair

`InClassP_NoInvariance` is `InClassP` with the trailing clause removed.
`InClassP_NoInvariance_total` proves it holds of **every** language, so the
class becomes the full powerset. The reason is structural: `Machine` is
`⟨accepts : BinString → Prop, steps : BinString → ℕ⟩` with no transition
function, so `steps` is a free field and the time bound constrains nothing.
The trailing clause was load-bearing for `P_subset_NP` precisely because the
`Machine` interface cannot express "ignore the certificate".

## (iii) The repair

`TM` below is a deterministic two-tape machine with a genuine total transition
function `tr : Fin states → Sym → Sym → Fin states × Sym × Dir × Dir`, halting
states, a work tape and a read-only certificate tape, and step-indexed
semantics `run : ℕ → Cfg M → Cfg M` in which halting states are fixed points.
Time is the actual number of applications of `step`, not a free field.

* `InClassP_Step` — decided within `T (|x|)` steps by a machine whose program
  does not consult the certificate tape (`CertBlind`: a condition on the
  transition function, not on the language), `T` a monotone polynomially
  bounded time bound.
* `InClassNP_Step` — verified with a polynomially bounded certificate on the
  certificate tape.
* `firstOneTM` / `Lfirst` — an explicit 3-state machine deciding
  "the first symbol is 1" in one step; `Lfirst_mem_ClassP_Step` with
  `Lfirst_ne_empty`, `Lfirst_ne_univ` is the non-vacuity witness.
* `ClassP_Step_subset_ClassNP_Step` — `P ⊆ NP` rebuilt without any
  context-invariance clause, via `run_certBlind` plus the fixed-point lemma
  `run_of_le_halted`.
* `legacy_ClassP_subset_ClassP_Step`, `ClassP_Step_not_subset_legacy_ClassP` —
  the repaired class strictly contains the defective one.

## What this still does NOT capture, relative to the Clay statement

1. **Alphabet and tape count are fixed.** One work tape, one read-only
   certificate tape, tape alphabet `{blank, 0, 1}`. This is a real model but
   not shown equivalent to any standard one; no robustness/simulation theorem
   is proved here.
2. **No proof that `ClassP_Step` is a proper subclass of all languages.** The
   class is non-collapsing and resource-sensitive by construction, but the
   diagonal/counting argument showing some language is outside it is not
   formalized. So "P is a nontrivial class" is exhibited, not proved in the
   strong sense.
3. **No reductions, no completeness, no Cook–Levin.** `ClassNP_Step` has no
   complete problem here, so `ClassP_Step ≠ ClassNP_Step` is not reduced to
   any concrete language.
4. **`PvsNP_Step` is left open, deliberately.** No theorem in this file bears
   on it. That is the contrast with (i): the defective question was decidable
   in one line; the repaired one is not touched.
5. **No connection to the fractal operator route.** Nothing here links
   `ClassP_Step` to `H_α`, `α_P = √2`, `α_NP = φ + 1/4`, or
   `PolylogEigenvalueConjecture`. Every PF theorem currently phrased over
   `ClassP` / `ClassNP` would have to be re-derived over these definitions,
   and `legacy_ClassP_ne_ClassNP` shows the old ones carried no complexity
   content to re-derive.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.

Author: Pablo Cohen + Claude Opus 5. 2026-10-08.
-/

import PF.TuringEncoding.Complexity
import PF.P_NP_Complete_Proof

namespace PrincipiaTractalis.TuringEncoding.Repair20261008

/-! ## Part 1 — the defect in the current `InClassP`, proved -/

section LegacyDefect

/-- The trailing-input clause of `InClassP` forces the decider's accept
    predicate to be constant: take `x := []` and use `[] ++ c = c`. -/
theorem legacy_accepts_const {Γ Λ σ : Type} (M : Machine Γ Λ σ)
    (hinv : ∀ x c : BinString, M.accepts (x ++ c) ↔ M.accepts x) :
    ∀ s : BinString, M.accepts s ↔ M.accepts [] := by
  intro s
  simpa using hinv [] s

/-- **The collapse.** Every language satisfying `InClassP` is `∅` or `univ`. -/
theorem legacy_InClassP_trivial {L : Language} (h : InClassP L) :
    L = (∅ : Language) ∨ L = (Set.univ : Language) := by
  obtain ⟨Γ, Λ, σ, M, T, _hpoly, hdec, _htime, hinv⟩ := h
  have hconst := legacy_accepts_const M hinv
  by_cases hM : M.accepts []
  · right
    ext x
    constructor
    · intro _; trivial
    · intro _; exact (hdec x).mpr ((hconst x).mpr hM)
  · left
    ext x
    constructor
    · intro hx; exact absurd ((hconst x).mp ((hdec x).mp hx)) hM
    · intro hx; simp at hx

/-- `∅` really is in the defective `ClassP`. -/
theorem legacy_empty_mem_ClassP : (∅ : Language) ∈ ClassP := by
  refine ⟨Unit, Unit, Unit, ⟨fun _ => False, fun _ => 0⟩, fun n => n,
    ⟨1, 1, Nat.one_pos, Nat.one_pos, fun n => by simp⟩, ?_, ?_, ?_⟩
  · intro x; simp
  · intro x; simp [turingTimeComplexity]
  · intro x c; simp

/-- `univ` really is in the defective `ClassP`. -/
theorem legacy_univ_mem_ClassP : (Set.univ : Language) ∈ ClassP := by
  refine ⟨Unit, Unit, Unit, ⟨fun _ => True, fun _ => 0⟩, fun n => n,
    ⟨1, 1, Nat.one_pos, Nat.one_pos, fun n => by simp⟩, ?_, ?_, ?_⟩
  · intro x; simp
  · intro x; simp [turingTimeComplexity]
  · intro x c; simp

/-- **`ClassP` is exactly the two-element set `{∅, univ}`.** -/
theorem legacy_ClassP_eq_pair :
    ClassP = {(∅ : Language), (Set.univ : Language)} := by
  ext L
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hL
    exact legacy_InClassP_trivial hL
  · intro hL
    rcases hL with h | h
    · rw [h]; exact legacy_empty_mem_ClassP
    · rw [h]; exact legacy_univ_mem_ClassP

/-- A second defect of the same specification: `IsPolynomialBounded` requires
    `k > 0`, so the bound at `n = 0` reads `T 0 ≤ c * 0 ^ k = 0`. Every legacy
    P-decider must therefore take zero steps on the empty input. -/
theorem legacy_IsPolynomialBounded_forces_zero {T : ℕ → ℕ}
    (h : IsPolynomialBounded T) : T 0 = 0 := by
  obtain ⟨c, k, _hc, hk, hT⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h0 := hT 0
  simp [pow_succ] at h0
  exact h0

end LegacyDefect

/-! ## Part 2 — deleting the clause is not the repair -/

/-- `InClassP` with the trailing-input clause deleted. -/
def InClassP_NoInvariance (L : Language) : Prop :=
  ∃ (Γ Λ σ : Type) (M : Machine Γ Λ σ) (T : ℕ → ℕ),
    IsPolynomialBounded T ∧
    (∀ x : BinString, x ∈ L ↔ M.accepts x) ∧
    (∀ x : BinString, turingTimeComplexity Γ Λ σ M x ≤ T (binLength x))

/-- **Deleting the clause overshoots: the class becomes the full powerset.**
    `Machine` has no transition function, so `steps` is a free field and the
    polynomial bound constrains nothing. -/
theorem InClassP_NoInvariance_total (L : Language) : InClassP_NoInvariance L := by
  refine ⟨Unit, Unit, Unit, ⟨fun x => x ∈ L, fun _ => 0⟩, fun n => n,
    ⟨1, 1, Nat.one_pos, Nat.one_pos, fun n => by simp⟩, fun _ => Iff.rfl, ?_⟩
  intro x; simp [turingTimeComplexity]

theorem InClassP_NoInvariance_class_eq_univ :
    {L : Language | InClassP_NoInvariance L} = Set.univ := by
  ext L
  constructor
  · intro _; trivial
  · intro _; exact InClassP_NoInvariance_total L

/-! ## Part 3 — a genuine machine model -/

/-- Tape alphabet: the two input symbols plus a blank. -/
inductive Sym where
  | blank : Sym
  | zero : Sym
  | one : Sym
  deriving DecidableEq

/-- Head movement. -/
inductive Dir where
  | left : Dir
  | right : Dir
  | stay : Dir
  deriving DecidableEq

/-- Input symbols embed into the tape alphabet. -/
def symOf : BinSymbol → Sym
  | BinSymbol.zero => Sym.zero
  | BinSymbol.one => Sym.one

/-- A two-way infinite tape as a zipper: `left` nearest-cell-first, `cur` under
    the head, `right` the rest. Cells outside the written window read `blank`. -/
structure Tape where
  left : List Sym
  cur : Sym
  right : List Sym

namespace Tape

/-- Overwrite the cell under the head. -/
def write (t : Tape) (s : Sym) : Tape := { t with cur := s }

/-- Move the head one cell left, materialising a blank at the boundary. -/
def moveLeft (t : Tape) : Tape :=
  match t.left with
  | [] => ⟨[], Sym.blank, t.cur :: t.right⟩
  | a :: l => ⟨l, a, t.cur :: t.right⟩

/-- Move the head one cell right, materialising a blank at the boundary. -/
def moveRight (t : Tape) : Tape :=
  match t.right with
  | [] => ⟨t.cur :: t.left, Sym.blank, []⟩
  | b :: r => ⟨t.cur :: t.left, b, r⟩

/-- Head movement in a given direction. -/
def move (t : Tape) : Dir → Tape
  | Dir.left => t.moveLeft
  | Dir.right => t.moveRight
  | Dir.stay => t

/-- The tape holding `x`, head on its first cell (blank if `x` is empty). -/
def ofInput : BinString → Tape
  | [] => ⟨[], Sym.blank, []⟩
  | b :: t => ⟨[], symOf b, t.map symOf⟩

end Tape

/-- A deterministic machine with a **total transition function**, halting
    states, one read-write work tape and one read-only certificate tape.
    `tr q a b = (q', s, d, e)`: in state `q` reading `a` on the work tape and
    `b` on the certificate tape, move to `q'`, write `s` on the work tape, move
    the work head by `d` and the certificate head by `e`. -/
structure TM where
  /-- Number of states; `start : Fin states` forces `states > 0`. -/
  states : ℕ
  /-- Initial state. -/
  start : Fin states
  /-- Halting states. -/
  halt : Fin states → Bool
  /-- Which states accept. -/
  acc : Fin states → Bool
  /-- The transition function. -/
  tr : Fin states → Sym → Sym → Fin states × Sym × Dir × Dir

/-- A configuration: state, work tape, certificate tape. -/
structure Cfg (M : TM) where
  /-- Current state. -/
  q : Fin M.states
  /-- Work tape. -/
  work : Tape
  /-- Certificate tape (read-only: never written, only scanned). -/
  cert : Tape

namespace TM

/-- A configuration is halted when its state is a halting state. -/
def Halted (M : TM) (c : Cfg M) : Prop := M.halt c.q = true

/-- One application of the transition function (ignoring halting). -/
def next (M : TM) (c : Cfg M) : Cfg M :=
  ⟨(M.tr c.q c.work.cur c.cert.cur).1,
   (c.work.write (M.tr c.q c.work.cur c.cert.cur).2.1).move
     (M.tr c.q c.work.cur c.cert.cur).2.2.1,
   c.cert.move (M.tr c.q c.work.cur c.cert.cur).2.2.2⟩

/-- One step: halting configurations are fixed points. -/
def step (M : TM) (c : Cfg M) : Cfg M :=
  if M.halt c.q = true then c else M.next c

/-- `run M t c` is `c` after exactly `t` steps. -/
def run (M : TM) : ℕ → Cfg M → Cfg M
  | 0, c => c
  | n + 1, c => M.step (M.run n c)

/-- Initial configuration on input `x` with certificate `cert`. -/
def initCfg (M : TM) (x cert : BinString) : Cfg M :=
  ⟨M.start, Tape.ofInput x, Tape.ofInput cert⟩

/-- The machine's verdict after `t` steps. -/
def verdict (M : TM) (t : ℕ) (x cert : BinString) : Bool :=
  M.acc (M.run t (M.initCfg x cert)).q

/-- The machine has halted after `t` steps. -/
def haltedAfter (M : TM) (t : ℕ) (x cert : BinString) : Prop :=
  M.Halted (M.run t (M.initCfg x cert))

/-- The program never consults the certificate tape — a condition on the
    transition function, not on the accepted language. Such a machine is
    literally a one-tape machine. -/
def CertBlind (M : TM) : Prop := ∀ q a b b', M.tr q a b = M.tr q a b'

/-! ### Basic semantics -/

theorem step_of_halted {M : TM} {c : Cfg M} (h : M.Halted c) : M.step c = c := by
  have h' : M.halt c.q = true := h
  simp [step, h']

theorem run_succ (M : TM) (t : ℕ) (c : Cfg M) :
    M.run (t + 1) c = M.step (M.run t c) := rfl

/-- Once halted, always halted at the same configuration. -/
theorem run_eq_of_halted {M : TM} {c : Cfg M} {t : ℕ}
    (h : M.Halted (M.run t c)) (d : ℕ) : M.run (t + d) c = M.run t c := by
  induction d with
  | zero => rfl
  | succ d ih =>
      have e : M.run (t + (d + 1)) c = M.step (M.run (t + d) c) := rfl
      rw [e, ih, step_of_halted h]

theorem run_of_le_halted {M : TM} {c : Cfg M} {t t' : ℕ} (hle : t ≤ t')
    (h : M.Halted (M.run t c)) : M.run t' c = M.run t c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact run_eq_of_halted h d

/-- A certificate-blind program's next state and work tape do not depend on the
    certificate tape. -/
theorem next_certBlind {M : TM} (hb : M.CertBlind) {c₁ c₂ : Cfg M}
    (hq : c₁.q = c₂.q) (hw : c₁.work = c₂.work) :
    (M.next c₁).q = (M.next c₂).q ∧ (M.next c₁).work = (M.next c₂).work := by
  have key : M.tr c₁.q c₁.work.cur c₁.cert.cur
           = M.tr c₂.q c₂.work.cur c₂.cert.cur := by
    rw [hq, hw]; exact hb _ _ _ _
  refine ⟨?_, ?_⟩
  · simp only [next]
    rw [key]
  · simp only [next]
    rw [key, hw]

/-- A certificate-blind program's whole run, projected to state and work tape,
    does not depend on the certificate tape. -/
theorem run_certBlind {M : TM} (hb : M.CertBlind) (t : ℕ) {c₁ c₂ : Cfg M}
    (hq : c₁.q = c₂.q) (hw : c₁.work = c₂.work) :
    (M.run t c₁).q = (M.run t c₂).q ∧ (M.run t c₁).work = (M.run t c₂).work := by
  induction t with
  | zero => exact ⟨hq, hw⟩
  | succ t ih =>
      obtain ⟨hq', hw'⟩ := ih
      by_cases hh : M.halt (M.run t c₁).q = true
      · have hh2 : M.halt (M.run t c₂).q = true := by rw [← hq']; exact hh
        rw [run_succ, run_succ, step_of_halted hh, step_of_halted hh2]
        exact ⟨hq', hw'⟩
      · have hh2 : ¬ (M.halt (M.run t c₂).q = true) := by rw [← hq']; exact hh
        rw [run_succ, run_succ]
        have e1 : M.step (M.run t c₁) = M.next (M.run t c₁) := by simp [step, hh]
        have e2 : M.step (M.run t c₂) = M.next (M.run t c₂) := by simp [step, hh2]
        rw [e1, e2]
        exact next_certBlind hb hq' hw'

end TM

/-! ### Resource bounds -/

/-- Polynomially bounded, stated so that it does not force `f 0 = 0`. -/
def IsPolyBound (f : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, f n ≤ c * (n + 1) ^ k

/-- A time bound: monotone and polynomially bounded. -/
def IsTimeBound (T : ℕ → ℕ) : Prop := Monotone T ∧ IsPolyBound T

/-! ### The repaired classes -/

/-- `M` decides `L` within `T (|x|)` steps, certificate tape empty. -/
def DecidesInTime (M : TM) (L : Language) (T : ℕ → ℕ) : Prop :=
  ∀ x : BinString,
    M.haltedAfter (T (binLength x)) x [] ∧
    (x ∈ L ↔ M.verdict (T (binLength x)) x [] = true)

/-- **The repaired P.** Decided in polynomially many actual steps by a machine
    whose program does not consult the certificate tape. -/
def InClassP_Step (L : Language) : Prop :=
  ∃ (M : TM) (T : ℕ → ℕ), IsTimeBound T ∧ M.CertBlind ∧ DecidesInTime M L T

/-- The repaired class P. -/
def ClassP_Step : Set Language := {L | InClassP_Step L}

/-- `V` verifies `L` with certificates of length at most `p (|x|)`. -/
def VerifiesInTime (V : TM) (L : Language) (T p : ℕ → ℕ) : Prop :=
  (∀ x cert : BinString, V.haltedAfter (T (binLength x + binLength cert)) x cert) ∧
  (∀ x : BinString, x ∈ L ↔ ∃ cert : BinString,
      binLength cert ≤ p (binLength x) ∧
      V.verdict (T (binLength x + binLength cert)) x cert = true)

/-- **The repaired NP.** -/
def InClassNP_Step (L : Language) : Prop :=
  ∃ (V : TM) (T p : ℕ → ℕ), IsTimeBound T ∧ IsPolyBound p ∧ VerifiesInTime V L T p

/-- The repaired class NP. -/
def ClassNP_Step : Set Language := {L | InClassNP_Step L}

/-- The repaired question. **No theorem in this file bears on it.** -/
def PvsNP_Step : Prop := ClassP_Step = ClassNP_Step

/-! ## Part 4 — the non-vacuity witness -/

/-- The language of strings whose first symbol is `1`. -/
def Lfirst : Language := {s : BinString | s.head? = some BinSymbol.one}

/-- Three states: `0` running, `1` halt-accept, `2` halt-reject. Reads the cell
    under the head once and halts. Ignores the certificate tape. -/
def firstOneTM : TM where
  states := 3
  start := ⟨0, by omega⟩
  halt := fun q => !(decide (q.val = 0))
  acc := fun q => decide (q.val = 1)
  tr := fun _ a _ =>
    (if a = Sym.one then (⟨1, by omega⟩ : Fin 3) else (⟨2, by omega⟩ : Fin 3),
     a, Dir.stay, Dir.stay)

theorem firstOneTM_certBlind : firstOneTM.CertBlind := by
  intro q a b b'; rfl

theorem firstOneTM_timeBound : IsTimeBound (fun _ : ℕ => 1) :=
  ⟨monotone_const, ⟨1, 0, fun n => by simp⟩⟩

theorem firstOneTM_halted (x : BinString) : firstOneTM.haltedAfter 1 x [] := by
  cases x with
  | nil => rfl
  | cons b t => cases b <;> rfl

theorem firstOneTM_verdict_iff (x : BinString) :
    x ∈ Lfirst ↔ firstOneTM.verdict 1 x [] = true := by
  cases x with
  | nil =>
      have h : firstOneTM.verdict 1 ([] : BinString) [] = false := rfl
      simp [Lfirst, Set.mem_setOf_eq, h]
  | cons b t =>
      cases b with
      | zero =>
          have h : firstOneTM.verdict 1 (BinSymbol.zero :: t) [] = false := rfl
          simp [Lfirst, Set.mem_setOf_eq, h]
      | one =>
          have h : firstOneTM.verdict 1 (BinSymbol.one :: t) [] = true := rfl
          simp [Lfirst, Set.mem_setOf_eq, h]

theorem firstOneTM_decides : DecidesInTime firstOneTM Lfirst (fun _ => 1) :=
  fun x => ⟨firstOneTM_halted x, firstOneTM_verdict_iff x⟩

/-- **The non-vacuity witness is in the repaired P.** -/
theorem Lfirst_mem_ClassP_Step : Lfirst ∈ ClassP_Step :=
  ⟨firstOneTM, fun _ => 1, firstOneTM_timeBound, firstOneTM_certBlind,
    firstOneTM_decides⟩

theorem Lfirst_ne_empty : Lfirst ≠ (∅ : Language) := by
  intro h
  have hm : ([BinSymbol.one] : BinString) ∈ Lfirst := by simp [Lfirst]
  rw [h] at hm
  simp at hm

theorem Lfirst_ne_univ : Lfirst ≠ (Set.univ : Language) := by
  intro h
  have hm : ([] : BinString) ∉ Lfirst := by simp [Lfirst]
  rw [h] at hm
  exact hm (Set.mem_univ _)

/-- **The repaired class does not collapse to `{∅, univ}`.** -/
theorem ClassP_Step_noncollapse :
    ∃ L : Language, L ∈ ClassP_Step ∧ L ≠ (∅ : Language) ∧
      L ≠ (Set.univ : Language) :=
  ⟨Lfirst, Lfirst_mem_ClassP_Step, Lfirst_ne_empty, Lfirst_ne_univ⟩

/-! ## Part 5 — the defective class is trivially separated; the repaired one is not -/

/-- The witness language is in the **defective** `ClassNP`: its verifier reads
    the first symbol of `x ++ c`, which is the first symbol of `x`. -/
theorem Lfirst_mem_legacy_ClassNP : Lfirst ∈ ClassNP := by
  refine ⟨Unit, Unit, Unit,
    ⟨fun s => s.head? = some BinSymbol.one, fun _ => 0⟩, fun n => n,
    ⟨1, 1, Nat.one_pos, Nat.one_pos, fun n => by simp⟩, ?_, ?_⟩
  · intro x c; simp [turingTimeComplexity]
  · intro x
    constructor
    · intro hx
      refine ⟨[], by simp [binLength], ?_⟩
      simpa [Lfirst, Set.mem_setOf_eq] using hx
    · rintro ⟨c, hc, hacc⟩
      cases x with
      | nil =>
          cases c with
          | nil => simp at hacc
          | cons b r => simp [binLength] at hc
      | cons b t =>
          simpa [Lfirst, Set.mem_setOf_eq] using hacc

theorem Lfirst_not_mem_legacy_ClassP : Lfirst ∉ ClassP := by
  intro h
  rcases legacy_InClassP_trivial h with hE | hU
  · exact Lfirst_ne_empty hE
  · exact Lfirst_ne_univ hU

/-- **The defective `ClassP ≠ ClassNP` is unconditional.** No spectral
    hypothesis, no `PolylogEigenvalueConjecture`, no fractal operator: the
    separation follows from the specification defect alone. -/
theorem legacy_ClassP_ne_ClassNP : ClassP ≠ ClassNP := by
  intro h
  have h1 : Lfirst ∈ ClassNP := Lfirst_mem_legacy_ClassNP
  rw [← h] at h1
  exact Lfirst_not_mem_legacy_ClassP h1

/-- Equivalently: the framework's `PvsNP_Question` is refutable outright. -/
theorem legacy_PvsNP_Question_refuted : ¬ PvsNP_Question :=
  legacy_ClassP_ne_ClassNP

/-- **The framework's own target proposition is provable with no hypothesis.**
    `PrincipiaTractalis.P_neq_NP_def` is defined at `PF/P_NP_Complete_Proof.lean`
    lines 79–83 as `¬ (∀ L, InClassNP L → InClassP L)`. It is discharged here
    outright. Consequently every PF implication of the form
    `⟨hypothesis⟩ → P_neq_NP_def` — including
    `PolylogEigenvalueConjecture → P_neq_NP_def` and the empirical routes in
    `PF/EmpiricalPostulateDischarge.lean` — has a conclusion that is already a
    theorem, so none of them transmits any complexity-theoretic content. -/
theorem legacy_P_neq_NP_def_unconditional : PrincipiaTractalis.P_neq_NP_def := by
  unfold PrincipiaTractalis.P_neq_NP_def PrincipiaTractalis.P_equals_NP_def
  intro h
  exact Lfirst_not_mem_legacy_ClassP (h Lfirst Lfirst_mem_legacy_ClassNP)

/-! ## Part 6 — the repaired class strictly contains the defective one -/

/-- One state, halts immediately, rejects. -/
def rejectTM : TM where
  states := 1
  start := ⟨0, by omega⟩
  halt := fun _ => true
  acc := fun _ => false
  tr := fun q a _ => (q, a, Dir.stay, Dir.stay)

/-- One state, halts immediately, accepts. -/
def acceptTM : TM where
  states := 1
  start := ⟨0, by omega⟩
  halt := fun _ => true
  acc := fun _ => true
  tr := fun q a _ => (q, a, Dir.stay, Dir.stay)

theorem rejectTM_certBlind : rejectTM.CertBlind := by
  intro q a b b'; rfl

theorem acceptTM_certBlind : acceptTM.CertBlind := by
  intro q a b b'; rfl

theorem zeroTimeBound : IsTimeBound (fun _ : ℕ => 0) :=
  ⟨monotone_const, ⟨0, 0, fun n => by simp⟩⟩

theorem empty_mem_ClassP_Step : (∅ : Language) ∈ ClassP_Step := by
  refine ⟨rejectTM, fun _ => 0, zeroTimeBound, rejectTM_certBlind, ?_⟩
  intro x
  refine ⟨rfl, ?_⟩
  have h : rejectTM.verdict 0 x [] = false := rfl
  simp [h]

theorem univ_mem_ClassP_Step : (Set.univ : Language) ∈ ClassP_Step := by
  refine ⟨acceptTM, fun _ => 0, zeroTimeBound, acceptTM_certBlind, ?_⟩
  intro x
  refine ⟨rfl, ?_⟩
  have h : acceptTM.verdict 0 x [] = true := rfl
  simp [h]

theorem legacy_ClassP_subset_ClassP_Step : ClassP ⊆ ClassP_Step := by
  intro L hL
  rcases legacy_InClassP_trivial hL with h | h
  · rw [h]; exact empty_mem_ClassP_Step
  · rw [h]; exact univ_mem_ClassP_Step

theorem ClassP_Step_not_subset_legacy_ClassP : ¬ (ClassP_Step ⊆ ClassP) := by
  intro h
  exact Lfirst_not_mem_legacy_ClassP (h Lfirst_mem_ClassP_Step)

theorem legacy_ClassP_ne_ClassP_Step : ClassP ≠ ClassP_Step := by
  intro h
  exact ClassP_Step_not_subset_legacy_ClassP (fun L hL => by rw [h]; exact hL)

/-! ## Part 7 — `P ⊆ NP` rebuilt, with no context-invariance clause -/

theorem ClassP_Step_subset_ClassNP_Step : ClassP_Step ⊆ ClassNP_Step := by
  intro L hL
  obtain ⟨M, T, hT, hb, hdec⟩ := hL
  -- Certificate-blindness transports every run from `cert` to `[]`.
  have hcb : ∀ (t : ℕ) (x cert : BinString),
      (M.run t (M.initCfg x cert)).q = (M.run t (M.initCfg x [])).q := by
    intro t x cert
    exact (TM.run_certBlind hb t (c₁ := M.initCfg x cert)
      (c₂ := M.initCfg x []) rfl rfl).1
  -- Halting on `(x, cert)` at the larger time bound.
  have hhalt : ∀ x cert : BinString,
      M.haltedAfter (T (binLength x + binLength cert)) x cert := by
    intro x cert
    have h0 : M.Halted (M.run (T (binLength x)) (M.initCfg x cert)) := by
      show M.halt (M.run (T (binLength x)) (M.initCfg x cert)).q = true
      rw [hcb (T (binLength x)) x cert]
      exact (hdec x).1
    have hle : T (binLength x) ≤ T (binLength x + binLength cert) :=
      hT.1 (Nat.le_add_right _ _)
    show M.halt (M.run (T (binLength x + binLength cert)) (M.initCfg x cert)).q = true
    rw [TM.run_of_le_halted hle h0]
    exact h0
  refine ⟨M, T, fun n => n, hT, ⟨1, 1, fun n => by simp only [one_mul, pow_one]; omega⟩,
    hhalt, ?_⟩
  intro x
  constructor
  · intro hx
    refine ⟨[], Nat.zero_le _, ?_⟩
    have e : binLength x + binLength ([] : BinString) = binLength x := by
      simp [binLength]
    rw [e]
    exact (hdec x).2.mp hx
  · rintro ⟨cert, _, hv⟩
    refine (hdec x).2.mpr ?_
    have h0 : M.Halted (M.run (T (binLength x)) (M.initCfg x cert)) := by
      show M.halt (M.run (T (binLength x)) (M.initCfg x cert)).q = true
      rw [hcb (T (binLength x)) x cert]
      exact (hdec x).1
    have hle : T (binLength x) ≤ T (binLength x + binLength cert) :=
      hT.1 (Nat.le_add_right _ _)
    have hv' : M.acc (M.run (T (binLength x)) (M.initCfg x cert)).q = true := by
      have := hv
      unfold TM.verdict at this
      rw [TM.run_of_le_halted hle h0] at this
      exact this
    show M.acc (M.run (T (binLength x)) (M.initCfg x [])).q = true
    rw [← hcb (T (binLength x)) x cert]
    exact hv'

/-- The witness language is in the repaired NP as well. -/
theorem Lfirst_mem_ClassNP_Step : Lfirst ∈ ClassNP_Step :=
  ClassP_Step_subset_ClassNP_Step Lfirst_mem_ClassP_Step

end PrincipiaTractalis.TuringEncoding.Repair20261008
