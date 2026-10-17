# P-vs-NP step-bounded scoping: NON-CIRCULAR, already half-built, and the only P/NP work in the repo independent of the α-web. Buildable entry point — but it makes the question *statable*, not answerable.

**Date:** 2026-10-17 (Legion, audit on Acer). Scoping. No Lean.
Labels FACT / MEASURED / JUDGEMENT / OPEN.

**VERDICT: BUILDABLE ENTRY POINT.** The step-bounded approach is not circular,
does not touch the α-web, and is **already built** — `InClassPRepair_2026_10_08.lean`,
657 lines, no `sorry`, no `axiom`, no `Prop := True`. The brief says it was
"mentioned but never built"; it was built, by Pablo Cohen + Claude Opus 5 on
2026-10-08, and then left unused by everything downstream.

**But state the ceiling with it:** this approach does **not** attack P vs NP. It
makes the question *statable on honest definitions*, and deliberately leaves it
open. That is the Navier–Stokes pattern — faithful statement reachable, proof
untouched — and it is the correct posture, not a shortfall.

---

## 1. What the proposal was, and who wrote it. FACT

`PF/TuringEncoding/InClassPRepair_2026_10_08.lean` — "**Additive repair of the
`InClassP` specification defect**", Pablo Cohen + Claude Opus 5, 2026-10-08.
Its own three-part structure:

> "(i) proves the defect in `PrincipiaTractalis.TuringEncoding.InClassP`,
> (ii) proves that merely deleting the offending clause does not repair it, and
> (iii) supplies a replacement definition built on an actual model of
> computation, with a non-vacuity witness."

**It also contains the sharpest statement of the P/NP defect anywhere in the
corpus, and it predates my `336441d1` audit by eight days.** The legacy
`InClassP` carries the clause `(∀ x c, M.accepts (x ++ c) ↔ M.accepts x)`;
instantiating `x := []` forces `accepts` constant, whence:

* `legacy_InClassP_trivial` — `InClassP L → L = ∅ ∨ L = univ`
* `legacy_ClassP_eq_pair` — `ClassP = {∅, univ}`, both inclusions
* `legacy_ClassP_ne_ClassNP` — `ClassP ≠ ClassNP` **unconditionally, with no
  spectral hypothesis of any kind**
* `legacy_PvsNP_Question_refuted` — `¬ PvsNP_Question`

In the author's own words:

> "the `P ≠ NP` statement is not merely about a proxy, it is a one-line
> consequence of the specification defect. **Nothing in the fractal-operator
> route is doing any work.**"

**JUDGEMENT: that sentence is the whole P/NP axis in one line, it was written on
2026-10-08, and the spectral-gap stack was still being extended afterwards.**
The finding was made and not propagated — which is why `336441d1` had to find it
again.

A second legacy defect is recorded too: `legacy_IsPolynomialBounded_forces_zero`
— `IsPolynomialBounded T → T 0 = 0`, because `c * 0^k = 0` for `k > 0`, so every
legacy P-decider was additionally required to take **zero steps on empty input**.

## 2. Circularity check — NOT circular, and structurally so. FACT

**The parked bridge was circular** because its hypothesis was *provably
equivalent* to its conclusion:

```
alpha_realization_canonical_pair_iff_classes_distinct :
  (∃ f, f ClassP = √2 ∧ f ClassNP = phi + 1/4)  ↔  ClassP ≠ ClassNP
```

**The step-bounded approach has no hypothesis and no bridge.** It is a
*definitional* repair: it replaces the carriers and restates the question.

```lean
def PvsNP_Step : Prop := ClassP_Step = ClassNP_Step
```

with the file's own comment: "**No theorem in this file bears on it.**" And its
§4 of self-declared scope:

> "`PvsNP_Step` is left open, **deliberately**. No theorem in this file bears on
> it. That is the contrast with (i): the defective question was decidable in one
> line; the repaired one is not touched."

**So there is no circle to name.** The honest characterisation: the parked bridge
assumed its conclusion; the step-bounded approach assumes nothing and proves
nothing about the question. Those are different failure-to-progress modes, and
only the first is a defect. **The second is what an honest formalisation of an
open problem looks like.**

**The non-circularity is checkable structurally, not just by inspection:**
`InClassP_Step` and `InClassNP_Step` quantify only over `TM`, `ℕ → ℕ` time/length
bounds, and `BinString` — no real-valued parameter appears anywhere in either
definition, so no α-realisation can be hiding in them. §4 below confirms this is
deliberate.

## 3. What "step-bounded" means formally. FACT

**A genuine machine model, with time as a derived quantity rather than a field.**

```lean
structure TM where
  states : ℕ
  start  : Fin states          -- forces states > 0
  halt   : Fin states → Bool
  acc    : Fin states → Bool
  tr     : Fin states → Sym → Sym → Fin states × Sym × Dir × Dir
```

Two tapes (work + read-only certificate), alphabet `{blank, 0, 1}`,
configurations `Cfg M = ⟨q, work, cert⟩`, and **step-indexed semantics**
`run : ℕ → Cfg M → Cfg M` in which halting states are **fixed points** —
`step_of_halted`, `run_eq_of_halted`, `run_of_le_halted`. Time is the actual
number of `step` applications.

**Why the legacy design could not work, in the file's own diagnosis:**

> "`Machine` is `⟨accepts : BinString → Prop, steps : BinString → ℕ⟩` with no
> transition function, so `steps` is a **free field** and the time bound
> constrains nothing. The trailing clause was load-bearing for `P_subset_NP`
> precisely because the `Machine` interface cannot express 'ignore the
> certificate'."

**The three definitional fixes:**

| | definition | why it is right |
|---|---|---|
| `CertBlind M` | `∀ q a b b', M.tr q a b = M.tr q a b'` | a condition on the **program**, not the language — the honest way to say "ignores the certificate" |
| `IsPolyBound f` | `∃ c k, ∀ n, f n ≤ c * (n+1)^k` | the `(n+1)^k` **fixes** the legacy `T 0 = 0` bug |
| `IsTimeBound T` | `Monotone T ∧ IsPolyBound T` | monotonicity is used, not assumed away |

**The classes:**

```lean
def InClassP_Step  L := ∃ M T,   IsTimeBound T ∧ M.CertBlind ∧ DecidesInTime M L T
def InClassNP_Step L := ∃ V T p, IsTimeBound T ∧ IsPolyBound p ∧ VerifiesInTime V L T p

def VerifiesInTime V L T p :=
  (∀ x cert, V.haltedAfter (T (|x| + |cert|)) x cert) ∧
  (∀ x, x ∈ L ↔ ∃ cert, |cert| ≤ p |x| ∧ V.verdict (T (|x| + |cert|)) x cert = true)
```

**`VerifiesInTime` is textbook NP** — halting within a polynomial bound in
`|x|+|cert|`, and membership iff a short accepting certificate exists. I checked
this against Cook's 1971 formulation; it is faithful.

## 4. The α-web: bypassed entirely, and deliberately. FACT

The file's own §5 of "what this still does NOT capture":

> "**No connection to the fractal operator route.** Nothing here links
> `ClassP_Step` to `H_α`, `α_P = √2`, `α_NP = φ + 1/4`, or
> `PolylogEigenvalueConjecture`. Every PF theorem currently phrased over
> `ClassP` / `ClassNP` would have to be re-derived over these definitions, and
> `legacy_ClassP_ne_ClassNP` shows the old ones **carried no complexity content
> to re-derive**."

**That is the answer, and it is the approach's chief virtue, not a gap.** The
α-web is under-determined (a second positive solution satisfies all eleven
invariants) and its P/NP bridge is circular. **The step-bounded route is the only
P/NP work in the repo that is independent of both.** Its `α_P = √2` /
`α_NP = φ+¼` values — which the `336441d1` audit traced to an Observation
(empirical, 10⁻¹⁰), two Conjectures and a Heuristic — simply never enter.

## 5. The first concrete theorems — already built, and kernel-honest. MEASURED

No `sorry` (the single grep hit is line 97, the header *asserting* there is
none), no `axiom`, no `native_decide`, no `Prop := True`.

| theorem | content |
|---|---|
| `ClassP_Step_subset_ClassNP_Step` | **`P ⊆ NP` rebuilt with no invariance clause**, via `run_certBlind` + `run_of_le_halted` |
| `Lfirst_mem_ClassP_Step` | non-vacuity: explicit 3-state `firstOneTM` decides "first symbol is 1" in one step |
| `Lfirst_ne_empty`, `Lfirst_ne_univ` | the witness language is neither trivial case |
| `legacy_ClassP_subset_ClassP_Step` | the repair is **additive** |
| `ClassP_Step_not_subset_legacy_ClassP` | and **strict** — `ClassP ≠ ClassP_Step` |

So the useful question is not "what is the first theorem" but **"what is the
next one"**. The file lists its own five gaps; ranked by reachability:

### The next theorem, recommended: `ClassP_Step` is countable, hence a proper subclass

This closes the author's own gap (2) — *"No proof that `ClassP_Step` is a proper
subclass of all languages… So 'P is a nontrivial class' is **exhibited, not
proved** in the strong sense."*

**Why it goes through — JUDGEMENT, with the two load-bearing steps checked:**

1. **TMs are countable.** For fixed `states = n`, each of `start`, `halt`, `acc`,
   `tr` ranges over functions between **finite** types, so there are finitely
   many `TM`s with `states = n`; a countable union over `n : ℕ` is countable.
2. **The language is determined by `M` alone.** Because halting states are fixed
   points (`run_of_le_halted`, already proved), the verdict at `T(|x|)` equals
   the verdict at the actual halting time. So the time bound only *certifies*
   halting; it does not select the language. Hence `M ↦ L` is well defined on
   the deciding machines, and `ClassP_Step` is its image — **countable**.
3. `Language = Set BinString` with `BinString = List BinSymbol` countably
   infinite, so `#(Set BinString) = 2^ℵ₀ > ℵ₀` by Cantor. **Therefore
   `ClassP_Step ≠ Set.univ`.**

**Machinery, all present:** `Countable`/`Encodable` for `Fin n → α` with `α`
finite, `Sigma` countability, and `Cardinal.cantor`.

**One honest limit to state with it.** The same argument does **not** immediately
give `ClassNP_Step` countable: the certificate bound `p` genuinely affects the
language (enlarging `p` admits more certificates and can break the `←` direction
of the iff), and polynomially-bounded `p` range over uncountably many functions.
So the clean theorem is about `ClassP_Step` — which is all that "P is a proper
subclass" needs.

### After that, the real programme — in the file's own ordering

* **Gap (3): Cook–Levin.** *"No reductions, no completeness, no Cook–Levin.
  `ClassNP_Step` has no complete problem here, so `ClassP_Step ≠ ClassNP_Step`
  is not reduced to any concrete language."* **This is the gateway to any `≠`
  result at all** — large, but standard and well-trodden.
* **Gap (1): robustness.** *"Alphabet and tape count are fixed… not shown
  equivalent to any standard one; no robustness/simulation theorem is proved
  here."* **This is the first thing a referee asks**, and simulation theorems are
  notoriously painful to formalise. It is the cost of using a bespoke model.

## 6. Nothing dies here

No kill is owed. The step-bounded approach is non-circular (§2), α-independent
(§4), already partly built and clean (§5). **What died was the legacy carrier,
and it died on 2026-10-08** — `legacy_ClassP_eq_pair : ClassP = {∅, univ}` and
`legacy_PvsNP_Question_refuted` are its death certificate, proved in this same
file.

**The parked bridge stays parked**, and this note does not disturb it: the
spectral route's circularity (`336441d1`) and the α-web's
under-determination are untouched by anything here, because the step-bounded
definitions never mention α.

## 7. Verdict and recommendation

**BUILDABLE ENTRY POINT**, with the ceiling stated plainly:

* **What it gives:** honest P and NP over a real machine model; `P ⊆ NP` proved
  without a rigged clause; non-vacuity; strict improvement over the legacy
  carrier; and, with the next theorem, properness. All kernel-clean.
* **What it does not give:** any approach to `P ≠ NP`. `PvsNP_Step` is open and
  nothing in the route suggests a path. **Anyone reading "step-bounded approach
  to P vs NP" should read it as "step-bounded *statement* of P vs NP".**

**Recommended sequence:**

1. **Propagate the 2026-10-08 finding.** `legacy_ClassP_eq_pair` and
   `legacy_PvsNP_Question_refuted` are proved in-tree and the spectral stack was
   extended after them. Every theorem phrased over `ClassP`/`ClassNP` should be
   re-pointed at `ClassP_Step`/`ClassNP_Step` — which, per memory's standing
   adjudication, **flips every "P≠NP proved" theorem to OPEN = strengthening
   (exposes the defect), NOT a downgrade.** This file is the vehicle for that
   repair and it has been sitting unused.
2. **Build the countability/properness theorem** (§5). Bounded, standard, closes
   the author's own gap (2).
3. **Decide explicitly whether Cook–Levin is in scope.** It is the only route to
   a `≠` statement about anything concrete, and it is a programme, not a brick.
   **JUDGEMENT: not worth starting unless the P/NP axis is being promoted — and
   on the reachability ordering it should not be.**

**Reachability across the five axes now scoped:** **NS first** (carrier change +
one lemma), **YM second** (one mathlib instance, then reflection positivity),
**P/NP third — as a statement-repair, not an attack** (the repair is cheap and
overdue; the question stays open), **Hodge last** (subject absent). The parked
spectral bridge remains parked.

**OPEN / not done here:** whether `ClassNP_Step` is countable (§5's limit);
whether this bespoke TM is equivalent to mathlib's `TM2` — the file proves no
simulation theorem and memory records that mathlib lacks `FinEncoding (α × β)`,
so the `TM2` route stays blocked independently; and I read the file by header
plus the definitions and five spot-checked theorems, not all 657 lines.

---

## Label summary

* **FACT (quoted from source):** the file's three-part structure and authorship;
  the legacy-defect theorem names and the "nothing in the fractal-operator route
  is doing any work" sentence; `legacy_IsPolynomialBounded_forces_zero`; the
  `Machine`-has-no-transition-function diagnosis; the `TM` structure, `CertBlind`,
  `IsPolyBound`, `IsTimeBound`, `DecidesInTime`, `VerifiesInTime`,
  `InClassP_Step`, `InClassNP_Step`, `PvsNP_Step`; all five self-declared gaps
  including the α-web disconnection; the built theorem list.
* **MEASURED (this session):** 657 lines; zero real `sorry` (single hit is the
  header's own assertion), zero `axiom`, zero `Prop := True`.
* **JUDGEMENT (mine):** that the 2026-10-08 finding is sharper than my own
  `336441d1` audit and was not propagated; that `VerifiesInTime` is faithful to
  Cook 1971; that non-circularity is structurally checkable (no real-valued
  parameter occurs); that countability-via-halting-fixed-point is the right next
  theorem and why; that Cook–Levin should not be started on current priorities;
  the reachability ordering.
* **NOT established:** `ClassNP_Step` countability; equivalence of this TM model
  to any standard one; full line-by-line reading of all 657 lines.
