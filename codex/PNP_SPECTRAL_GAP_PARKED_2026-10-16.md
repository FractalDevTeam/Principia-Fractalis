# P≠NP spectral-gap claim: PARKED. The wiki is wrong, the ledgers are right — and the repo already contains the theorem that says why.

**Date:** 2026-10-16 (Legion, probes on Acer). Audit only; **no new Lean**
(nothing here is closable in a day — see §6). All axiom sets and statements
below are **machine-checked output**, not readings. Labels FACT / JUDGEMENT.

**VERDICT: PARKED.** The spectral-gap route cannot close P vs NP, and the
obstruction is a theorem in this repo: producing the α-assignment the route
needs is **logically equivalent** to proving `ClassP ≠ ClassNP`. The route
assumes its conclusion.

**Why the wiki claim is seductive and must still go.** "✅ FORMALLY VERIFIED
(Lean 4 + Coq, 0 incomplete proofs)" is **literally true of the artifacts**:
the Lean is kernel-clean at exactly `[propext, Classical.choice, Quot.sound]`,
there are no `sorry`s, the Coq compiles, and there are indeed 0 incomplete
proofs. What is false is that any of it is **about P vs NP**. The theorem named
`P_neq_NP` proves that a real number is nonzero.

---

## 1. What is actually proven in Lean about the spectral gap — FACT (machine-checked)

`PF/SpectralGap.lean`, 274 lines, 19 declarations. The two "ground state
eigenvalues" are **closed-form constants**:

```
def PrincipiaTractalis.lambda_0_P  : ℝ := pi_10 / √2
def PrincipiaTractalis.lambda_0_NP : ℝ := pi_10 / (phi + 1 / 4)
```
with `pi_10 := Real.pi / 10` and `phi := (1 + Real.sqrt 5)/2`
(`PF/IntervalArithmetic.lean:22,25`). So

  `λ₀(P) = π/(10√2) ≈ 0.2221441469`,  `λ₀(NP) = π/(10(φ+¼)) ≈ 0.1681764190`,
  `Δ ≈ 0.0539677287`.

**There is no operator anywhere in the file.** No `H_P`, no `H_NP`, no
Hilbert space, no Turing machine, no language, no complexity class. `λ₀` is not
the spectrum of anything; it is a name given to a quotient of constants.

The theorems, with their machine-printed types and axiom sets:

| theorem | type (as printed) | axioms |
|---|---|---|
| `spectral_gap_value` | `\|spectral_gap − 0.0539677287\| < 1e-8` | three |
| `spectral_gap_positive` | `spectral_gap > 0` | three |
| **`P_neq_NP`** | **`spectral_gap ≠ 0`** | three |
| `pvsnp_spectral_separation` | `∃ Δ > 0, Δ = lambda_0_P − lambda_0_NP ∧ \|Δ − 0.0539677287\| < 1e-8` | three |
| `unitary_conjugation_incompatible_with_spectral_gap` | `∀ (_ : lambda_0_P = lambda_0_NP), False` | three |

All `[propext, Classical.choice, Quot.sound]` — **kernel-clean, and that is not
in dispute.** Everything claimed is proved. Nothing proved is about P vs NP.

Three specific observations:

* **`P_neq_NP : spectral_gap ≠ 0`.** The name is the only complexity content in
  the declaration. Its proof is `linarith` from positivity.
* **`unitary_conjugation_incompatible_with_spectral_gap`** is `√2 ≠ φ+¼` in
  disguise. Its docstring claims the "supposed unitary relationship cannot
  exist… REFUTED at the operator-structural level, not just the numerical
  level." There are no operators in the file to refute anything about.
  **JUDGEMENT: this is the sharpest single overclaim in the chain.**
* `pvsnp_spectral_separation` is the file's "Main theorem: P ≠ NP via spectral
  separation". It quantifies over one real number.

## 2. Is "Δ > 0 ⟹ P ≠ NP" formalized? — **No.** FACT

It is **not proved, not sketched in Lean, and not stated.** There is no Lean
theorem anywhere whose hypothesis is `spectral_gap > 0` and whose conclusion
mentions `ClassP` and `ClassNP`.

The only object joining the α-values to the classes runs the **other way**, and
it is an **equivalence**, not an implication
(`PF/TuringEncoding/AlphaRealizationNoGo.lean:85`, machine-printed):

```
alpha_realization_canonical_pair_iff_classes_distinct :
  (∃ f, f ClassP = √2 ∧ f ClassNP = phi + 1/4)  ↔  ClassP ≠ ClassNP
```
axioms: three. **Kernel-clean.**

Read the two directions:

* **(→)** is true and content-free: a function cannot take two different
  values at one point, so if a realising `f` exists the classes differ.
* **(←)** is the killer: if the classes differ, such an `f` exists. So the
  hypothesis the spectral route needs is **logically equivalent to P ≠ NP.**

> **The bridge is exactly circular, and the repo proves the circularity.**
> `alpha_concrete_realization_implies_P_neq_NP` is a genuine theorem — but its
> hypothesis is a restatement of its conclusion.

## 3. Where the chain breaks — three independent breaks. FACT

### (a) λ₀ is not a spectrum

The link from the constants to any operator is `λ₀(H_α) = π/(10α)`. The repo's
own docstring (`PF/TuringEncoding/Operators.lean:181-228`) states its status
with complete honesty, and it is worth quoting because it is the repo
convicting the claim:

> "The manuscript Ch 21 establishes the values `α_P = √2` and `α_NP = φ + 1/4`
> via **three named non-theorems**:
> * `Observation obs:hp-closed-form` — the **empirical** (numerical,
>   finite-dim, 10-digit-precision) ground-state energy of `H_P` AGREES with
>   the closed form `π/(10√2)` to within 10⁻¹⁰… **it does NOT claim to derive
>   the closed form** from the operator's spectral structure.
> * `Conjecture conj:polylog-spectrum` — … **NOT proven.**
> * `Heuristic heur:branch-selection` — … Labeled `\begin{heuristic}`, not
>   `\begin{theorem}`.
> * `Conjecture conj:golden-modulation` — the unitary conjugacy
>   `H_NP = U(φ)·H_P·U†(φ)` that pins `α_NP = φ + 1/4`… **NOT proven.**"

So the numerical coincidence at 10⁻¹⁰ is the entire empirical basis, and the
structure around it is two conjectures and a heuristic.

### (b) `alpha_of_class` is opaque — **this is the exact missing link**

Machine-printed: `opaque PrincipiaTractalis.TuringEncoding.alpha_of_class :
Set TuringEncoding.Language → ℝ`. **No definitional content.** The same
docstring says a concrete definition

> "(a) … would require deciding ClassP = ClassNP — **itself the P vs NP
> problem**"

and closes:

> "**Retirement requires original mathematical research, not formalization
> labor.**"

The axiom that formerly pinned the canonical values,
`alpha_class_canonical_values`, was **deleted 2026-05-14**
(`Operators.lean:331`), and there are **zero declared project axioms repo-wide**
(verified: the three `grep` hits for `^axiom` are docstring prose). So nothing
pins the values now — correctly, but it also means the chain has no first link.

> **Named exactly: there is no function from complexity classes to α, and by
> §2 producing one is equivalent to P ≠ NP.**

### (c) The chain uses the vacuous generation of class carriers

The no-go is stated about `ClassP`/`ClassNP` from
`PF/TuringEncoding/Complexity.lean:118` — the carriers this project's own
ledger records as vacuous (`ClassP = {∅, univ}`, a trailing-input clause
forcing `accepts` constant; `legacy_P_neq_NP_def_unconditional` proving P≠NP
from no hypothesis; see `project_millennium_faithful_encodings`).

A **repaired** and genuine-looking pair exists —
`PF/TuringEncoding/InClassPRepair_2026_10_08.lean:405-416`, with
`ClassP_Step`, `InClassNP_Step`, real verifiers, certificates and polynomial
bounds. **Nothing in the spectral chain uses it.** So even if (a) and (b) were
repaired, the target statement would still be about the wrong objects.

**JUDGEMENT:** (c) is the most tractable of the three and the only one that is
formalization labor rather than research — but on its own it buys nothing,
because (b) blocks regardless of which carriers it blocks against.

## 4. The Coq side adds nothing — FACT

`PF_Coq_Code/PF/PNP_FrameworkMillenniumAnswerCoq.v` (171 lines) and
`PF_Coq_Code/PF/Wave41/AlphaOfClassNoGoSingleCitation.v` (252 lines). **Every
proposition is defined as `True`:**

```coq
Definition spectral_gap_positive : Prop := True.
Definition P_neq_NP_via_spectral_separation : Prop := True.
Definition pvsnp_spectral_separation : Prop := True.
Definition unitary_conjugation_incompatible_with_spectral_gap : Prop := True.
```

and the headline theorem is proved by nine copies of the proof of `True`:

```coq
Theorem pnp_axis_framework_level_millennium_answer :
  PNPFrameworkMillenniumAnswerBundle.
Proof. apply mkPNPBundle. - exact I. - exact I. … Qed.
```

No `Axiom`, `Parameter`, `Hypothesis` or `Admitted` — because there is nothing
to assume. **This is why "0 incomplete proofs" is true and meaningless: `True`
is never incomplete.**

The Coq file states its own scope, and should be credited for it:

> `Definition honest_scope_coq_parity_only_not_a_clay_discharge : Prop := True.`
> … "Coq structural-shape parity **ONLY**. The Lean side composes axiom-free
> content by exact name…"

So the "Lean 4 + Coq" double-verification in the wiki claim is one kernel-clean
arithmetic file plus a set of name-level stubs that declare themselves stubs.

## 5. Verdict

**PARKED.** Not CONDITIONAL — a conditional result would need a stated
hypothesis that is not a restatement of the conclusion, and by §2 the only
available hypothesis is equivalent to `ClassP ≠ ClassNP`. Not PROVED, by §1–§4.

| Rio's question | answer |
|---|---|
| What is proven in Lean? | `π/(10√2) − π/(10(φ+¼)) ≈ 0.05397 > 0`, kernel-clean at the three axioms. Arithmetic on two constants. |
| Is `Δ>0 ⟹ P≠NP` formalized? | **No** — not proved, sketched, or stated. |
| Where does it break? | (a) λ₀ is not a spectrum; **(b) `alpha_of_class` is opaque and defining it is P-vs-NP-equivalent — the exact missing link**; (c) the chain uses the vacuous class carriers, not the Oct-8 repaired ones. |
| Does Coq add anything? | **No.** `Prop := True` throughout; headline proved by `exact I` ×9; self-declared parity-only. |

**One of the wiki and the ledgers is wrong: it is the wiki.** The ledgers,
`project_millennium_faithful_encodings`, and the docstrings inside
`Operators.lean` and the Coq files are all consistent and correct. The wiki
claim is the outlier.

## 6. Nothing here is closable in under a day — and what to do instead

Per the order I checked for a closable gap. There is none:

* (b) is the P vs NP problem, by the repo's own `iff`.
* (a) needs the spectral derivation of `λ₀(H_α) = π/(10α)` from the
  fractal-kernel construction — the docstring calls it "multi-page operator
  theory, not yet attempted in the manuscript."
* (c) is a week of honest formalization at best, and buys nothing while (b)
  stands.

**The actionable item is the claim, not the mathematics — repair, not
disclosure.** Two things, both Pablo-gated because they touch public text:

1. **The wiki's "✅ FORMALLY VERIFIED" for P≠NP must come off.** It is the
   crank-flag in this axis, and it is the kind that a referee finds in ten
   minutes and never forgives — precisely because the underlying Lean *is*
   clean, which makes the mismatch look deliberate rather than careless.
2. **`theorem P_neq_NP : spectral_gap ≠ 0` is the root cause and should be
   renamed to match what it proves** (e.g. `spectral_gap_ne_zero`), likewise
   `pvsnp_spectral_separation` and
   `unitary_conjugation_incompatible_with_spectral_gap`. **This is not a
   downgrade under the standing rule** — the content is unchanged and the name
   currently overstates it; removing an overclaim is strengthening, the same
   precedent recorded for the NS carrier repair. The honest-scope commentary
   already present in the Coq files is the model.

**JUDGEMENT on the whole axis.** There is real, kernel-clean work here and a
genuinely honest documentation layer sitting right next to a headline that
contradicts it. The defect is not in the proofs; it is in the naming and the
public summary. That is cheap to fix and expensive to leave.

---

## Label summary

* **FACT (machine-checked this session):** the printed types of `P_neq_NP`,
  `pvsnp_spectral_separation`, `alpha_realization_canonical_pair_iff_classes_distinct`;
  the definitions of `lambda_0_P`, `lambda_0_NP`, `pi_10`, `phi`; `opaque
  alpha_of_class`; all four axiom sets `[propext, Classical.choice, Quot.sound]`;
  probe EXIT=0.
* **FACT (read in source):** the `Operators.lean` docstring's three named
  non-theorems and its "(a) … itself the P vs NP problem" and "Retirement
  requires original mathematical research" sentences; the 2026-05-14 deletion of
  `alpha_class_canonical_values`; zero declared project axioms repo-wide; the
  Coq `Prop := True` definitions, the nine `exact I`, and the self-declared
  parity-only scope; `ClassP_Step`/`InClassNP_Step` existing and being unused by
  the spectral chain.
* **JUDGEMENT (mine):** that `unitary_conjugation_incompatible_with_spectral_gap`
  is the sharpest overclaim; that PARKED rather than CONDITIONAL is the right
  verdict; that (c) is tractable but worthless alone; that renaming is
  strengthening rather than a downgrade; the recommendation in §6.
* **NOT established:** that no spectral route to P vs NP could exist. What is
  established is that **this** one is circular by the repo's own theorem, and
  that its present Lean content is arithmetic about two constants.
