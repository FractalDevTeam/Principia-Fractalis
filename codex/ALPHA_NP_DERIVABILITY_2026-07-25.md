# Is `α_NP = φ + 1/4` Derivable? — Full Evidence Audit

**Date:** 2026-07-25
**Scope:** read-only audit. No Lean edited, no claim changed, no file deleted.
**Question:** Is `α_NP = φ + 1/4` (A) derivable from more primitive postulates,
(B) circular, (C) provably P-vs-NP-equivalent, or (D) something else?

---

## 0. VERDICT

> **(B), with a precise (D) qualification, and (C) is FALSE as stated in the
> triage.**
>
> **`α_NP = φ + 1/4` is a DEFINITION that is re-derived from theorems whose
> only proof is `unfold` + `ring` on that same definition.** Every purported
> "derivation" or "forcing" in the corpus is one of three closed loops
> (§2). No file anywhere in the Lean corpus, the manuscript, the arXiv
> prior-work paper, or the referenced `cohen2025pvsnp` contains a derivation
> of the value from anything more primitive.
>
> **The genuinely open analytic step is not merely unformalized — it is
> absent from the corpus entirely.** It is deferred to `cohen2025pvsnp`
> (`Principia_Fractalis_master_folder/bibliography.bib:3229`), which is an
> **unpublished manuscript by the author himself**, and the actual companion
> paper that exists (`Papers/PriorWork_PNeqNP_Spectral_Arxiv_2025/`) does not
> derive it either — it *assumes* it in a definition (§2.3).
>
> **The triage's bucket-3 claim is over-generous to the framework.** The
> P-vs-NP-equivalence theorem (`AlphaRealizationNoGo`) is real and correctly
> proved, but it establishes only that *assigning any two distinct reals* to
> `ClassP` and `ClassNP` is P-vs-NP-equivalent. It says **nothing** about the
> specific value `φ + 1/4`. Deriving the *specific value* is not shown to be
> P-vs-NP-equivalent, and `EnumToClassSeparationBridge` carries no α-content
> at all (§3).
>
> **Honest one-line statement:**
> *`α_NP = φ + 1/4` is asserted. It cannot currently be derived, and the
> corpus contains no visible route to deriving it. The `φ` has a real
> (though non-derivational) motivation via H₃/icosahedral symmetry; the
> `+1/4` has none beyond numerological pattern-match to the H₃ exponent gap.*

---

## 1. GROUND TRUTH — WHAT IS A DEFINITION AND WHAT IS A THEOREM

### 1.1 The value is a `def`, in at least five places

| File:line | Declaration |
|---|---|
| `PF_Lean4_Code/PF/CrossMillenniumSharedInvariants.lean:70` | `noncomputable def α_NP : ℝ := phi + 1/4` |
| `PF_Lean4_Code/PF/TuringEncoding/PolylogQuadraticDerivation.lean:75` | `noncomputable def alphaNP : ℝ := phi + 1/4` |
| `PF_Lean4_Code/PF/H3UnifiedMillenniumStructure.lean:41` | `noncomputable def alpha_NP_H3U : ℝ := goldenRatio + 1 / 4` |
| `PF_Lean4_Code/PF/H3CoxeterOrigin.lean:236` | `noncomputable def alpha_NP_H3 : ℝ := goldenRatio + 1 / 4` |
| `PF_Lean4_Code/PF/IBMPeaksGaloisPair.lean:64` | `noncomputable def alpha_NP : ℝ := phi + 1/4` |

There is no `theorem` anywhere whose conclusion is `α_NP = φ + 1/4` and whose
hypotheses do not already contain that fact.

### 1.2 The only genuinely opaque object is `alpha_of_class`

```lean
-- PF/TuringEncoding/Operators.lean:178
opaque alpha_of_class : Set Language → ℝ
```

and the conjecture that pins it:

```lean
-- PF/TuringEncoding/Operators.lean:250-253
def PolylogEigenvalueConjecture : Prop :=
    ((alpha_of_class ClassP)^2 = 2 ∧ 0 < alpha_of_class ClassP) ∧
    (16 * (alpha_of_class ClassNP)^2 - 24 * (alpha_of_class ClassNP) - 11 = 0 ∧
     0 < alpha_of_class ClassNP)
```

**The corpus is already honest about this in its own docstring.**
`Operators.lean:213-228` states, verbatim:

> "The manuscript Ch 21 establishes the values `α_P = √2` and `α_NP = φ + 1/4`
> via three named non-theorems … `Conjecture conj:polylog-spectrum` … NOT
> proven … `Heuristic heur:branch-selection` … Labeled `\begin{heuristic}`,
> not `\begin{theorem}` … `Conjecture conj:golden-modulation` … NOT proven."

and at `Operators.lean:230-235`:

> "**Retirement requires original mathematical research, not formalization
> labor.**"

**This audit confirms that assessment and finds it, if anything, understated.**

### 1.3 The polynomial and the closed form are the same statement

`PF/TuringEncoding/AlphaCanonical.lean:108-155`
(`algebraic_pair_to_value_assignment`) proves that for *any* `f`, the algebraic
system `16(f y)² − 24(f y) − 11 = 0 ∧ 0 < f y` is equivalent to
`f y = φ + 1/4`. The file's own docstring says so at lines 16-19:

> "The axiom's substantive content is therefore **not** the algebraic equations
> themselves (which are simple arithmetic facts about specific real numbers)
> but rather the *structural assignment* of these values to ClassP and ClassNP
> via the opaque function `alpha_of_class`."

Confirmed. `16x² − 24x − 11 = 0` with `x > 0` and `x = φ + 1/4` carry **exactly
the same information**. Neither derives the other. Any argument of the form
"the quadratic forces φ + 1/4" is a restatement, not a derivation.

---

## 2. THE CIRCLES

Three distinct closed loops. All three are load-bearing somewhere in the
corpus or the current paper.

### 2.1 CIRCLE 1 — the "9-of-9 rigidity" loop (the most load-bearing)

This is the circle the **current paper explicitly relies on**:

> "The substrate forces $\alpha_{\textsf{NP}} = \varphi + 1/4 = 1.86803\ldots$
> via (I4) + (I10)"
> — `Papers/principia_fractalis_millennium_problems_2026-07-13.tex:160`
> (repeated at `:361`, `:926`)

**The cycle:**

```
  ┌──────────────────────────────────────────────────────────────────┐
  │                                                                  │
  │  (1) DEFINITION                                                  │
  │      CrossMillenniumSharedInvariants.lean:70                     │
  │        noncomputable def α_NP : ℝ := phi + 1/4                   │
  │      CrossMillenniumSharedInvariants.lean:85                     │
  │        noncomputable def α_Hodge : ℝ := phi                      │
  │                          │                                       │
  │                          ▼                                       │
  │  (2) "INVARIANT 10", proved BY UNFOLDING (1)                     │
  │      CrossMillenniumSharedInvariants.lean:166-167                │
  │        theorem α_NP_sub_Hodge_eq_quarter :                       │
  │            α_NP - α_Hodge = 1/4 := by                            │
  │          unfold α_NP α_Hodge; ring     ← the WHOLE proof         │
  │                          │                                       │
  │                          ▼                                       │
  │  (3) PROMOTED TO A HYPOTHESIS FIELD                              │
  │      CrossMillenniumDerivedConsequences.lean:252-254             │
  │        structure ExtendedAbstractAlphaSystem ... where           │
  │          inv_Hodge_sq_eq_self_plus_one : αHodge^2 = αHodge + 1   │
  │          inv_NP_sub_Hodge_eq_quarter   : αNP - αHodge = 1/4      │
  │                          │                                       │
  │                          ▼                                       │
  │  (4) "★★★ FULL RIGIDITY THEOREM — 9 of 9 α-values forced ★★★"    │
  │      CrossMillenniumDerivedConsequences.lean:278-285, 325-329    │
  │        theorem alpha_system_rigidity_extended (S : Extended…) :  │
  │          … ∧ S.αNP = (1 + Real.sqrt 5)/2 + 1/4 ∧ …               │
  │        proof of the αNP clause, verbatim (lines 325-329):        │
  │          have h_NP : S.αNP = (1 + Real.sqrt 5) / 2 + 1/4 := by   │
  │            have := S.inv_NP_sub_Hodge_eq_quarter                 │
  │            rw [h_Hodge] at this                                  │
  │            linarith                                              │
  │                          │                                       │
  │                          ▼                                       │
  │  (5) CITED AS "FIRST PRINCIPLES" / "NOT ASSERTED"                │
  │      CrossMillennium/AlphaValuesFirstPrinciples.lean:294-297     │
  │        "This strengthens the framework's claim from 'α-values    │
  │         asserted…' to 'α-values DERIVED from substrate           │
  │         structure and OVER-DETERMINED by the algebraic           │
  │         skeleton'."                                              │
  │                          │                                       │
  │                          ▼                                       │
  │  (6) CITED IN THE PAPER AS "the substrate forces α_NP"           │
  │      millennium_problems_2026-07-13.tex:160, 361, 926            │
  │                          │                                       │
  └──────────────────────────┴───► back to (1). The "invariant"      │
                                    IS the definition.               │
```

**The circle in one sentence:** the rigidity theorem derives
`α_NP = φ + 1/4` from the hypothesis `α_NP − α_Hodge = 1/4` plus
`α_Hodge² = α_Hodge + 1`; the first hypothesis is a theorem proved by
`unfold α_NP α_Hodge; ring` from `α_NP := phi + 1/4`, and the second is
proved the same way from `α_Hodge := phi`. **The system is fed φ and 1/4 and
returns φ + 1/4.**

**Corollary — the paper's "coefficient-rigidity certificate" is vacuous.**
`millennium_problems_2026-07-13.tex:352` argues:

> "perturb the coefficient of invariant I4 ($16\alpha^2 - 24\alpha - 11 = 0$)
> by 1% … Joint consistency between I2 ($\alpha_{\textsf{NP}} = \varphi + 1/4$
> pinned by the substrate) and the perturbed I4 is broken"

I2 and I4 are provably the *same statement* (`AlphaCanonical.lean:108-155`).
Perturbing one and observing it no longer agrees with the other tests
nothing. This "four-way rigidity" argument, on the I2/I4 leg, has no content.

### 2.2 CIRCLE 2 — the `AlphaValuesFirstPrinciples` loop

`PF/CrossMillennium/AlphaValuesFirstPrinciples.lean` is titled
*"First-principles derivations of the framework α-values"* and carries a table
of "Forcing reason"s (lines 12-19). **Every theorem in the file is `rfl`,
`norm_num`, or `ring` applied to the definition.** Examples:

```lean
-- :58-59
theorem alpha_Poincare_eq_one_from_substrate_identity :
    α_Poincare = 1 := rfl

-- :73-76
theorem alpha_RH_eq_one_plus_one_half_from_critical_line :
    α_RH = α_Poincare + 1/2 := by
  unfold α_RH α_Poincare
  norm_num
```

The "forcing reason" column is prose in a comment. It has no Lean content and
no proof anywhere. This file cannot be cited as a derivation of anything.

**Additional finding — the file's own α_PvNP is a *different, incompatible*
value.** Its §6 (lines 140-161) derives the P-vs-NP α from the "polylog
deficit" as `alpha_PvsNP = α_Poincare + 1/4 = 5/4` — **not** `φ + 1/4`. The
corpus itself records that these are algebraically incompatible:

> `PF.lean:94` (on `PolylogEigenvalueClosureAttempt`):
> "the cascade outputs `a_PvNP = 5/4`, which **fails** the NP-axis
> self-adjointness quadratic `16α² − 24α − 11 = 0` (value **-16**, not 0).
> The substrate cascade therefore does NOT close the 4th sub-prop … there are
> **TWO distinct NP-α-axes** (5/4 polylog-deficit vs φ+1/4 self-adjointness)
> and they are **algebraically incompatible**."

So the framework's own "first-principles substrate cascade" produces a value
that *contradicts* the canonical α_NP. That is not a derivation gap — it is a
derivation that comes out wrong, retained alongside the value it contradicts.

### 2.3 CIRCLE 3 — the empirical/spectral loop (the most serious)

This is the loop behind the "10⁻¹⁰-precision empirical confirmation" claim.

**Step A — the α value is inserted into the operator's own definition.**
`Papers/PriorWork_PNeqNP_Spectral_Arxiv_2025/p_neq_np_spectral.tex:585-591`:

```latex
\begin{definition}[NP-class Weight Function]
w_{NP}(C, C') = \frac{\pi}{10(\phi + 1/4)} \cdot
                \frac{1}{1 + D_3(\encode(C) + \encode(C'))}
\end{definition}
```

The constant `π/(10(φ+1/4))` is **literally a factor in the definition of the
Hamiltonian's matrix elements**.

**Step B — it is recovered as the "computed" ground state.**
Same file, `:620-627`, `\begin{theorem}[Ground State Eigenvalues]`:

```latex
\lambda_0(H_{NP}) = \frac{\pi}{10\alpha_{NP}} = \frac{\pi}{10(\phi + 1/4)}
```

**Step C — the ground state is inverted to "extract" α.**
`Papers/PriorWork_AlphaUniqueness_Nov2025/ALPHA_UNIQUENESS_CERTIFICATION.md`,
§4:

> "Using α = π/(10λ₀): … α_NP = π/(10 × 0.168176418230) = 1.868033988744673 …
> |α_NP(empirical) − φ+1/4| = 5.222 × 10⁻¹² … These are not arbitrary choices
> or fitting parameters. They are **forced** by the spectral data."

**The cycle:**

```
  φ + 1/4  ──inserted into w_NP──►  H_NP  ──"computed"──►  λ₀ = π/(10(φ+1/4))
     ▲                                                            │
     │                                                            │
     └────────── α = π/(10 λ₀)  ◄──"empirical extraction"─────────┘
```

The claimed `5.2 × 10⁻¹²` agreement is the round-trip error of dividing π by
`10·(φ+1/4)` and then dividing π by the result. It is a floating-point
artifact, not evidence.

The 2026-05-20 reconciliation note in
`ARCHIVE/2026-05-XX-historical/DERIVATION_ANALYSIS_alpha_NP.md` inadvertently
documents the loop closing:

> "The certified empirical is `λ_0(H_NP) = 0.1681764182230`, which **exactly
> matches** the canonical Lean closed form `π/(10(φ+1/4))` to 10⁻¹⁰."

It matches exactly because it is the same number, computed twice.

**Step D — the loop is then labelled "EMPIRICAL VALIDATION" in Lean, with a
`rfl` proof.** `PF/CrossMillenniumDerivedConsequences.lean:371-376`:

```lean
/-- **★ EMPIRICAL VALIDATION (α_NP): the framework's rigidity-forced
    α_NP matches the IBM Quantum hardware-measured NP peak EXACTLY
    (within four-decimal empirical precision of `1.868 ≈ φ + 1/4`).** -/
theorem framework_α_NP_matches_IBM_empirical_peak :
    α_NP = PrincipiaTractalis.IBMPeaksGaloisPair.alpha_NP :=
  rfl
```

`α_NP` is `phi + 1/4` (`CrossMillenniumSharedInvariants.lean:70`);
`IBMPeaksGaloisPair.alpha_NP` is `phi + 1/4` (`IBMPeaksGaloisPair.lean:64`).
`rfl` closes it because both sides are the same term. **No measurement enters
this theorem.** It is a docstring asserting empirical validation attached to a
proof of `x = x`.

### 2.4 Where the chain actually terminates: an unpublished self-reference

The one place the corpus says the real derivation lives:

`PF/TuringEncoding/PolylogEigenvalueClosureAttempt.lean:370-388` quotes
`ch21_p_vs_np.tex` lines 102-105 verbatim:

> "Imposing this condition and analyzing the phase factors `e^(iπ α D_3(n))`
> leads to Diophantine constraints. The solutions `α_P = √2` and
> `α_NP = φ + 1/4` emerge as the unique values … **Complete proof in
> [cohen2025pvsnp]**."

and then records, honestly:

> "The Diophantine analysis producing the polynomial `16α² − 24α − 11 = 0`
> from H_NP self-adjointness:
> * Is **deferred to an external reference** (cohen2025pvsnp).
> * Is **not** present in the Lean codebase …
> * Is **not** present in the manuscript proper."

**What `cohen2025pvsnp` actually is** —
`Principia_Fractalis_master_folder/bibliography.bib:3229-3235`:

```bibtex
@misc{cohen2025pvsnp,
  author = {Cohen, Pablo},
  title = {Resolution of P versus NP through Operator-Theoretic Spectral Analysis},
  year = {2025},
  note = {Spectral gap $\Delta = 0.0891219046$ proves P $\neq$ NP. ...},
  howpublished = {Unpublished manuscript}
}
```

**It is an unpublished manuscript by the author.** The rev2 bibliography is
even blunter — `ARCHIVE/…/Principia_Fractalis_master_folder_rev2/bibliography.bib:3364`:

> "% cohen2025weinstein, cohen2025pvsnp -- **placeholder entries** pointing at…"

The nearest existing artifact, `p_neq_np_spectral.tex`, does not contain the
derivation: it *defines* α_P and α_NP (`:498-503`) and builds the Hamiltonian
around them (`:589`). **The reference chain terminates in a placeholder.**

Note also the numerical inconsistency the bib entry itself carries: it
advertises `Δ = 0.0891219046`, while `p_neq_np_spectral.tex:62` reports
`Δ = 0.0539677287`. See §4.

### 2.5 The `Prop := True` layer

The formal "composition with the analytic step" is a no-op:

```lean
-- PF/TuringEncoding/PolylogQuadraticDerivation.lean:216-219
def FrameworkNPSelfAdjointnessReductionToQuadratic (α : ℝ) : Prop :=
  True

-- :224-225
theorem framework_NP_reduction_holds (α : ℝ) :
    FrameworkNPSelfAdjointnessReductionToQuadratic α := trivial

-- :237-240 — the "substrate-route closure"
theorem substrate_route_NP_axis_forces_alphaNP
    (α : ℝ) (_ : FrameworkNPSelfAdjointnessReductionToQuadratic α)
    (hq : NPQuadratic α = 0) (hp : 0 < α) : α = alphaNP :=
  NPQuadratic_positive_root_unique α hq hp
```

The first hypothesis is discarded (`_`). The theorem is exactly
"the positive root of the quadratic is φ + 1/4" — §1.3's tautology — wearing a
`True`-valued costume named after the missing analytic step.

The same pattern recurs in the "substrate discharge" of the empirical
hypothesis, `PF/Empirical/EmpiricalAlphaIdent_Substrate_Anchors.lean`:

```lean
:154  def IBM9Way_AlphaPin_Anchor : Prop := True
:182  def Ch21_PolylogSpectralDerivation_Anchor : Prop := True
:227  def CrossMillenniumInvariants_AlphaSkeleton_Anchor : Prop := True
:259  def EmpiricalAlphaIdentificationHypothesis_Substrate : Prop :=
        IBM9Way_AlphaPin_Anchor ∧ Ch21_PolylogSpectralDerivation_Anchor ∧
        CrossMillenniumInvariants_AlphaSkeleton_Anchor
```

The file is candid about it (`:35`, `:66-69`) — it calls this the framework's
"typed-anchor pattern". But the resulting `empirical_alpha_ident_substrate_discharge`
(`:274`) is `True ∧ True ∧ True → True ∧ True ∧ True`. It discharges nothing.

---

## 3. THE (C) CLAIM IS FALSE AS STATED — WHAT `AlphaRealizationNoGo` ACTUALLY PROVES

The triage (`codex/RESIDUAL_TRIAGE_2026-07-23.md`, §1.2 and §3 item 3) says:

> "**Any genuine derivation is P-vs-NP-equivalent**: Wave 57 sharpness
> certificate + `AlphaRealizationNoGo` show a concrete discharge decides
> P vs NP."

**The theorem is real and correctly proved. The inference drawn from it is
not.** Here is the theorem in full
(`PF/TuringEncoding/AlphaRealizationNoGo.lean:85-108`):

```lean
theorem alpha_realization_canonical_pair_iff_classes_distinct :
    (∃ f : Set Language → ℝ,
        f ClassP = Real.sqrt 2 ∧ f ClassNP = phi + 1/4) ↔
      ClassP ≠ ClassNP := by
  constructor
  · rintro ⟨f, hP, hNP⟩ heq
    have hf : f ClassP = f ClassNP := congrArg f heq
    rw [hP, hNP] at hf
    linarith [phi_plus_quarter_gt_sqrt2]
  · intro hne
    refine ⟨fun S => if S = ClassP then Real.sqrt 2
                     else if S = ClassNP then phi + 1/4 else 0, ?_, ?_⟩
    · simp
    · have hne_sym : ClassNP ≠ ClassP := fun h => hne h.symm
      simp [hne_sym]
```

**Read the proof.** The forward direction uses `√2 ≠ φ + 1/4` and nothing else.
The backward direction is a classical `if`-then-`else`. **The theorem holds
verbatim for any two distinct reals `a ≠ b` in place of `√2` and `φ + 1/4`.**
It would be equally true for `(0, 1)`, `(e, π)`, or `(1.7, 2.3)`.

**What it therefore establishes:**
> *Assigning two **distinct** numbers to `ClassP` and `ClassNP` via a total
> function is equivalent to `ClassP ≠ ClassNP`.*

**What it does NOT establish:**
> *Determining that the NP number is **φ + 1/4 specifically** is
> P-vs-NP-hard.*

The no-go constrains the **distinctness** clause of
`PolylogEigenvalueConjecture`, not the **value** clause. The corpus's own
decomposition confirms this split — `PF.lean:689` on
`PolylogEigenvalueConjectureDecomposition_2026_06_24`:

> "Sub-claims 1–4 encode the algebraic uniqueness equations … STATUS: (C)
> Substrate-internal open … Sub-claim 5 (distinctness α_P ≠ α_NP) is
> kernel-only PROVEN … **P ≠ NP chain requires only Sub-claim 5
> (distinctness).**"

So: the P≠NP chain needs only distinctness (proven at enum level, but
P-vs-NP-equivalent at set level by the no-go); the *values* (sub-claims 1–4)
are open **and are not what the no-go is about**.

**`EnumToClassSeparationBridge` carries zero α-content.** Its definition
(`PF/TuringEncoding/PNPClassSeparationPrecisionBridge.lean:241-242`):

```lean
def EnumToClassSeparationBridge : Prop :=
  ∃ L : DecidableProblem, L ∈ class_NP_typed ∧ L ∉ class_P_typed
```

This is literally "∃ L ∈ NP \ P" — P ≠ NP restated. The file says so at
`:250`:

> "NOTE: this is a *reduction*, not a discharge: **the bridge IS the gap.**"

Correct, and honest — but there is no α in it. It cannot be used to argue that
pinning α_NP is P-vs-NP-equivalent.

**Net correction to the triage:** the α-pin should be reclassified as

- **distinctness clause** (`α_P ≠ α_NP` at set level): bucket 3 — genuinely
  P-vs-NP-equivalent, per `AlphaRealizationNoGo`. ✔ triage correct.
- **value clause** (`α_NP = φ + 1/4` specifically): **bucket 2, and not shown
  to be bucket 3.** The triage's "derivation is bucket 3" upgrade is not
  supported by any theorem in the corpus. Calling it bucket 3 makes the gap
  look *harder* (and therefore more excusable) than the evidence warrants.
  It is an unsupported assertion whose difficulty is simply **unknown**.

---

## 4. THE EMPIRICAL ROUTE — THE DATA DOES NOT SUPPORT THE PIN

Dataset: `Papers/Data/principia_fractalis_143_problems_IBM_dataset.csv`
(identical content to `/home/xluxx/143.csv` modulo timestamp formatting).
**142 data rows**, not 143.

### 4.1 The pin rests on exactly one row, which is the row named "P vs NP"

```
theory     = "P vs NP"
category   = "Computation"
peak_alpha = 1.8680000000000003
timestamp  = 5/23/25 4:04
```

Rows within 0.05 of φ+1/4 = 1.86803: **1 of 142.**
Rows within 1e-4 of √2: **0 of 142.** (The closest are `1.41`, Δ = 0.0042.)

### 4.2 Other complexity-theoretic rows scatter and contradict a class invariant

If α were an invariant of the complexity *class*, every NP-side row should sit
at 1.868. Actual values:

| Problem | Category | peak_alpha |
|---|---|---|
| **P vs NP** | Computation | **1.868** |
| Integer Programming | Computation | 1.75 |
| Polynomial Zeros | Computation | 1.70 |
| Linear Inequalities | Computation | 1.60 |
| Exponential Time Hypothesis | Complexity Theory | 1.59 |
| Computational Duality | Computation | 1.45 |
| Counting CSP Complexity | Complexity Theory | 1.39 |
| Unique Games Conjecture | Complexity Theory | 1.38 |
| Graph Isomorphism | Graph Theory | 1.41 |

Unique Games and Counting CSP — both squarely NP-side — land nearer `√2` than
`φ + 1/4`. **The single hit is on the row *named after the hypothesis being
tested*.** That is the signature of a label effect, not a class invariant.

### 4.3 The α-histogram has no peak at either canonical value

Modal values across all 142 rows: **1.45 (7 rows)**, 1.55 (7 across two float
encodings), 1.50 (6), 1.60 (6), 1.65 (4). Mean 1.772, median 1.600.
Neither 1.414 nor 1.868 is a mode. There is no bimodal P/NP structure.

### 4.4 The "16-decimal precision" claim is IEEE-754 noise — verified

`millennium_problems_2026-07-13.tex:1279` states:

> "13 rows at 16-decimal floating-point precision (including the P-versus-NP
> row at `peak_alpha = 1.8680000000000003`…)"

and `:1285` builds the pre-registered `10⁻⁴` GI acceptance threshold on this
being "the currently-demonstrated precision".

**Direct check:**

| value in CSV | rounded to 3 dp | difference |
|---|---|---|
| 1.8680000000000003 | 1.868 | **+2.220446e-16** |
| 1.5499999999999998 | 1.550 | **−2.220446e-16** |
| 1.5899999999999999 | 1.590 | **−2.220446e-16** |
| 1.9500000000000002 | 1.950 | **+2.220446e-16** |

Every one differs from its 3-decimal rounding by **exactly ±1 ULP**
(2.22e-16 = 2⁻⁵²). These are 3-decimal quantities carrying double-precision
representation noise, produced by ordinary float arithmetic (e.g.
`1.87 − 0.002` evaluates to `1.868` at exactly this offset). They are **not**
16-digit measurements.

**Consequence:** the actual match is `1.868` vs `1.8680339887…`, i.e.
Δ = 3.4 × 10⁻⁵ against a measured value known to **3 decimal places**. The
`10⁻⁴` pre-registered tolerance at `:1281`/`:1285` is calibrated against a
precision the pipeline does not have, which makes the GI forward test
unresolvable-by-noise in either direction.

### 4.5 The 10⁻¹⁰ / 143-problem λ₀ claim is unsupported by this dataset

`ALPHA_UNIQUENESS_CERTIFICATION.md` §1 and Appendix C claim
"143 independent problem measurements, each precise to 10 decimal places"
of `λ₀`. **The CSV has no `λ₀` column at all** — the columns are
`theory, source, category, known_result, fractal_coherence, fractal_time,
fractal_peak_scale, peak_alpha, conv_rate, sg_corr, dim_scale, cqc, stability,
entropy, spectrum, quantum_fidelity, quantum_time, consistency,
coupling_strength, phase_trans, spec_corr, timestamp`. The "empirical λ₀" is a
single number from Ch 21 which, per §2.3, is the closed form.

### 4.6 Three mutually-inconsistent spectral gaps, machine-checked distinct

`PF/TuringEncoding/SpectralGapInconsistencyAnalysis.lean:44-52`:

```lean
noncomputable def Delta_emp : ℝ := 891219046 / 10000000000  -- ≈ 0.0891  (IBM)
noncomputable def Delta_gm  : ℝ := 131 / 1000               -- ≈ 0.131   (golden-modulation)
noncomputable def Delta_lcf : ℝ := 54 / 1000                -- ≈ 0.054   (Lean closed form)
```

with `:72-89` proving all three pairwise distinct. The corpus carries three
different values for the quantity that is supposed to be its headline
observable — plus `|spectral_gap − 0.0539677287| < 1e-8` at `PF.lean:476`, and
`Δ = 0.0891219046` in the `cohen2025pvsnp` bib note. **The empirical
Δ ≈ 0.0891 is not reproduced by any closed form in the corpus.**

**Honest assessment of the empirical route: the 143-problem dataset provides
no support for the α_NP pin.** It provides one 3-decimal coincidence on a
self-labelled row, against a background distribution that peaks elsewhere and
in which structurally similar NP problems scatter across [1.38, 1.75].

---

## 5. THE PARTIAL RESULTS — HOW FAR ANYTHING ACTUALLY GETS

Honest accounting of what *is* established, since a negative result should not
erase real content.

### 5.1 What is genuinely proven, axiom-free

- **Root-uniqueness.** `NPQuadratic_positive_root_unique`
  (`PolylogQuadraticDerivation.lean:174-201`): the unique positive root of
  `16x² − 24x − 11` is `φ + 1/4`. Correct, kernel-only, and *content-free as a
  derivation* (§1.3), but valid algebra.
- **Value ↔ system equivalence.** `algebraic_pair_to_value_assignment`
  (`AlphaCanonical.lean:108-155`). Correct.
- **The no-go / sharpness certificate.**
  `alpha_realization_canonical_pair_iff_classes_distinct`
  (`AlphaRealizationNoGo.lean:85-108`). Correct, and genuinely valuable — but
  about distinctness, not values (§3).
- **The negative result on the bare generating-function route.** This is the
  most intellectually honest artifact in the whole chain:

  ```lean
  -- PF/TuringEncoding/WeightedDigitalSumGeneratingFunction.lean:130-133
  theorem bare_route_structural_finding (α : ℝ) :
      (betaIm α = 0) →
      (Real.sin (Real.pi * α) = 0 ∨ Real.cos (Real.pi * α) = -1/2) :=
    (betaIm_zero_iff α).mp
  ```

  with the docstring at `:117-127`:

  > "(i) `sin(π·α) = 0` — forces `α` to be an integer;
  > (ii) `cos(π·α) = -1/2` — forces `α = 2/3 + 2k` or `α = 4/3 + 2k`.
  > **Neither sub-case includes `α = √2` … or `α = φ + 1/4`.** Therefore the
  > BARE weighted-G_n series alone does **NOT** close the framework's
  > reduction to `16α² − 24α − 11 = 0`."

  **This is a machine-checked refutation of the manuscript's stated derivation
  mechanism** (the reality condition on `G_3(e^{iπα})`). The reality condition,
  as actually written down, excludes both canonical α values. The corpus's
  response is to posit that the "genuine" reduction must instead use a
  fractal-metric kernel with `α^n` inside the cosine — but that route is then
  declared `Prop := True` at `:150` and deferred to `cohen2025pvsnp`.

### 5.2 The `√2` side is not better off

The task asked whether P is derivable while NP is not. **No.** `α_P = √2` has
exactly the same status: `Operators.lean:250` posits `(α_P)² = 2` on the opaque
function; `AlphaCanonical.lean:43` proves `(√2)² = 2` (trivially); the "forcing
reason" is `α_P² = α_YM` with `α_YM := 2` by definition
(`CrossMillenniumSharedInvariants.lean:79`; the "forcing" theorem
`α_P_sq_eq_α_YM` at `:96-99` is proved by `unfold`).
Same circle, one step shorter. The P side is *slightly* cleaner only in that
`α² = 2 ∧ α > 0` looks more natural than `16α² − 24α − 11 = 0`.

### 5.3 The best case for `φ`: real, but not a derivation

`PF/H3CoxeterOrigin.lean` is the strongest motivational material in the corpus
and is worth preserving as *motivation*:

- `H3_Coxeter_number = 10` — genuinely the Coxeter number of H₃ (icosahedral).
- `sin(π/10) = 1/(2φ)` — a genuine classical identity, machine-checked
  (`sin_pi_div_ten_eq_inv_two_phi`, cited in the capstone at `:266-272`).
- H₃ root coordinates genuinely involve φ.

So "φ appears because the substrate's symmetry group is icosahedral, and φ is
the icosahedral constant" is a **defensible heuristic**, and the
`π/10 ↔ H₃ Coxeter number 10` link is a real structural observation, not
numerology.

### 5.4 The best case for `1/4`: numerology

`H3_exponents := [1, 5, 9]` (`H3CoxeterOrigin.lean:78`) — correct, these are
the H₃ exponents. `H3_exponent_gap := 4` (`:84`) — correct, the uniform gap.
Then:

```lean
-- PF/H3CoxeterOrigin.lean:244-248
/-- **α_NP = φ + 1/(H₃ exponent gap) EXACTLY**: `φ + 1/4 = φ + 1/4`. -/
theorem alpha_NP_eq_phi_plus_inv_gap :
    alpha_NP_H3 = goldenRatio + 1 / (H3_exponent_gap : ℝ) := by
  show goldenRatio + 1 / 4 = goldenRatio + 1 / (4 : ℝ)
  norm_num
```

The docstring's own statement of the content — `φ + 1/4 = φ + 1/4` — is the
whole theorem. There is no argument anywhere for **why the reciprocal of the
exponent gap should be *added* to the generator**: not additive vs
multiplicative, not reciprocal vs direct, not gap vs Coxeter number vs
exponent sum. Any of `φ + 4`, `φ/4`, `φ + 1/10`, `φ + 1/15`, `4φ`, `φ^(1/4)`
would be equally "derivable" by this method — and the corpus's own α-table in
fact uses a *different* combining rule per value (α_RH = exponent-sum /
Coxeter-number = 15/10 at `:239-243`; α_NP = φ + 1/gap at `:244-248`).

**Conclusion on the decomposition:** `φ` has a motivation; `1/4` has a
post-hoc pattern-match. The 2025-11-30 audit's Gap 3 ("The 1/4 Term Has No
Derivation") is **still exactly correct** eight months later, and the H₃
material does not close it.

---

## 6. WHAT WOULD CONSTITUTE A GENUINE DERIVATION

A derivation of `α_NP = φ + 1/4` must satisfy **all** of:

1. **Definitional independence.** The construction of `H_NP` (its kernel,
   weight function, measure, domain) must not contain `φ`, `1/4`,
   `φ + 1/4`, `π/(10(φ+1/4))`, or `16x² − 24x − 11` as a parameter. It may
   contain only: the ternary substrate, the encoding, the digital sum `D_3`,
   the certificate weighting `Σ i·D(c_i)`, and free real parameters.
   *→ Currently violated at `p_neq_np_spectral.tex:589`.*

2. **A stated, non-`True` criterion.** The condition selecting α must be a
   real Lean `Prop` about `H_NP` (self-adjointness, trace-class,
   spectral discreteness, or a reality condition on a *derived* generating
   function), not `def C : Prop := True`.
   *→ Currently violated at `PolylogQuadraticDerivation.lean:216`,
   `WeightedDigitalSumGeneratingFunction.lean:150`,
   `EmpiricalAlphaIdent_Substrate_Anchors.lean:154/182/227`.*

3. **The criterion must produce the quadratic**, not consume it. The theorem
   shape must be `Criterion α → 16α² − 24α − 11 = 0`, with `Criterion`
   satisfying (1) and (2). *Every existing theorem has the quadratic as a
   hypothesis.*

4. **Uniqueness in a stated window**, e.g. `∀ α ∈ (1,2), Criterion α → α = φ + 1/4`.

5. **A separate account of the `1/4`** that predicts additivity, reciprocity,
   and the choice of 4, *before* the value is known.

6. **A prediction that is not the value itself.** The derivation should
   determine some *other* observable (a second eigenvalue, a ratio, a
   degeneracy) which is then checked against data not used to fix α.

### Is any route visible?

**No route to (1)–(4) is visible in the corpus, and one plausible route has
been machine-checked to fail.**

- The **bare generating-function route is refuted** (§5.1): the reality
  condition on `G_3(e^{iπα})` admits only integers and `α ≡ ±2/3 (mod 2)`.
  Neither `√2` nor `φ + 1/4`.
- The **fractal-kernel route** (`α^n` inside the cosine) is the corpus's
  proposed replacement, but exists only as `Prop := True` plus a list of three
  absent mathlib prerequisites
  (`WeightedDigitalSumGeneratingFunction.lean:174-186`: Hilbert–Schmidt
  operators on general metric-measure spaces; iterated function systems /
  self-similar measures, "mathlib lacks this entirely"; fractal-recursion
  spectral analysis, "the genuine novel content"). No partial computation of
  this route exists anywhere.
- The **substrate-cascade route** produces `5/4`, which fails the quadratic
  (§2.2).
- The **empirical route** is the closed loop of §2.3 and, taken at face value
  against the actual CSV, does not support the pin (§4).

**The honest statement is: this is asserted, it cannot currently be derived,
and no partial progress toward a derivation exists in the corpus.**

---

## 7. WHAT THIS MEANS FOR THE CORPUS

### 7.1 Where the book/papers currently overclaim

Ranked by severity.

**(1) "The substrate forces α_NP = φ + 1/4 via (I4) + (I10)."**
`millennium_problems_2026-07-13.tex:160`, repeated `:361`, `:926`, `:1295`
("substrate-rigid algebraic fact … immutable, forced by sector-2 minimal
invariants").
**This is circular** (§2.1). I4 and I10 are theorems proved by `unfold` +
`ring` from `α_NP := phi + 1/4`. This is the single most consequential
overclaim in the corpus, because "forced" is doing real rhetorical work
against the "you chose the numbers" objection — and it is precisely the leg
that does not hold.

**(2) The "coefficient-rigidity certificate" / "FOUR-WAY RIGID".**
`millennium_problems_2026-07-13.tex:352`.
The I2-vs-I4 perturbation leg tests the consistency of a statement with
itself. It should be withdrawn or restricted to the legs that are not
self-referential.

**(3) "α-values DERIVED from substrate structure and OVER-DETERMINED by the
algebraic skeleton."** `AlphaValuesFirstPrinciples.lean:294-297`, plus the
file's title and its "Honest scope" marker at `:299-311`.
Nothing in that file is a derivation (§2.2). The file also carries a
*different* P-vs-NP α (5/4) that contradicts the canonical one.

**(4) "EMPIRICAL VALIDATION … matches the IBM Quantum hardware-measured NP
peak EXACTLY."** `CrossMillenniumDerivedConsequences.lean:371-376` (and
`:365-369` for the RH twin).
A `rfl` proof of `phi + 1/4 = phi + 1/4` under an empirical-validation
docstring. Any referee who opens this file will read it as dispositive,
whether or not it was intended that way. **Highest reputational-risk item in
the audit.**

**(5) "13 rows at 16-decimal floating-point precision."**
`millennium_problems_2026-07-13.tex:1279`, load-bearing for the pre-registered
GI threshold at `:1281`/`:1285`.
Falsified by direct check (§4.4): all are 3-decimal values ± 1 ULP.

**(6) "143 problems … each precise to 10 decimal places" (λ₀).**
`Papers/PriorWork_AlphaUniqueness_Nov2025/ALPHA_UNIQUENESS_CERTIFICATION.md`
§1, §5, Appendix C, and the "forced by the spectral data" conclusion in §9.
The dataset has no λ₀ column; the single λ₀ is the closed form; the
"extraction" is the round-trip of §2.3. This document is currently shipped in
`Papers/` and should be retired or prefaced with a correction.

**(7) "Complete proof in [cohen2025pvsnp]."** (Ch 21 §4.2, quoted at
`PolylogEigenvalueClosureAttempt.lean:374`.)
Citing an unpublished self-authored placeholder as the location of a complete
proof, in a paper offered for external review, is not defensible. Either the
manuscript exists and should be released, or the citation must be replaced by
an explicit open-problem marker.

### 7.2 What is *not* an overclaim, and should be protected

- The Lean corpus's **axiom budget** (`zero project axioms`, kernel-only) is,
  as far as this audit can tell, accurate. The circles are not *unsound*; they
  are *uninformative*. Every theorem cited above is true.
- `Operators.lean:190-235` is a model of honest documentation and should be
  the template for the prose. It already says the right thing.
- `bare_route_structural_finding` (§5.1) is a genuine negative result. It
  should be **promoted, not buried** — "we machine-checked the obvious
  derivation route and it provably fails" is real scientific content, and it
  is more credible than any of the forcing claims.
- `SpectralGapInconsistencyAnalysis.lean` likewise: publishing your own
  three-way inconsistency is a strength.
- The H₃ / `sin(π/10) = 1/(2φ)` / Coxeter-number-10 material is a real
  structural observation about where φ and the 10 could come from.

### 7.3 Recommended honest phrasing

Replace every instance of "the substrate **forces** α_NP = φ + 1/4" with:

> **"The framework *posits* α_NP = φ + 1/4. The value is *consistent with* the
> framework's algebraic α-skeleton — indeed it is one of the skeleton's
> defining inputs, not an output — and the H₃ icosahedral structure of the
> substrate supplies a heuristic for the φ term (H₃ generator; the classical
> identity sin(π/10) = 1/(2φ) likewise supplies the coupling's factor of 10).
> **No derivation of the value from the operator's self-adjointness exists.**
> The reality condition on the bare generating function G₃ has been
> machine-checked to *exclude* both canonical α values
> (`bare_route_structural_finding`); the proposed fractal-kernel replacement
> is not formalized and its prerequisites (Hilbert–Schmidt operators on
> metric-measure spaces, IFS / self-similar measures) are absent from mathlib.
> The additive `+1/4` has no derivation; its match to the H₃ exponent gap is a
> post-hoc observation. The empirical anchor is one row of a 142-row
> Aer-simulator panel, at 3-decimal precision, on the row labelled 'P vs NP';
> the panel's α-distribution does not cluster at either canonical value and
> structurally similar NP problems scatter across [1.38, 1.75]."**

And for the no-go, replace "any genuine derivation is P-vs-NP-equivalent"
with:

> **"Assigning *any two distinct* reals to ClassP and ClassNP by a total
> function is equivalent to P ≠ NP (`AlphaRealizationNoGo`). This bounds the
> *distinctness* clause. It does not bound the *value* clause: the difficulty
> of deriving φ + 1/4 specifically is unknown."**

### 7.4 Concrete next actions (priority order)

1. **Retire or re-docstring the two `rfl` "EMPIRICAL VALIDATION" theorems**
   (`CrossMillenniumDerivedConsequences.lean:365-376`). Rename to something
   like `framework_α_NP_defeq_IBMPeaksGaloisPair_alpha_NP` and state in the
   docstring that this is a definitional-consistency check between two copies
   of the same constant, not an empirical claim. *Fifteen minutes; removes the
   single worst referee landmine in the corpus.*
2. **Correct the precision claim** at
   `millennium_problems_2026-07-13.tex:1279/1281/1285` and re-set the GI
   pre-registered tolerance to something the pipeline can actually deliver (or
   state the pipeline upgrade as an explicit prerequisite).
3. **Rename `AlphaValuesFirstPrinciples.lean`** to
   `AlphaValuesStructuralMotivations.lean` and rewrite §10, which currently
   asserts the opposite of what the file proves.
4. **Downgrade "forces" → "posits / is consistent with"** at
   `millennium_problems_2026-07-13.tex:160, 361, 926, 1295`.
5. **Withdraw the I2/I4 leg** of the coefficient-rigidity certificate (`:352`).
6. **Replace the `cohen2025pvsnp` citation** with an explicit open-problem
   marker, or release the manuscript.
7. **Reclassify in `RESIDUAL_TRIAGE`**: split the α-pin into distinctness
   (bucket 3) and value (bucket 2, difficulty *unknown* — not bucket 3).
8. **Promote the negative results.** `bare_route_structural_finding` and
   `SpectralGapInconsistencyAnalysis` are the corpus's most credible content
   on this axis. A short note titled "The obvious derivation of α_NP provably
   fails" would be a genuine, publishable, honest contribution — and it is
   already 90% written in Lean.

---

## 8. SUMMARY TABLE

| Claim | Status | Evidence |
|---|---|---|
| `α_NP = φ + 1/4` is a definition | **YES** | `CrossMillenniumSharedInvariants.lean:70` + 4 others |
| A derivation exists in Lean | **NO** | exhaustive grep; every path ends in `unfold`+`ring` or `Prop := True` |
| A derivation exists in the manuscript | **NO** | `PolylogEigenvalueClosureAttempt.lean:376-382` says so explicitly |
| A derivation exists in `cohen2025pvsnp` | **UNVERIFIABLE — placeholder** | `bibliography.bib:3229` "Unpublished manuscript"; rev2 bib `:3364` calls it a "placeholder entry" |
| The "rigidity" derivation is circular | **YES** | §2.1: inv 10 is `unfold α_NP α_Hodge; ring` |
| The "first-principles" file derives anything | **NO** | §2.2: all `rfl`/`norm_num` |
| The empirical extraction is circular | **YES** | §2.3: `π/(10(φ+1/4))` inserted at `p_neq_np_spectral.tex:589`, recovered at `:625` |
| The bare GF derivation route works | **NO — machine-checked to fail** | `WeightedDigitalSumGeneratingFunction.lean:130` |
| The substrate cascade agrees | **NO — gives 5/4, fails the quadratic** | `PF.lean:94` |
| Deriving the *value* is P-vs-NP-equivalent | **NOT ESTABLISHED** | §3: the no-go is about distinctness only |
| Asserting `α_P ≠ α_NP` (set level) is P-vs-NP-equivalent | **YES** | `AlphaRealizationNoGo.lean:85-108` |
| The 143-problem data supports the pin | **NO** | §4: 1/142 rows; NP-side rows scatter 1.38–1.75; no mode at 1.868 |
| The "16-decimal precision" rows are precise | **NO — ±1 ULP of 3 decimals** | §4.4, verified numerically |
| `φ` has a motivation | **YES (heuristic)** | H₃ icosahedral generator; `sin(π/10) = 1/(2φ)` |
| `1/4` has a motivation | **NO** | §5.4: `φ + 1/4 = φ + 1/4` by `norm_num` |
| The Lean corpus is unsound | **NO** | every theorem cited is true; the problem is that they are uninformative |

---

*Audit performed 2026-07-25, read-only. All file:line references are relative
to `/home/xluxx/Principia-Fractalis`; Lean paths are relative to
`PF_Lean4_Code/`.*
