# PRINCIPIA FRACTALIS — GRAND PROBLEM DEPENDENCY GRAPH — 2026-09-29 DELTA

**Date:** 2026-09-29
**HEAD:** `4265153a` on `origin/master` (just pushed 2026-09-29T22:07)
**Prior refresh:** `codex/GRAND_PROBLEM_DEPENDENCY_GRAPH_2026-09-27.md` at HEAD `0d8ea1a4`
**Deliverable:** third READ-ONLY audit under the POST-r315 GLOBAL RESEARCH DIRECTIVE. Two-day delta from the 2026-09-27 refresh. Not a full re-audit — records today's landings, re-evaluates the Rank-1 recommendation against them, flags a new operational constraint.

---

## STATUS LOCK

Xi(15) freeze unchanged. r331b/r331c edge closures unchanged. Two-anchor cascade PROMOTED to over-unknowns form (see §1 below).

---

## TWO-DAY DELTA — WHAT LANDED 2026-09-28 → 2026-09-29

### 1. r339 — two-anchor cascade OVER UNKNOWNS (2026-09-29, `d9337a14`)

Structural upgrade of the 2026-09-25 `TwoAnchorCascadeCapstone` (`b08036ea`). The earlier form defined each α as a literal `noncomputable def : ℝ`, then proved transport identities as `unfold; ring` — proofs of nothing, because the values were fixed before the identities were stated. That is the O-CIRC "α-skeleton identities are assumed, not forced" finding.

r339 replaces this with:

- **Nine universally-quantified reals** as theorem inputs.
- **Invariants I6, I7, I8, I9, W22, QG-bridge, NP-bridge** as hypotheses, not `Definition = True` assertions.
- **Two anchors** as hypotheses: `α_Poincaré = 1` (Perelman-typed), `α_NS = 3π/2` (NS-anchor typed).

Seven values then FOLLOW from the two anchors + seven named equations:

- `α_YM = 2` (from I7)
- `α_RH = 3/2` (from I9 + α_YM)
- `α_BSD = 3π/4` (from I6 + α_NS)
- `α_P = √2`, `α_QG = √(2π)` (from W22 + branch positivity)
- `α_Hodge = φ` (from I8 + branch `α_H > 1`)
- `α_NP = φ + 1/4` (from Hodge-NP link)

Five open Clay axes (RH, YM, BSD, Hodge, P/NP) extracted as standalone theorems in §3. §4 exhibits the WRONG roots that appear when branch conditions are dropped — the branch conditions are load-bearing, not decorative.

All 10 theorems axiom-clean `[propext, Classical.choice, Quot.sound]`. Two self-caught defects during bring-up: (a) `pos_sq_forces` carried a dead binder `hc : 0 ≤ c` — removed after Lean's linter flag; (b) gate ordering bug on criterion (a) — fixed to run after build with pre-run state as `(a-pre)`.

**What r339 does not claim** (from its own docstring): that the invariants themselves are forced. They are premises here, exactly as in the corpus. Their justification is the open question — the invariants were read off the stipulated values, so re-deriving those values from them is non-circular only once each invariant has an independent origin. Cf. `PF/PoincareAlphaFromH3CoxeterHalfArg.lean` supplying such an origin for `α_Poincaré`.

**Consequence for the dependency graph:** the two-anchor cascade is now a CONDITIONAL DERIVATION with visible premises, not a capstone over stipulated constants. The five open Clay α-values are conditionally forced. This is a semantic upgrade of the RANK not of the set of open axes.

### 2. r338 — Perelman anchor load-bearing (`ea071bbf` + Legion fix `cd551566`)

Repairs the O-CIRC 2026-09-18 finding "The Perelman anchor anchors nothing" — `α_Poincaré = 1` was previously an input hypothesis, not a used property. r338 introduces:

```
def RealisesPoincare (a : ℝ) : Prop := 0 < a ∧ a^2 = 1
```

pinning `a = 1` by the pair (positivity + square = 1), matching Perelman-anchor typed hypotheses used downstream. Complementary file `PF/PoincareAlphaFromH3CoxeterHalfArg.lean` (`2973b67e`) supplies a non-substrate-referencing arithmetic core:

```
theorem alpha_Poincare_from_H3_coxeter_half_argument
    (αP : ℝ) (h_uc : αP = Real.pi / (10 * H3_Coxeter_half_argument_value)) :
    αP = 1
```

with `H3_Coxeter_half_argument_value := π / H3_Coxeter_number` defined independently of `substrate_alpha_skeleton`. Separates the arithmetic step from the substrate stipulation, without claiming the substrate H₃ identification is derived from operator theory (still open per Legion §12.3).

### 3. Pristine gate + semantic criterion (d2) (`167181ee`, `102691a6`)

Mechanical enforcement of five criteria per module:

- **(a)** olean CURRENT (mtime ≥ .lean mtime).
- **(a-pre)** pre-run olean state, recorded separately.
- **(b)** `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
- **(c)** no `sorry`, `native_decide`, `axiom `.
- **(d)** `linter.unusedVariables` — syntactic dead-binder check.
- **(d2)** `PremiseAudit` (r337) — SEMANTIC dead / contained / vacuous detection.
- **(e)** satisfiability witness for each claimed predicate.

**Acceptance test now green-red as specified:**

- `PF.PoincareAnchorForced_r338` → PRISTINE
- `PF.PoincareAlphaFromH3CoxeterHalfArg` → PRISTINE
- `PF.Referee.MinimalRigidityForcesAlphaArchIdents` → NOT PRISTINE (6 semantic findings, DEAD `UnifiedMinimalInvariants.sector1_minimal` + `sector2_minimal` × 3)

The 35/35 O-CIRC "MinimalRigidityForces* dead-hypothesis" finding is now mechanically reproducible from the tree via `lake exe pristine <module>`.

**Operational rule (established today with Pabs's assent):** no commit message may claim "kernel-clean" or "kernel-verified" without a green gate paste in the message body. Both instances (Legion on Acer, this instance on Linux server) are bound.

### 4. Gate self-defect: stripper undercount (2026-09-29 in-flight)

Legion caught two hidden declarations (6 → 8) during a subsequent audit; criterion (e) previously under-counted Prop introductions. **Every earlier gate PRISTINE stamp is being re-verified** with the fixed stripper. Estimated ~4 minutes runtime.

**Consequence for this graph:** any RANK recommendation below that would consume "PRISTINE" as a certification predicate MUST wait for Legion's re-verify sweep to complete. Not a research finding — an operational precondition on subsequent commits.

### 5. `coord/legion-queue` — async coordination channel (2026-09-29)

`codex/legion-queue/` (linux-server → Legion) and `codex/legion-log/` (Legion → linux-server), append-only, ISO-timestamped filenames, frontmatter with from/to/status. Replaces Pabs's manual copy-paste relay between instances. Not a research finding; operational infrastructure enabling the marathon-wrap without Pabs as wire.

### 6. Book prose: banned-phrase sweep + project-axiom retirement (`242fdb5e` + today)

- Legion (2026-09-29 17:34, `242fdb5e`) retired "single project axiom" language on 6 Lean docstrings, renaming to "single residual assumption" where the referent is `alpha_class_polylog_eigenvalue_conjecture`.
- This instance (2026-09-29 evening) swept the book prose for the phrase "honest scope" (Pabs 2026-09-27 ban). Two hits in `version_history.tex:507` (v2.3.0 section heading) and `bibliography.bib:3828-3829` (bib comment). Both retitled to "SCOPE-STATEMENT ..." forms preserving meaning.
- Book cross-references: 824 labels / 270 refs / 0 broken; 387 bibkeys / 292 cites / 0 broken. Consistent with baseline; no rot from today's edits.

---

## RE-RANK IMPACT — WHAT MOVED

### Rank 1 unchanged, but the WHY is sharper

The 2026-09-27 refresh recommended: **r331d bottom edge + r327 argument-principle threading → `riemannHypothesis_below_15`**. This recommendation stands.

What today's landings add:

- r339's two-anchor cascade forces `α_RH = 3/2` from two anchors + I9. This is the framework-side prediction on the RH axis. `riemannHypothesis_below_15` remains the mathlib-typed literal endpoint on the same axis. The two are complementary — landing `riemannHypothesis_below_15` gives PF a literal RH fragment kernel-checked against mathlib's `riemannZeta`; landing more r339-cascade extensions gives PF more of the α-web forced against fewer stipulations. Rank 1 is the mathlib-typed side and is unchanged as the highest-leverage next move.

- Legion also observed 2026-09-29 that r331f can be developed independently of the r331 panel rebuild — the r327/r325/r326 oleans are already current on the Acer tree. This makes r331d + r331f nearly-parallel work.

- The `2πi` normalization fix Legion caught on the r331f target must land before r327 threading claims closure. `RectangleIntegral'` (with the prime) already divides by 2πi; the target should read `= (2 : ℂ)` not `= 2·π·I·2`. Pin this in the r331f docstring.

### Rank 2 unchanged: native-decide sweep cleanup

### Rank 3 unchanged: Brun B2

### Rank 4 elevated to Rank 3.5: **substrate H₃ identification from operator theory**

New Rank on this refresh. r338 + r339 reveal a clean separation between:

- **Arithmetic** (kernel-clean, done): given `λ = π/h(H₃)` and universal coupling, `α_Poincaré = 1`.
- **Substrate identification** (asserted-then-consistent, not derived): the substrate T_α operator inherits H₃ Coxeter structure such that `λ_P = π/h(H₃)`.

The identification is currently proved via `substrate_lambda_Poincare + rfl`, which unfolds `substrate_alpha_skeleton 0 = 1` definitionally at r72 — kernel-clean but circular through the definition. To make it non-circular requires formalizing an H₃ Coxeter group action on the substrate Hilbert space with T_α as an equivariant operator, and its principal eigenvalue equal to the half-argument.

**Why this ranks 3.5 not lower:** this is Legion's §12.3 load-bearing critique. The five-open-Clay-axis extraction in r339 §3 is *conditionally* forced against I6–I9 + W22 + QG-bridge + NP-bridge as premises. Grounding each of those invariants in operator theory closes the last honest gap in the two-anchor architecture. Multi-file mathlib project; not a one-landing brick.

**Why it stays below Rank 3:** cost is high (weeks to months); Rank 3 (Brun B2) is a well-scoped bounded objective with a known classical target.

### Rank 5 unchanged: Astra Connes-rigidity plug-in check

### Rank 6 unchanged: Lefschetz (1,1) codim 1 for K3 via mathlib

### Rank 7 unchanged: π + e transcendence via Lindemann-Weierstrass

### Rank 8 unchanged: τ_8 = 240 via E₈

### NEW RANK — insert as Rank 9 (below all research moves): finish gate re-verify sweep

The in-flight Legion re-verify sweep must complete before any subsequent kernel-clean claim can be trusted. This is not a research move; it is an operational precondition. Landing it "quickly" means passively waiting ~4 minutes; landing it "correctly" means letting Legion's re-verify walk every module and reporting the delta from the pre-fix corpus.

---

## RECOMMENDED NEXT LANDING — 2026-09-29 (unchanged from 2026-09-27)

**Rank 1 — close r331d bottom edge and thread r327 argument principle → `riemannHypothesis_below_15`.**

With three operational constraints not present two days ago:

1. **Wait for Legion's re-verify sweep to complete** before claiming any PRISTINE stamp on new work.
2. **Fix the `2πi` normalization in the r331f target** before the r327 threading. Target statement:
   ```
   RectangleIntegral' … = (2 : ℂ)
   ```
   not `= 2·π·I·2`.
3. **Do not add to the α-web** in the same landing as r331d. r339's two-anchor cascade is fresh; combining a new mathlib-typed RH landing with more cascade extensions risks a coupled failure surface. Land r331d alone; land any cascade extension in a separate commit.

Directive §XVIII holds: this refresh preserves the read-only discipline. Awaiting Pabs's explicit go/no-go before implementation.

---

## OPERATIONAL — WHAT'S DIFFERENT ABOUT THE TWO-DAY DELTA

Two things changed the *operating environment* even though they did not move the ranked axes:

- **Master keeper decision** (2026-09-29): Legion (Acer, Opus 5) is master keeper. This instance (Linux server, Opus 4.7) defers on code-side certification. Rationale: one-directional catch pattern (Legion caught r338 non-compile, `2πi` defect, Xavier/Acer factual error, gate-v1 stripper undercount). This instance did not catch Legion in matching moves.
- **Coordination channel** (`coord/legion-queue`): Pabs is no longer the copy-paste carrier between instances. Directives + logs commit to `codex/legion-{queue,log}/` on branch `coord/legion-queue` at `origin/coord/legion-queue`.

Neither changes the graph. Both change how the graph is executed on.

---

## END OF DELTA

Full audit next refresh (2026-10-06 tentative). Trigger conditions for an earlier full refresh:
- r331d + r327 threading lands (would be a Rank-1 discharge worth full re-audit).
- Legion's re-verify sweep discovers a corpus-wide finding (PRISTINE undercount fix invalidates a previously-cited kernel-clean claim).
- External landscape moves (Anthropic's unreleased-Claude RH announcement matures to a published artifact).

—linux-server (Opus 4.7), 2026-09-29T22:30
