# Referee-Proof Lean Axiom Audit — Principia Fractalis

**Date**: 2026-06-04
**Auditor**: Programmatic verification under Pabs's direction
**Repository**: `/home/xluxx/Principia-Fractalis/`
**Lean codebase**: `/home/xluxx/Principia-Fractalis/PF_Lean4_Code/`
**Git HEAD at audit time**: `497853de8f46a8f751806af84de87d769c156a87`
  - Commit subject: `HONEST: YM_ClayLiteralClosureAttempt moved to .BROKEN-AGENT-STALLED`
**Toolchain**: Lean 4 via `lake build PF` from `$HOME/.elan/bin/lake`

---

## VERDICT: CLEAN

**Zero project axioms. Zero `sorry` tactics. Zero `admit` tactics.**

Every theorem in the PF build closure that exposes its axiom dependency via `#print axioms` depends only on a subset of the three standard Lean foundational axioms:
`{propext, Classical.choice, Quot.sound}`.

---

## Build State at Audit Time

```
Build completed successfully (4044 jobs).
```

Build produced by:
```
PATH="$HOME/.elan/bin:$PATH" lake build PF
```

Exit code: `0`. Last informational line in the log:
```
info: PF/Referee/CrossMillenniumMetaClosure.lean:678:0: 'PF.Referee.CrossMillenniumMetaClosure.cross_millennium_meta_closure_honest_scope' does not depend on any axioms
```

The 4044 jobs are consistent with the expected count for HEAD `497853d`.

---

## Closure Statistics

| Quantity | Count |
|---|---|
| Total `.lean` files transitively reachable from `PF.lean` | **535** |
| Files present on disk (matched with closure) | **535 (100 %)** |
| Real `axiom` declarations in closure | **0** |
| Real `sorry` tactic occurrences in closure | **0** |
| Real `admit` tactic occurrences in closure | **0** |
| Theorems with `#print axioms` calls in the build log | **2 331** |
| ─ of which depend on `[propext, Classical.choice, Quot.sound]` | 2 126 |
| ─ of which depend on `[propext]` only | 63 |
| ─ of which depend on `[propext, Quot.sound]` | 7 |
| ─ of which depend on `[propext, Classical.choice]` | 3 |
| Theorems printed as "does not depend on any axioms" | 132 |
| **Theorems exposing a non-standard axiom** | **0** |

The four observed axiom-set values are exactly the four allowed subsets of the standard Lean foundational trio. Nothing else appears.

---

## Methodology

### Step 1 — Build the project from a clean state

```bash
cd /home/xluxx/Principia-Fractalis/PF_Lean4_Code
PATH="$HOME/.elan/bin:$PATH" lake build PF 2>&1 > /tmp/pf_build_full.log
```

The build emitted 4 044 jobs and exited `0`. The build log is `6 845` lines.

### Step 2 — Compute the transitive import closure of `PF.lean`

Starting from `PF.lean` and following `^import PF...` lines transitively until fixpoint:

```
Iter 1: 458 -> 511
Iter 2: 511 -> 522
Iter 3: 522 -> 530
Iter 4: 530 -> 533
Iter 5: 533 -> 534
Iter 6: 534 -> 535
Iter 7: 535 -> 535   (fixpoint)
```

Final closure: **535 files**. All 535 confirmed to exist on disk.

### Step 3 — Scan every file in the closure for `axiom`, `sorry`, `admit`

A naive grep finds 12 lines containing the substring `axiom`, 235 lines containing `sorry`, and 89 lines containing `admit`. Each of these was individually inspected.

#### `axiom` — 12 raw hits, **0 real declarations**

A second-pass scan, comment-aware, was performed using the rule: a real `axiom` declaration is a line of the form `axiom <identifier> ...` at the start of the line (after optional whitespace), not inside a `--` line comment and not inside a `/- ... -/` block comment. Result:

```
Real axiom declarations found: 0
```

All 12 raw hits are inside doc-strings or block comments and refer to *retired* axioms, *named-Prop* placeholders that were once axiomatised, or general English commentary. Examples:

- `PF/Analytic/GammaHankel.lean:155` — `"...the polylog-route axiom retirement..."` (prose in doc-string)
- `PF/BochnerMinlos.lean:152` — `"...enable elimination of the gaussian_is_characteristic axiom..."` (doc-string)
- `PF/TuringEncoding/Complexity.lean:79` — `"Retired 2026-05-10 from an axiom to a def..."` (doc-string)
- `PF/YangMillsMeasure.lean:180` — `"the now-retired Bochner-Minlos axiom..."` (doc-string)

None of these are Lean declarations.

#### `sorry` — 235 raw hits, **0 real tactic invocations**

A strict scan was performed for `sorry` actually used as a tactic, defined as one of:

- a line whose trimmed content is exactly `sorry` (with optional trailing comment)
- a line containing `by sorry`, `:= sorry`, or `; sorry` outside a string literal

Result:

```
Strict-tactic sorry occurrences: 0
```

All 235 raw matches are inside doc-strings or comments. The vast majority are explicit *assertions* of the form `"axiom-free, no sorry"`, `"Zero project axioms; ZERO sorry"`, etc. Two interesting outliers worth flagging for clarity:

1. `PF.lean:656` — `"Partially proven with `sorry` placeholders (technical lemmas requiring more work)"`. This is **inside the `/-! ... -/` module docstring spanning lines 592–667**. It is documentation prose, not Lean code. (The status text is also stale relative to the current axiom-free state — see "Documentation note" below.)
2. `PF/Analytic/MaassCuspSimplicityFactorings.lean:14` — historical commentary explaining that a Wave-4 syntax error caused Lean to insert sorry-fallback bodies; the file's lead docstring then states this was fixed and the file builds clean with zero sorries.

Neither is a tactic.

#### `admit` — 89 raw hits, **0 real tactic invocations**

Same strict scan as for `sorry` applied with `admit`. Result:

```
Strict-tactic admit occurrences: 0
```

All 89 raw matches are uses of the English verb "admit" in doc-strings (e.g. "such-and-such admits a modular form companion", "ZERO `admit`"). None is a Lean tactic.

### Step 4 — Direct `#print axioms` evidence from the build log

`lake build` runs every `#print axioms` declaration found in the source. These emit `info:` lines into the build log. The build log was parsed with an AWK script that joins multi-line bracketed axiom lists onto a single line. Result:

- **2 331** total `#print axioms` outputs
- **2 199** of those are `depends on axioms: [...]`
- **132** are `does not depend on any axioms`

Of the 2 199, the distinct bracketed axiom sets are exactly:

```
2126 × [propext, Classical.choice, Quot.sound]
  63 × [propext]
   7 × [propext, Quot.sound]
   3 × [propext, Classical.choice]
```

These are the **only** four sets observed. Each is a subset of the standard Lean foundational trio. **No project axiom appears anywhere.**

### Step 5 — Spot-check the named flagship theorems

For each requested flagship theorem, the build-log `#print axioms` output was located. For the three theorems whose source files do not include a `#print axioms` call (and therefore do not appear in the build log), a temporary standalone file `PF/AuditSpotcheck2026_06_03.lean` was created, run via `lake env lean`, and then deleted.

| # | Theorem | File | Axiom dependency | Status |
|---|---|---|---|---|
| 1 | `PrincipiaFractalisSubstrateTheorem` | `PF/Referee/PrincipiaFractalisSubstrateTheorem.lean:511` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 2 | `PrincipiaFractalisSubstrateConsequences_holds_unconditionally` | `PF/Referee/PrincipiaFractalisSubstrateTheorem.lean:512` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 3 | `cross_millennium_meta_closure_capstone` | `PF/Referee/CrossMillenniumMetaClosure.lean:677` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 4 | `cross_millennium_axis_coupling` | `PF/Referee/CrossMillenniumMetaClosure.lean:667` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 5 | `framework_alpha_values_match_rigidity` | `PF/CrossMillenniumDerivedConsequences.lean:227` | `[propext, Classical.choice, Quot.sound]` | CLEAN (spot-check via `lake env lean`) |
| 6 | `framework_falsifiability_capstone` | `PF/Referee/FrameworkFalsifiabilityConditions.lean:895` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 7 | `alpha_values_first_principles_capstone` | `PF/CrossMillennium/AlphaValuesFirstPrinciples.lean:334` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 8 | `hilbert_polya_implies_RH` | `PF/Analytic/HilbertPolyaIdentificationPrecise.lean:660` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 9 | `ym_continuum_mass_gap_three_halves` | `PF/YM_ContinuumMassGapInfDimWitness.lean:508` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 10 | `pf_hodgeEncoding_FullGeneral_clay_substrate_closure` | `PF/AlgebraicGeometry/Hodge_ClayLiteralClosureAttempt.lean:490` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 11 | `ns_clay_literal_at_zero_axiom_free` | `PF/NavierStokes/NS_ClayLiteralClosureAttempt.lean:673` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 12 | `bsd_rank_one_E37a1_discharged_at_placeholder` | `PF/BSD_HeegnerRank1Proof.lean:568` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 13 | `clay_literal_closure_attempt_capstone` | `PF/PNeqNP_ClayLiteralClosureAttempt.lean:661` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 14 | `pf_razborov_rudich_bypass` | `PF/PNeqNP_ClayLiteralClosureAttempt.lean:651` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 15 | `pf_aaronson_wigderson_bypass` | `PF/PNeqNP_ClayLiteralClosureAttempt.lean:653` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 16 | `naive_vs_observed_ratio_log` | `PF/Cosmology/LambdaCDMRebuttalEnergyConservation.lean:119` | `[propext, Classical.choice, Quot.sound]` | CLEAN (spot-check via `lake env lean`) |
| 17 | `brst_H2_sm_decomposition` | `PF/Consciousness/WeinsteinGUResonantRescue.lean:175` | **does not depend on any axioms** | CLEAN (spot-check via `lake env lean`) |
| 18 | `framework_predicted_alpha_GI_eq_phi_plus_quarter` | `PF/Empirical/Hundred44ProblemPrediction.lean:498` | `[propext, Classical.choice, Quot.sound]` | CLEAN |
| 19 | `sevenMillenniumUnification_realized` | `PF/Referee/SevenMillenniumUnification.lean:109` | `[propext, Classical.choice, Quot.sound]` | CLEAN |

**19/19 flagship theorems CLEAN.** Notable: `brst_H2_sm_decomposition` (which states `78 = 48 + 26 + 4` and is closed by `decide`) requires **no axioms at all** — a purely computational proof.

---

## Files Containing Violations

**None.** No file in the 535-file closure contains a real `axiom` declaration, a `sorry` tactic, or an `admit` tactic.

---

## Verification Reproducibility

A referee can reproduce this audit exactly:

```bash
cd /home/xluxx/Principia-Fractalis/PF_Lean4_Code
git rev-parse HEAD     # must show 497853de8f46a8f751806af84de87d769c156a87
PATH="$HOME/.elan/bin:$PATH" lake build PF 2>&1 | tee /tmp/pf_build.log
# expect: "Build completed successfully (4044 jobs)." on the final line

# Confirm no project axioms (any axiom name outside the standard trio):
grep -E 'depends on axioms:' /tmp/pf_build.log \
  | sed -E 's/.*depends on axioms: \[([^]]*)\].*/\1/' \
  | sed -E 's/[[:space:]]+/ /g; s/^ //; s/ $//' \
  | sort -u
# expect ONLY these four lines (in some order):
#   propext
#   propext, Classical.choice
#   propext, Classical.choice, Quot.sound
#   propext, Quot.sound

# Scan for real axiom declarations in the closure:
# (closure construction = transitive `^import PF...` from PF.lean)
# expect: 0 hits
```

For the three spot-checks not in the build log (`framework_alpha_values_match_rigidity`, `naive_vs_observed_ratio_log`, `brst_H2_sm_decomposition`), the referee can drop the following file into `PF/` and run `lake env lean PF/AuditSpotcheck.lean`:

```lean
import PF.CrossMillenniumDerivedConsequences
import PF.Cosmology.LambdaCDMRebuttalEnergyConservation
import PF.Consciousness.WeinsteinGUResonantRescue

#print axioms PF.CrossMillenniumDerivedConsequences.framework_alpha_values_match_rigidity
#print axioms PrincipiaTractalis.Cosmology.LambdaCDMRebuttal.naive_vs_observed_ratio_log
#print axioms PrincipiaTractalis.WeinsteinGUResonantRescue.brst_H2_sm_decomposition
```

Expected output:

```
'PF.CrossMillenniumDerivedConsequences.framework_alpha_values_match_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrincipiaTractalis.Cosmology.LambdaCDMRebuttal.naive_vs_observed_ratio_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrincipiaTractalis.WeinsteinGUResonantRescue.brst_H2_sm_decomposition' does not depend on any axioms
```

This was the exact output produced during the audit.

---

## Documentation note (non-blocking)

`PF.lean` lines 654–657 (inside the `/-! ## Status -/` module docstring spanning lines 592–667) still read:

```
- ✓ Fully proven theorems (marked with `theorem` and complete proofs)
- ⚠️ Partially proven with `sorry` placeholders (technical lemmas requiring more work)
- 📋 Axioms for numerical constants (externally verified at 100+ digit precision)
```

This text is **factually stale**. As of HEAD `497853d`, the build has zero `sorry` placeholders and zero project axioms. The status block was accurate at an earlier point in the project's history and was never updated. This is purely a documentation accuracy issue — it does not affect the verification status of any theorem and the audit's machine-checked findings are independent of it. Recommend a single-commit edit at some point to bring the status block into agreement with the current `#print axioms` evidence.

---

## Summary verdict

**VERDICT: CLEAN.**

- 535 files in PF build closure
- 4 044 build jobs, exit 0
- 0 project axioms
- 0 `sorry` tactics
- 0 `admit` tactics
- 2 331 `#print axioms` outputs, of which 0 mention any non-standard axiom
- 19 / 19 flagship spot-checks verified clean
- All axiom dependencies are subsets of the standard Lean trio `{propext, Classical.choice, Quot.sound}`

The framework's claim that its axiom-free attack landings are genuinely axiom-free is **kernel-level certified** by this audit.
