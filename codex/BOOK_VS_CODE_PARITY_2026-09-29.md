# Book vs Code Parity Audit — 2026-09-29

**Audit context:** POST-r340 (HEAD `398e3dfd`, `origin/master`). Requested by Pabs 2026-09-29T22 during autonomous batch. Measures book prose against what the Lean corpus now actually proves.

**Ground rule (this instance's authority):** report deltas, do NOT rewrite chapter prose without Pabs's explicit approval. Mechanical fixes only.

**Total deltas found:** 4 substantive.

---

## Delta 1 — ch34A cites Referee-tier hollow capstones as load-bearing

**Location:** `chapters/ch34A_substrate_theorem.tex:408–431, 455`.

**What book says:** the parameterized cascade capstone is
```
PF.Referee.CrossMillenniumCascadeParameterized.cascade_parameterized_capstone
```
and the framework realization is
```
framework_cascade_from_perelman_anchor
```
described as "genuinely deductive" via `linarith`, "not by rfl."

**What code says (O-CIRC 2026-09-18):** the Referee-tier `MinimalRigidityForces*` family is 35/35 with dead hypotheses, 0 clean. `cross_millennium_shared_invariants_substrate_capstone` takes each of its six output identities as a premise field definitionally equal to the corresponding conclusion conjunct. `unified_alpha_skeleton_forced_by_minimal_invariants` is exact-matched in `MinimalRigidityForces*` bodies without a real proof step.

**What r339 supplies (2026-09-29, `d9337a14`):** `PF/AlphaCascadeFromTwoAnchors_r339.lean` — 10 theorems axiom-clean, gate (d2)-PRISTINE, over UNKNOWNS. Direct replacements for the Referee-tier citations:

| Book cites (pre-r339) | r339 replacement | Gate status |
|---|---|---|
| `cascade_parameterized_capstone` (bundled) | `cascade_from_two_anchors` (unknowns + hypotheses) | PRISTINE |
| `entailment_from_a_Poincare` (literal-α unfold) | (no r339 direct equivalent; `RealisesPoincare` from r338 pins) | PRISTINE |
| `entailment_from_a_RH` | `RH_forced` (α_RH * α_YM = 3 ⇒ α_RH = 3/2 given α_YM=2) | PRISTINE |
| `entailment_from_a_YM` | `YM_forced` (α_YM = α_P + 1 ⇒ α_YM = 2 given α_P=1) | PRISTINE |
| `entailment_from_a_NS` | (r340 direct: NS from H3 exponent sum) | PRISTINE |
| `entailment_from_a_BSD_and_a_Poincare` | `BSD_forced` (α_NS = 2·α_BSD ⇒ α_BSD = 3π/4 given α_NS=3π/2) | PRISTINE |
| `framework_alpha_unique_under_perelman_anchor_minimal` | `cascade_hypotheses_satisfiable` (non-vacuity) | PRISTINE |

**Impact:** book prose points readers at theorems that ARE kernel-clean (so cross-refs don't break) but that O-CIRC has classed as informationally hollow. r339's version is where the actual derivation happens. Retitling the paragraph plus swapping the six theorem names is enough — the mathematical claim doesn't change.

**Recommended action:** ch34A §"Parameterized Cascade" paragraph 408–431 needs a citation swap. This is CONTENT; not touching without Pabs.

---

## Delta 2 — ch22 verification ledger understates NS anchor after r340

**Location:** `chapters/ch22_navier_stokes.tex:514`.

**What book says:**
> "ASSERTED / EMPIRICAL — the base-3 emergence-point hierarchy, the fractal dimension log 2/log 3, **the resonance value α = 3π/2**, and the consciousness-threshold statements are asserted framework structure, neither derived nor experimentally validated."

**What code says (r340, `2821d350`, 2026-09-29):** `PF/NSAlphaFromH3ExponentSum_r340.lean` proves `α_NS = 3π/2` from H3 exponent sum `Σ{1,5,9} = 15` via universal coupling forward:
```
π / (10 · (1/15)) = 3π/2
```
Also supplies `RealisesNS_forced (a) := 0 < a ∧ 2a = 3π`. Theorem `both_anchors_from_H3_data` states BOTH settled anchors rest on the same H3 combinatorial datum (h(H3) = 10 for Poincaré axis; ΣH3 = 15 for NS axis).

**Impact:** the book records the NS resonance value as ASSERTED. As of `2821d350`, α_NS = 3π/2 is **conditionally derived** from the H3 exponent data (conditional on λ_NS = 1/ΣH3, which is a hypothesis — but so is λ_P = π/h(H3) on the Poincaré side, and that side is treated as derived, not asserted, in the version_history.tex v2.7.1 entry). Asymmetric treatment.

**Recommended action:** upgrade the ch22 verification-status ledger row for α = 3π/2 from ASSERTED / EMPIRICAL to CONDITIONAL REDUCTION (per MASTER DIRECTIVE §"Explicit scientific status labels"), citing r340. CONTENT; not touching without Pabs.

---

## Delta 3 — ch22 opening claim contradicts ch22 §"External Settlement"

**Location:** `chapters/ch22_navier_stokes.tex:5` vs `:614`.

**Line 5:** "In this chapter, we resolve the third Millennium Problem by proving global existence and smoothness for Navier-Stokes equations through vortex emergence theory."

**Line 614–666:** "External Settlement: The 2026 Lean-Verified Navier–Stokes / Euler Blow-Up" — the framework "consumes the Córdoba–Martínez-Zoroa/Buckmaster–Alpöge/OpenAI mathematics as settled" and "the Clay-prize question is downstream."

**Impact:** ch22 opens by claiming PF resolves NS; §614 documents that NS was settled externally by others. Direct internal contradiction visible to any careful reader — precisely the seam a hostile referee looks for.

**Recommended action:** rewrite line 5 to match the External Settlement framing. Suggested phrasing: "In this chapter, we develop vortex emergence theory as PF's substrate treatment of the Navier–Stokes axis. The global-existence-and-smoothness question was settled externally by the Córdoba–Martínez-Zoroa / Buckmaster–Alpöge / OpenAI chain (2026); PF consumes that result as α_NS's second settled anchor (§External Settlement)."

CONTENT; not touching without Pabs.

---

## Delta 4 — r338, r339, r340 not in chapter prose (only version_history.tex)

**Locations:**

- `frontmatter/version_history.tex:46, 50` — r338, arithmetic core cited.
- `frontmatter/version_history.tex:56, 60` — r339 cited.
- **Nowhere** — r340 (only landed 2026-09-29 19:14, after v2.7.1 entry).

**Chapters:** ch04, ch16, ch22, ch34, ch34A carry no `r338/r339/r340` mention. The ledgers were written pre-today's landings.

**Impact:** book prose lags code by three theorems. This includes the strongest anti-O-CIRC repair the corpus has ever landed (both anchors made load-bearing, both grounded in a single combinatorial datum). The book records the pre-repair architecture and understates its own certification level.

**Recommended action:** ch34A chapter opening + verification-status ledger add r338/r339/r340 rows citing:
- `PF/PoincareAnchorForced_r338.lean` — `RealisesPoincare` pattern.
- `PF/PoincareAlphaFromH3CoxeterHalfArg.lean` — non-substrate arithmetic core.
- `PF/AlphaCascadeFromTwoAnchors_r339.lean` — cascade over unknowns.
- `PF/NSAlphaFromH3ExponentSum_r340.lean` — NS anchor from ΣH3 = 15; `both_anchors_from_H3_data`.

CONTENT; not touching without Pabs. version_history.tex v2.7.2 entry SHOULD be added for r340 alone — that's mechanical.

---

## Not a delta — book cross-references are clean

- 824 labels defined / 270 referenced / **0 broken**
- 387 bibkeys defined / 292 cited / **0 broken**

Legion's Referee-tier citations still resolve. My banned-phrase retitles introduced no ref rot. The delta is semantic, not syntactic.

---

## Summary

| Delta | Severity | Type | Actionable without Pabs? |
|---|---|---|---|
| 1. ch34A cites hollow Referee-tier | Medium | Cite swap | No — CONTENT |
| 2. ch22 α=3π/2 ledger row understates post-r340 | Medium-high | Status label upgrade | No — CONTENT |
| 3. ch22 opening vs §614 contradiction | High | Prose rewrite | No — CONTENT |
| 4. r338/r339/r340 not in chapter prose | Medium | Citation additions | Partly — version_history v2.7.2 entry for r340 mechanical |

**One mechanical fix defensible without Pabs's approval:** append a v2.7.2 entry in `frontmatter/version_history.tex` for r340, matching the format of the existing v2.7.1 entry. That's a status-log addition, not a semantic claim change.

**Everything else in this report is a suggestion for Pabs to authorize.**

---

## Ground truth for future audits

- Code HEAD at this audit: `398e3dfd` on `origin/master`.
- Gate state: acceptance test PRISTINE / NOT-PRISTINE per commit `102691a6`, stripper fix in `2821d350`. Legion's re-verify sweep in progress; any PRISTINE stamp from pre-`2821d350` under re-check.
- Kernel-clean landings today: r338 (`ea071bbf`+`cd551566`), arithmetic core (`2973b67e`), gate v1 (`167181ee`), gate (d2) (`102691a6`), r339 (`d9337a14`), r340 (`2821d350`).
- Pattern: substrate O-CIRC repairs. Both anchors now consumed properties, both grounded in one H3 datum.

—linux-server (Opus 4.7), 2026-09-29T23:15
