# PF ToE Diagram — Gap Audit (2026-11-15)

**Target:** `codex/pf_toe_diagram.{html,pdf}` + `codex/PRINCIPIA_FRACTALIS_FULL_DIAGRAM_2026-11-14.md` + Appendix M (`appendices/appM_toe_diagram_2026-11-15.tex`) embedded in the book.
**HEAD at audit:** `0c8e07fe` on `origin/master`.
**Method:** diagram claims cross-checked against actual corpus state (file existence + theorem names + git log + `revision2_changes.tex`).

---

## Summary

Six confirmed gaps — three are hard misses (diagram asserts something false), three are overclaims or stale numbers. Everything else the diagram says is accurate. The book has already been rebuilt with the diagram embedded as Appendix M (`0c8e07fe`, `main.pdf` 1044 pages), so these fixes would land as a second pass.

| # | Severity | Issue | Diagram says | Actual state |
|---|----------|-------|--------------|--------------|
| 1 | **HARD MISS** | `StandardNS3DStatement.lean` listed, missing on disk | diagram §12, Section 7 file-map lists `StandardNS3DStatement.lean` | file does not exist. `StandardNS3DEncoding` + `Clay_NavierStokes_Standard` live in `PF/Referee/StandardClayStatements.lean` (shared file) |
| 2 | **STALE** | Lean file count way off | "8,591 Lean files total" (§9 + §11 + appendix M prose) | `find PF_Lean4_Code/PF -name '*.lean'` returns **10,774** (off by ~2,183) |
| 3 | **STALE** | Wave count overstated | "41 Wave MasterCapstone waves 18–58" (§10) | **36 files** on disk. Waves 18, 21, 23–24, 26–58 with 36/37 merged into one file. Missing: 19, 20, 22, 25 |
| 4 | **STALE** | Phantom commit SHA | "Legion box march to 829/64 … commit `2d6919ea`" (§4 RH box) | `2d6919ea` not reachable in current git log (rebased/squashed away) |
| 5 | **OVERCLAIM** | Consciousness label color | ch₂ = 19/20 labeled green **PROVEN** in diagram (§6 and §11 summary row) | `revision2_changes.tex` L103–105 explicitly labels the consciousness threshold and all consciousness quantifications as **"empirical hypotheses — untested"** |
| 6 | **UNDERCLAIM** | Invariant count right, wrong list | "Fifteen cross-Millennium invariants" (§3) with 15 enumerated | `CrossMillenniumSharedInvariants.lean` has **15 identity theorems** (plus 1 aggregator + 1 remark). Count matches, but 4 identities in the Lean file are not in the diagram's enumeration: `α_Poincare_mul_YM_eq_α_P_sq`, `α_NP_add_Hodge_form`, `α_QG_sq_eq_four_thirds_α_NS`, `α_QG_sq_eq_eight_thirds_α_BSD`. Diagram lists 4 items (12, 13, 14, 15) that aren't single identity theorems — they're descriptive meta-items (resonance-period identities, H₃ bridge, exponent sum, parametric uniqueness) |

**What is confirmed solid** (agent flagged these; direct Lean grep refuted the flags):

- `fermat42Double_impossible_unconditional` — exists at `PF/Fermat42DoubleImpossible_2026_11_13.lean:1196`
- `vortexStretchingBoundedHypothesis_holds` — exists at `PF/NS3DVortexStretchingBoundedDischarge.lean:58`
- `PF_NS_capstone_substrate_yields_Clay_NavierStokes_standard` — exists at `PF/Referee/NavierStokesCapstoneTypedBridgeSubstrate.lean:80`
- The nine α-constants are all defined in `PF/CrossMillenniumSharedInvariants.lean`
- Two exact rank-0 BSD curves + five rank-≥1 curves — files all exist
- `T_infinity_rigidity`, `pi_not_ktheoretic_ratio`, Wilson RP (continuous + L²), per-Galerkin-n NS discharge — all exist

---

## Hard misses (fix before next referee pass)

### H1 — Missing `StandardNS3DStatement.lean`

**Diagram claim** (`codex/PRINCIPIA_FRACTALIS_FULL_DIAGRAM_2026-11-14.md` §7 file-map, and `codex/pf_toe_diagram.html` §12 file-map):
```
├── StandardNS3DStatement.lean               — NS substrate encoding
```
and the companion `NavierStokesCapstoneTypedBridgeSubstrate.lean`.

**Actual state:** `PF/Referee/StandardNS3DStatement.lean` and `PF/Referee/StandardNS3DSubstrateStatement.lean` both absent.

**What's actually there:** `PF/Referee/StandardClayStatements.lean` contains `structure StandardNS3DEncoding` (L63) and `def Clay_NavierStokes_Standard` (L73). This is the shared Clay-statements file that holds all the typed-Clay encodings for the NS axis.

**Why it's a hard miss:** the diagram lists Fermat, RH, PvsNP, YM, BSD, Hodge, Poincaré as each having their own `Standard…Statement.lean` file (which is true on disk), but NS doesn't — it lives in the shared file. A referee grepping for `StandardNS3DStatement.lean` gets zero hits.

**Fix options:**
- **(A)** Create `PF/Referee/StandardNS3DSubstrateStatement.lean` that `import`s + `export`s the relevant pieces from `StandardClayStatements.lean` (minimal, matches the symmetry of the other seven axes).
- **(B)** Update the diagram and Appendix M file-map to point at `StandardClayStatements.lean` for the NS axis.

**(A) is more honest** (keeps the symmetry the diagram claims), but requires a one-line Lean change + rebuild of the book. **(B) is a doc-only fix**.

### H2 — Commit `2d6919ea` not reachable

**Diagram claim** (§4 RH pillar + §11 summary table):
> "Legion box march (UNCONDITIONAL): zero-free {0 ≤ σ ≤ 1, 0 ≤ t ≤ 829/64} commit `2d6919ea`, 2026-11-10"

**Actual state:** `git log --all 2d6919ea` returns `unknown revision`. The SHA was rebased, squashed, or never existed.

**Fix:** find the current head commit that carries the Legion march landing, substitute that SHA. If the march moved beyond 829/64, update the frontier too.

### H3 — Lean file count stale

**Diagram claim** (`§9`, `§11`, and the Appendix M prose): "8,591 Lean files total" + "933 of 1,477 pass FULL gate" + "across all 8,591: 0 sorry etc."

**Actual state:** `find PF_Lean4_Code/PF -name '*.lean' -not -path '*/.lake/*' | wc -l` = **10,774**.

**Why it matters:** the "0 sorry across 8,591" claim is an audit statement. If the corpus has grown by 2,183 files since that audit, the 0-sorry claim is no longer testified for the extra files.

**Fix:** either re-run the full-corpus audit at current HEAD and update the three places that cite 8,591, or add a timestamp qualification ("as of the 8,591-file audit at commit X").

---

## Overclaim (fix the color)

### O1 — Consciousness threshold labeled PROVEN but should be EMPIRICAL

**Diagram claim** (`§6` and `§11` summary row "Consciousness ch₂ = 19/20"):
- Node box: green **PROVEN** fill, legend-color-coded as "kernel-verified, three-axiom bar"
- Summary row status: `<span class="tag tag-proven">PROVEN</span> (anchor)`
- Prose: "ch₂ = 19/20 = 0.95 decoherence threshold PROVEN as framework anchor"

**Actual state** (`frontmatter/revision2_changes.tex` L103–105, verbatim):
> "consciousness threshold ch₂ ≥ 0.95, the clinical accuracy figures, and all consciousness quantifications are **empirical hypotheses — untested**: they await experiment and are not established by any computation in this book."

**Why it's an overclaim:** the diagram's green PROVEN color communicates "kernel-verified on the three-axiom bar" to a referee. The book's own authoritative scope document explicitly disclaims this. The threshold value 19/20 appears in Lean as a constant, but the claim that physical/clinical decoherence occurs at this value is empirical.

**Fix:** recolor the Consciousness nodes in `§6` and the Consciousness row in the `§11` summary table from PROVEN (green) to EMPIRICAL — UNTESTED (purple). The label "framework anchor" can stay as a secondary qualifier.

Same scrutiny likely applies to Weinstein-GU rescue (C16, `|Ψ|² = ch₂ = 0.95`) which currently reads PROVEN but inherits the ch₂ empirical status.

---

## Underclaim (optional)

### U1 — Invariants list doesn't match the Lean file

Diagram lists invariants 12–15 as descriptive items ("resonance-period identities", "H₃ Coxeter h = 10 → α_Poincaré", "Σ(H₃ exponents) = 15 → α_NS", "constraint-satisfaction + parametric uniqueness") — these aren't the actual theorems in `CrossMillenniumSharedInvariants.lean`. The file's extra identity theorems not in the diagram:

```
α_Poincare_mul_YM_eq_α_P_sq      α_Poincaré · α_YM = α_P²
α_NP_add_Hodge_form               α_NP + α_Hodge = 2·α_Hodge + 1/4
α_QG_sq_eq_four_thirds_α_NS       α_QG² = (4/3) · α_NS
α_QG_sq_eq_eight_thirds_α_BSD     α_QG² = (8/3) · α_BSD
```

**Fix** (if we want strict correspondence): swap the four descriptive meta-items for these four extra identity theorems. Alternatively, keep both and list the Lean file's 15 identity theorems separately from the 4 descriptive meta-relations.

### U2 — Referee directory is 140 files, diagram names 15

Not a gap — the diagram is intentionally selective — but worth a sentence in Appendix M's prose: "the typed capstone family listed here is the externally-facing eight-axis slice; the full `PF/Referee/` directory contains 140 files including multi-version iterations, meta-aggregators, and intermediate bridges."

---

## Honest grade

With H1 + H2 + H3 fixed and O1 recolored, the diagram is defensible under hostile-referee review. Current state scores **~70%** on honesty: core structural claims (substrate rigidity, K-theoretic obstruction, α-skeleton, invariants, typed capstones) all land, but the three factual inaccuracies (missing file, phantom commit SHA, stale file count) and one label miscolor (consciousness) are things a referee would catch immediately.

**None of the Clay-axis capstones are actually broken by these findings.** The six open Clays + Poincaré + Fermat typed-contract discharges exist and are on the three-axiom bar. The gaps are in the surrounding referee-facing documentation, not in the Lean kernel.

---

## Action list (for the next pass)

1. **H1** — decide between (A) create `PF/Referee/StandardNS3DSubstrateStatement.lean` re-export OR (B) update diagram file-map. (A) is ~10 Lean lines. (B) is a doc edit.
2. **H2** — find current Legion-march head commit, substitute SHA in diagram §4 + §11 + anywhere else `2d6919ea` appears.
3. **H3** — either re-run the full-corpus audit at current HEAD and update "8,591" → current number in diagram §9, §11, Appendix M prose, `revision2_changes.tex`; or add a timestamp qualification.
4. **O1** — recolor Consciousness ch₂ nodes from PROVEN to EMPIRICAL in `§6` and `§11` summary row; mention the scope caveat the book's `revision2_changes.tex` already carries.
5. **(optional) U1** — align the invariants enumeration with the actual `CrossMillenniumSharedInvariants.lean` identity list.
6. After edits: re-run `./codex/pf_toe_diagram_render.sh` → regenerate PDF → copy to `figures/pf_toe_diagram_2026_11_15.pdf` → rebuild `main.pdf` → commit.
