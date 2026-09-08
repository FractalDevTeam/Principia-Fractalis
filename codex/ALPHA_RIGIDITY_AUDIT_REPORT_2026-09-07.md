# α-SKELETON RIGIDITY AUDIT — ADVERSARIAL REPORT

**Date:** 2026-09-07. **Branch:** `r331b-provenance`.
**Mandate:** `codex/UNIFIED_THEORY_PROOF_DIRECTIVE_2026-09-07.md` §4, the first
mathematical gate. Charter: `codex/ALPHA_RIGIDITY_AUDIT_CHARTER_2026-09-01.md`.
**Kernel artifacts:** `PF/AlphaL5PiScalingObstruction_r332.lean` (L5),
`PF/AlphaStructuralLawAudit_r334.lean` (L1, L2, L3, L4, I6, I9),
`PF/AlphaStructuralLawAuditI7_r335.lean` (I7).

§4 requires six outputs: **verdicts · dependency paths · countermodels or
bounded failed searches · minimal sufficient subsets · residual parameter space ·
strongest non-circular uniqueness theorem.** Each has its own section below.

**Scope.** **All eight structural laws are audited** (I7 completed 2026-09-07,
r335): L5 (r332); L1, L2, L3, L4, I6, I9 (r334); I7 (r335). The eight-law system
is closed.

---

## 0. CANONICAL WORDING AND THE MANDATORY CAVEAT

Wording for this result is governed by
`codex/CANONICAL_VERDICT_LANGUAGE_2026-09-07.md` (Pablo, 2026-09-07).

> The substrate does not derive the α-constants; L5 is impossible through its
> formalized substrate-ratio channel; the other six laws are independent of the
> formalized substrate assumptions; together the laws form a triangular,
> noncircular constraint system; therefore the constants are explicit postulates
> — not hidden consequences, but not an inconsistent patchwork.

*(Issued against the r334 report; r335 has since audited I7, making it the other
seven. Substance unchanged.)*

**MANDATORY, and it qualifies every verdict below:**

> "Independent" means independent **relative to the formalized base theory and
> the exact constructions tested** — it does not establish independence from
> every future extension of Principia Fractalis.

Concretely, for this report: `independent` means no derivation exists *from the
substrate's formalized classifying invariant* — the unique trace with range
`ℤ[1/3]` — *through the channels tested here*, which are direct membership and
ratio-reachability. It is not a claim about substrates the framework has not
built.

---

## 1. VERDICTS

From the five permitted words. Every verdict is backed by a kernel theorem.

| law | statement | forces | remove-and-survey | substrate-reachable? | **verdict** |
|---|---|---|---|---|---|
| **L1** | `α_Hodge² = α_Po·α_Hodge + α_Po` | φ | necessary (r334.A) | no — irrational | **independent** |
| **L2** | `α_P² = α_YM` | √2 | necessary (r334.B) | no — irrational | **independent** |
| **L3** | `α_Po + 2(α_NP − α_Hodge) = α_RH` | φ + ¼ | necessary (r334.C) | no — irrational | **independent** |
| **L4** | `α_QG² = α_YM·π` | √(2π) | necessary (r334.D) | no — irrational | **independent** |
| **L5** | `α_NS = α_RH·π` | 3π/2 | (r124: closes the free parameter) | **no — π not a ratio** (r332) | **independent** |
| **I6** | `α_NS = α_YM·α_BSD` | 3π/4 | necessary (r334.E) | no — irrational | **independent** |
| **I9** | `α_RH·α_YM = 3` | 3/2 | necessary (r334.F) | **YES, as a ratio** (r334.I) | **independent** |
| **I7** | `α_YM = α_Po + 1` | 2 | necessary (r335.A) — **most cascading: 7 of 9 move** | **YES, directly in `ℤ[1/3]`** (r335.B) | **independent** |

**Why not `redundant`:** remove-and-survey exhibits, for each, a positive
skeleton satisfying the anchor and the other seven laws yet differing from
canonical. The family strictly grows when any one is dropped.

**Why not `derivable`:** six are blocked by the trace-range obstruction (L1, L2,
L3, L4, I6, and L5 outright via r332). The two that survive it — **I7** (`2 ∈
ℤ[1/3]`) and **I9** (`3/2` ratio-reachable) — are compatible but unlinked: no
theorem ties I7's `+1` or I9's `3` to any substrate structure. Compatibility is
necessary, not sufficient.

**Why not `circular`:** no law's *statement* mentions the value it forces. This
is a genuine distinction — from the r301 bundle (r333), whose premise **is** its
conclusion, and from a hypothetically target-quoting law.

**So: independent.** Genuine additional assumptions. The α-skeleton's "derived
constants" claim fails not because the laws are circular but because **they are
assumptions**.

---

## 2. DEPENDENCY PATHS

Given the anchor, the eight laws resolve as a **triangular chain** — each law
pins exactly one α, in this order:

```
anchor:  α_Poincaré = 1
   │
   ├── I7 ──────────────▶ α_YM   = 2
   │        │
   │        ├── L2 ─────▶ α_P    = √2            (α_P² = α_YM)
   │        ├── L4 ─────▶ α_QG   = √(2π)         (α_QG² = α_YM·π)
   │        └── I9 ─────▶ α_RH   = 3/2           (α_RH·α_YM = 3)
   │                        │
   ├── L1 ──────────────▶ α_Hodge = φ            (needs α_Po only)
   │                        │
   │        L3 ◀───────────┴──────────▶ α_NP    = φ + ¼   (needs α_Hodge, α_RH)
   │
   │        L5 ◀──────────────────────▶ α_NS    = 3π/2    (needs α_RH)
   │                                       │
   │        I6 ◀──────────────────────────┴────▶ α_BSD   = 3π/4  (needs α_NS, α_YM)
```

**This shape is the audit's sharpest structural finding.** Nine unknowns, nine
constraints (anchor + eight laws), and **exactly one constraint pinning each
unknown**. The system is perfectly determined and **nowhere over-determined**.

That matters. A rigid system with *redundancy* — more constraints than unknowns,
all consistent — is evidence of structure: the surplus equations could have
failed and did not. A triangular system with one equation per unknown cannot
fail, and cannot corroborate anything. It is a change of variables from the nine
values to nine constraints, carrying exactly the same information.

r124 already showed the *eleven invariants* contain redundancy (I2, I8, and I6
among them). r334 shows the *eight structural laws* contain none. The move from
eleven invariants to eight laws removed precisely the redundancy that could have
been evidential.

---

## 3. COUNTERMODELS AND BOUNDED SEARCHES

Per §8: **failed search ≠ nonexistence unless formally exhaustive.**

### 3a. Explicit countermodels to redundancy — exhaustive

Each is a witness, not a search. Constructed and kernel-verified in r334.

| law dropped | witness | differs in | remaining seven laws |
|---|---|---|---|
| L1 | `wo_L1` | `α_Hodge = 1 ≠ φ` (`α_NP = 5/4` follows) | all hold |
| L2 | `wo_L2` | `α_P = 1 ≠ √2` | all hold |
| L3 | `wo_L3` | `α_NP = 1 ≠ φ + ¼` | all hold |
| L4 | `wo_L4` | `α_QG = 1 ≠ √(2π)` | all hold |
| I6 | `wo_I6` | `α_BSD = 1 ≠ 3π/4` | all hold |
| I9 | `wo_I9` | `α_RH = 1`; `α_NS`, `α_BSD`, `α_NP` move with it | all hold |

All six are positive skeletons satisfying the anchor. **Exhaustive as
refutations of redundancy** — one countermodel suffices.

### 3b. Underivability — exhaustive over the stated route

- `no_ktheoretic_ratio_is_irrational` (r334.G): **exhaustive.** Every ratio of
  `ℤ[1/3]` elements is rational; every irrational is excluded. Not a search.
- `pi_not_ktheoretic_ratio` (r332.A): **exhaustive**, same argument.
- Scope limit, stated: exhaustive over the substrate's K-theoretic trace route,
  which is the route the corpus has. A future object with an invariant range
  wider than `ℤ[1/3]` is untouched.

### 3c. Bounded / unattempted

| search | bound | status |
|---|---|---|
| A second self-consistent nine-tuple satisfying all eight laws with a different anchor | none run | **UNATTEMPTED.** Would end the rigidity claim outright |
| The sign/Galois quotient (L1, L2, L4 each pin only up to conjugation; positivity selects) | none run | **UNATTEMPTED.** Charter P3. No *independent* principle for positivity is stated anywhere |
| S-Δ1 / S-Δ2 Gröbner computations (charter P2/P3) | not run | **UNATTEMPTED** |
| I7 full protocol | — | **DONE** 2026-09-07, r335 |

---

## 4. MINIMAL SUFFICIENT SUBSETS

**There is no proper sufficient subset.** Of the eight audited laws, each is the
unique constraint pinning at least one α:

| α | pinned by | sole pinner? |
|---|---|---|
| α_Poincaré | anchor | yes |
| α_YM | I7 | yes (r335) |
| α_Hodge | L1 | yes |
| α_P | L2 | yes |
| α_NP | L3 | yes |
| α_QG | L4 | yes |
| α_RH | I9 | yes |
| α_NS | L5 | yes |
| α_BSD | I6 | yes |

Dropping any one leaves its α free (r334.A–F for the six; r124 for L5). So the
**minimal sufficient subset is the whole set**: anchor + eight laws, nine
constraints for nine unknowns.

Contrast the eleven-invariant system, where r124 found I2 and I8 redundant. The
eight-law presentation has had that slack removed.

---

## 5. RESIDUAL PARAMETER SPACE

| system | dimension | source |
|---|---|---|
| eleven invariants (no laws) | **1** — `α_BSD` free, every `t > 0` admissible | r124, Gröbner, `dim V(I) = 1`, exhaustive |
| eight laws + anchor + positivity | **0** — the canonical point | r128 |
| eight laws minus any one + anchor + positivity | **≥ 1** | r334.A–F, r124 |
| eight laws + anchor, **without** positivity | ≥ 0, plus the sign/Galois quotient on L1, L2, L4 | **not computed** — charter P3 |

**Information accounting.** Nine numerals enter (the anchor's `1`, and one
constant apiece in the eight laws: the `+1` of I7, the `3` of I9, the implicit
`π` factors of L4 and L5, and the structural coefficients of L1, L2, L3, I6).
Nine values leave. **The system neither creates nor destroys information.**

That is the quantitative form of the verdict. "No free parameters" is true of the
*solved* system and says nothing, because the parameters were spent on the
constraints.

---

## 6. STRONGEST NON-CIRCULAR UNIQUENESS THEOREM

The strongest statement the kernel and the premise audit **jointly** support is
the one already in the corpus — `AlphaSkeletonUniqueness_r128`'s
`alpha_skeleton_unique` — read with its premises exposed:

> Given the eight structural laws {L1–L5, I6, I7, I9}, positivity, and the
> external anchor `α_Poincaré = 1`, the nine-tuple is **unique**.

That theorem is correct, non-circular, and kernel-green. Nothing in this audit
weakens it.

What the audit fixes is the **label**. Per §4, no "unique / forced / derived"
word may be used until the kernel theorem and the premise audit jointly support
that exact word:

| word | supported? | why |
|---|---|---|
| **unique** | **YES**, with the qualifier *"given the eight laws, positivity and the anchor"* | r128, non-circular |
| **forced** | **NO** — not by the framework | the laws are independent assumptions (§1); nothing in the substrate forces them |
| **derived** | **NO** | five laws blocked by the trace-range obstruction; I9 unlinked; L5 closed by r332 |
| **rigid** | only as *"rigid given the laws"* | the laws carry the rigidity, not the substrate |
| **no free parameters** | **misleading** — retire it | the parameters were spent on the constraints (§5) |

**Recommended standing sentence, for the paper and the book:**

> The nine α-values are uniquely determined by eight structural laws together
> with positivity and the external Perelman anchor. Those eight laws are
> independent assumptions: none is redundant, none is derivable from the
> framework's substrate, and the system is triangular — one constraint per value,
> with no over-determination. The α-skeleton is therefore a *presentation* of the
> nine values, not a derivation of them.

---

## 7. WHAT WOULD CHANGE THESE VERDICTS

| finding | what would overturn it |
|---|---|
| all seven **independent** | a substrate theorem forcing any one law, without inserting its value |
| trace-range closure on five laws | a substrate object whose invariant range exceeds `ℤ[1/3]` |
| I9 exception | either a theorem linking the constant `3` to base-3 substrate structure (→ `derivable`), or a proof no such link exists (→ closed like the others) |
| triangularity | an *additional*, independently-motivated relation among the nine values that the canonical assignment satisfies but that is not implied by the eight. That would be genuine over-determination and genuine evidence |

The last row is the constructive path. It is what a rigidity claim would need.

---

*All eight laws audited. Kernel artifacts r332, r334, r335. Wording governed by
`codex/CANONICAL_VERDICT_LANGUAGE_2026-09-07.md`. Public HEAD `96c71da7`. NO PUSH.*
