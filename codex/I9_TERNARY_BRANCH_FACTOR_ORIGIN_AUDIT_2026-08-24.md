# PRINCIPIA FRACTALIS — I9 TERNARY BRANCH FACTOR ORIGIN AUDIT

**Date:** 2026-08-24
**HEAD:** `974e7f43` (r321 reconciliation, local; `origin/master` at `37fcd20c`)
**Companion to:** `codex/R220_R222_LOG_FREQUENCY_ORIGIN_AUDIT_2026-08-24.md`, `codex/PF_TRANSCENDENTAL_CARRIER_AUDIT_2026-08-24.md`
**Deliverable:** the READ-ONLY audit mandated by the post-r321 directive.

The question this document answers:

> **The α-skeleton's structural law I9 says `α_RH · α_YM = 3`. The base-3 substrate genuinely owns the integer `3`. Does the corpus contain a non-circular substrate-native derivation of `3` that plausibly bridges to the product `α_RH · α_YM`?**

Unlike π (r320 ruled out for L5) and the log-frequency `2π/log 3` (r321 exposed as normalization choice), the number `3` is intrinsically ternary. This audit tests whether that intrinsic ternary content can be non-circularly connected to I9.

---

## 1. HEAD

`974e7f43` (local); `origin/master` = `37fcd20c` (r220/r222 audit push).

## 2. Two candidate α-free 3-carriers

### Candidate A — `chi(1) = 3` via r220 digit-character dynamics

r220 defines α-free objects:
- `chi (ω : ℂ) := 1 + ω + ω^2` — `PF/LogPeriodicity_r220.lean:169`
- `S (ω : ℂ) (N : ℕ) := Σ_{n < N} ω^(D₃(n))` — `PF/LogPeriodicity_r220.lean:165`
- Exact recursion `S(ω, 3^(k+1)) = χ(ω) · S(ω, 3^k)` — `S_three_mul` at line 192.

At the canonical trivial character `ω = 1`:
- `chi(1) = 1 + 1 + 1² = 3` — kernel-immediate via `unfold chi; norm_num`.
- `S(1, 3^k) = χ(1)^k = 3^k` — via `S_pow_three_eq_chi_pow` at r220:177.
- Semantically: `S(1, N) = N` since ω^(anything) = 1 makes the sum count elements.

**Currently `chi_one_eq_three` is NOT stated as a named theorem in the corpus.** It is kernel-immediate but nameless.

### Candidate B — `T3 : TransferOperator 3` canonical operator

`PF/TransferOperator.lean:1245-1248`:
```lean
noncomputable def T3 : TransferOperator 3 := {
  phases := phaseFactorBase3
  apply := transferOperatorAction 3 phaseFactorBase3
}
```

- T3 acts on `LogWeightedL2` with three inverse branches `inverseBranch 3 k x = (x + k) / 3` for `k ∈ Fin 3`.
- T3 is α-free and π-free in definition.
- T3 is self-adjoint (via `T3_formal_adjoint_relation_via_integrability`).
- T3 is bounded (`‖T3‖ ≤ 1`).
- **T3's spectrum is NOT computed.** No eigenvalue theorem exists in the corpus.
- The normalization factor `1/3` in the action means: if the unnormalized ternary branch operator has an eigenvalue λ, T3's eigenvalue would be λ/3. So even if the "raw" ternary branch count gives 3, T3's normalization removes this.
- `T3SymContinuousSpectralMeasureAttempt.lean` explicitly acknowledges (lines 55-73) that the literal T3_sym has discrete spectrum and any "continuous spectral measure" route is a substrate reformulation, not a derivation.

## 3. The auditor found ONE existing nontrivial ‖χ‖ = 3 characterization: **r224**

`PF/ChiNormLevelThree_r224.lean` contains the strongest existing substrate-side connection to `3`:

### r224:134 — the α-characterization
```lean
theorem chi_norm_three_iff_even_integer (α : ℝ) :
    ‖chi (omega α)‖ = 3 ↔ ∃ k : ℤ, α = 2 * k
```

- Statement: `‖χ(e^{iπα})‖ = 3` iff `α ∈ 2ℤ`.
- Not circular. Proved via `abs_one_add_two_cos_eq_three_iff` (line 107) using `cos(πα) = 1 ↔ α ∈ 2ℤ`.
- **This IS a genuine α-free-hypothesis theorem**: given "‖χ‖ = 3" as input (α-free), it forces α to lie in the discrete set `2ℤ`.

### r224:153 — the α_YM instance
```lean
theorem chi_norm_alphaYM : ‖chi (omega 2)‖ = 3
```

- Direct instance at α = 2 (i.e., α_YM).
- Not circular. Substitutes α = 2 into the characterization; does not use α_YM's def.

### r224:167 — the α = 0 instance
```lean
theorem chi_norm_alpha_zero : ‖chi (omega 0)‖ = 3
```

- Same statement at α = 0. Different member of `2ℤ`.

### r224:177 — the σ-form
```lean
theorem sigma_eq_one_iff_chi_norm_eq_three (α : ℝ) :
    PrincipiaTractalis.SigmaAbscissa.sigma α = 1 ↔ ‖chi (omega α)‖ = 3
```

- Bridges r212's σ-abscissa to the r220 χ-norm.

**Assessment.** `chi_norm_three_iff_even_integer` is the **strongest existing α-free 3-carrier bridging to a canonical α**. It provides:
- A theorem `Property(α)` (namely `‖χ(e^{iπα})‖ = 3`)
- The characterization `Property(α) ↔ α ∈ 2ℤ`
- The instance at α = 2 = α_YM (`chi_norm_alphaYM`)

But note the **discrete ambiguity**: `α = 0, 2, 4, 6, …, −2, −4, …` all satisfy the characterization. The substrate cannot distinguish α_YM = 2 from α = 0 or α = 4 by `‖χ‖ = 3` alone. Selecting α = 2 requires an ADDITIONAL principle (e.g., "smallest positive even integer," or I7's `α_YM = α_Poincaré + 1`).

## 4. Current I9 proof route — is it definitional?

`PF/CrossMillenniumSharedInvariants.lean:149-150`:

```lean
/-- **`α_RH · α_YM = 3`**: (3/2)·2 = 3. The product of the two
    rational non-unit α's is an integer. -/
theorem α_RH_mul_YM_eq_three : α_RH * α_YM = 3 := by
  unfold α_RH α_YM; norm_num
```

**Yes — purely definitional.** The proof is:
1. Unfold `α_RH := 3/2` and `α_YM := 2`.
2. `norm_num` on `(3/2) * 2 = 3`.

No reference to `chi`, `S`, T3, ternary branching, or any substrate object. The `3` in the RHS is inserted definitionally.

The r128 counterpart is a **structure field** (`rh_prod : s.aRH * s.aYM = 3` at `AlphaSkeletonUniqueness_r128.lean:118`), i.e., an axiomatic input to the `StructuralLaws` predicate.

## 5. Does the corpus contain an RH-side substrate invariant?

**NO.**

The auditor searched for any function `r(O)` on a canonical substrate object `O` (chi, S, T3, etc.) such that:
1. `r(O)` is defined WITHOUT α_RH.
2. A theorem proves `r(O) = α_RH` (or equivalently `= 3/2`) via nontrivial substrate content.

**Zero such invariant exists in the corpus.**

The closest results:
- σ(3/2) = 0 (from r223 `corpus_constant_amplitude_dichotomy`). This is `Property(α_RH)`, but as a substrate-side statement about the α-value 3/2, not a substrate-derivation of 3/2.
- arg χ(e^{iπ·3/2}) = arg χ(-i) = arg(1 - i - 1) = arg(-i) = -π/2. Also `Property(α_RH)`.
- `α_RH_squared_eq_9_over_4` (invariant I2). Downstream of α_RH's numerical value; not a substrate route to 3/2.

No RH-axis invariant on any canonical PF object equals `3/2` non-circularly.

## 6. The five-arrow ideal architecture

Per DIRECTIVE Part IX:

```
    canonical ternary object O
        ↓ arrow 1
    invariant c(O) = 3
        ↓ arrow 2
    RH-axis invariant r(O)                   YM-axis invariant y(O)
    (α_RH-free definition)                    (α_YM-free definition)
        ↓ arrow 3
    r(O) · y(O) = c(O)
        ↓ arrow 4
    r(O) = α_RH, y(O) = α_YM
        ↓ arrow 5
    I9 = α_RH · α_YM = 3
```

Current status of each arrow:

| Arrow | Status | Evidence |
|---|---|---|
| **1** — canonical O → invariant c(O) = 3 | **EXISTS** partially | `chi(1) = 3` (unnamed, unfold+norm_num); `chi_norm_alphaYM : ‖χ(e^{iπ·2})‖ = 3` (r224, named). Neither is stated as a canonically-labelled "the substrate's `3`." |
| **2** — YM-axis invariant y(O) | **EXISTS partially** | r224's `chi_norm_three_iff_even_integer` gives a **discrete-set characterization** `α ∈ 2ℤ`, of which α_YM = 2 is one member. Not a unique substrate identification of α_YM. |
| **2** — RH-axis invariant r(O) | **MISSING** | No file defines any RH-axis substrate invariant. The α_RH-related substrate facts (σ = 0, arg χ = -π/2) are functions OF α evaluated at 3/2, not identifications OF 3/2. |
| **3** — factorization `r(O) · y(O) = c(O)` | **MISSING** | No substrate factorization exists; the product structure `α_RH · α_YM` has no substrate analogue in the corpus. |
| **4** — identification `r(O) = α_RH ∧ y(O) = α_YM` | **VACUOUS** on RH side (no r(O)); **PARTIAL** on YM side (r224 gives characterization up to 2ℤ ambiguity, plus need for "smallest positive" selection rule). |
| **5** — conclusion I9 | **EXISTS as `norm_num`** | Direct arithmetic unfold; not a substrate consequence. |

**Verdict:** Two of five arrows partially exist (arrow 1 partially, arrow 2 YM-side partially). Three of five arrows (arrow 2 RH-side, arrow 3, arrow 4 RH-side) are **entirely absent**.

## 7. Comparison A vs B

| Criterion | Candidate A: `χ(1) = 3` | Candidate B: T3 spectrum |
|---|---|---|
| α-independence | ✓ | ✓ |
| π-independence | ✓ | ✓ |
| Target-encoding absence | ✓ (χ predefined; ω=1 is the multiplicative identity) | ✓ (T3 predefined; no "3" chosen in spectrum) |
| Canonicity | high (ω=1 = mult. identity; trivial character) | high (T3 is THE canonical base-3 transfer operator) |
| Formal proof status | **Kernel-proved** (`unfold chi; norm_num`), currently unnamed | **NOT PROVED** (spectrum uncomputed) |
| Mathematical depth | shallow (arithmetic) | deep (compact operator theory) |
| Direct link to substrate dynamics | ✓ (via `S_three_mul` at ω=1: `S(1, 3^(k+1)) = 3 · S(1, 3^k)`) | indirect (spectrum conjectural) |
| RH relevance | none | **conjectured** (Hilbert-Pólya style; not formalized) |
| YM relevance | via r224 characterization at α = 2 | none |
| Ability to support I9 in current corpus | none (no bridge to product structure) | none (spectrum uncomputed) |
| Infrastructure required | minimal | maximal (Mayer transfer-operator theory, Perron-Frobenius, computed spectrum) |

**Verdict: Candidate A is the stronger 3-carrier on current evidence.** Candidate B requires substantial new spectral-computation infrastructure not present in the corpus.

## 8. Semantic-bridge cheats to reject

Per DIRECTIVE Part X, the following would be circular and are explicitly rejected as recommendations:

| Rejected pattern | Reason |
|---|---|
| `def rhInvariant := α_RH; theorem rhInvariant · α_YM = χ(1)` | Trivially unfolds; not a substrate derivation. |
| Define an operator with coefficients `3/2` and `2`, then recover `3` from spectrum. | Same. |
| Pick eigenvectors/eigenvalues because they yield `3/2` and `2`. | Same. |
| Add `chi_one_eq_three` as `unfold chi; norm_num` — DIRECTIVE Part XV explicitly calls this too weak. | Trivial; would be a nameplate on a definition-unfold. |
| Add `theorem I9_holds : α_RH * α_YM = 3` in a substrate file, proved via `α_RH_mul_YM_eq_three`. | Same theorem, different location; not a derivation. |

## 9. Smallest non-circular positive theorem — recommendation

Per DIRECTIVE Part XV, GOOD candidates are:
- a theorem connecting an INDEPENDENTLY DEFINED RH or YM invariant to the canonical ternary branch/renormalization factor;
- a theorem establishing a nontrivial canonical operator eigenvalue 3, IF the operator has independent semantic value.

**Assessment of what's tractable.**

The r224 machinery already provides a substantive `α_YM`-side bridge (`chi_norm_alphaYM`, `chi_norm_three_iff_even_integer`). Extending this to an RH-side bridge would require finding a canonical substrate quantity that INDEPENDENTLY equals `3/2` or characterizes it.

Two candidates were considered:

### Candidate R1 — chi-based
There is no natural chi-invariant equal to `3/2`. Modulus `‖χ(e^{iπ·3/2})‖ = |1 + 2cos(3π/2)| = |1 + 0| = 1`, not 3/2. Argument is `-π/2`. Neither is 3/2.

### Candidate R2 — T3-based
No computed spectrum. `3/2` is not proved to be an eigenvalue.

### Candidate R3 — direct chi(1) = 3 as named theorem
DIRECTIVE Part XV: **too weak**. Immediate via `unfold chi; norm_num`.

### **Recommendation: NO POSITIVE THEOREM RECOMMENDED.**

Per DIRECTIVE Part XV, the current state does not offer a non-trivial positive theorem candidate. Adding `chi_one_eq_three` would be "too weak" territory. Adding a genuine RH-side invariant would require inventing a new canonical PF object.

**Instead, the recommendation is: SEMANTIC RECONCILIATION — surface r224's existing bridge more prominently, and DOCUMENT the missing RH-side arrow.**

Concretely:
- Add a docstring cross-reference in `PF/AlphaSkeletonUniqueness_r128.lean` next to the `rh_prod : s.aRH * s.aYM = 3` field (line 118), citing r224's `chi_norm_alphaYM` as the strongest existing substrate-side YM connection AND noting that no analogous RH-side connection currently exists in the corpus.
- Add a docstring cross-reference in `PF/CrossMillenniumSharedInvariants.lean` near `α_RH_mul_YM_eq_three` (line 149) making the current definitional-unfold proof route honest: state that the `3` on the RHS is **not currently derived from the substrate's `3`** in a bridged form; cite r224 as the closest partial (YM-side only).
- Optionally: add a brief documentation-style theorem in r224 that CONNECTS the r224 YM-side bridge to the I9 statement, honestly labelled as "one factor of I9 has partial substrate provenance via r224; the other factor does not."

This is Type-3 in the sense of "precise semantic clarification," not a new positive characterization. It is the honest state.

**Alternative: a DOCUMENTED PARTIAL-BRIDGE theorem.**

If a more substantive landing is desired, the smallest legitimate one is:

```lean
/-- **Partial substrate provenance of I9 — YM side only.**  If `α = α_YM = 2`,
then `α_RH · α = 3` is equivalent to `α_RH · ‖χ(e^{iπα})‖ / 3 · 3 = 3`, i.e.,
under r224's characterization the YM-factor of I9 has a substrate-side witness
via `chi_norm_alphaYM`.  **No analogous RH-side witness exists in the corpus.** -/
theorem I9_YM_factor_matches_chi_norm_at_alphaYM :
    α_RH * ‖chi (omega α_YM)‖ = 3 * α_RH := by
  rw [chi_norm_alphaYM]
```

This is a documentation-oriented theorem that surfaces the r224 bridge in the exact location where I9 lives, without pretending to derive I9. Its content is not new mathematics; it is a proof-carrying cross-reference.

Whether to land this or leave it as pure docstring cross-reference is a stylistic choice; I do NOT recommend one over the other without your input, because both are legitimate and neither advances the actual gap (RH-side substrate invariant).

## 10. Status lock

Per DIRECTIVE Part XI:

| Result | Status |
|---|---|
| r128 conditional one-anchor rigidity | PROVED |
| Structural-law provenance | 0/8 laws intrinsically PF-derived |
| r320 trace-range ratio for L5 | FORMALLY RULED OUT |
| r220/r222 phase frequency uniqueness from base | REVOKED (r321 reconciliation) |
| Transcendental-carrier audit | 0 class-A/B π-generators formalized; ω-inversion candidate REVOKED |
| **I9 ternary bridge — YM side** | **PARTIAL** via r224 `chi_norm_alphaYM` + `chi_norm_three_iff_even_integer` (up to `2ℤ` discrete ambiguity) |
| **I9 ternary bridge — RH side** | **MISSING** — no substrate invariant equal to α_RH = 3/2 exists in the corpus |
| **I9 as a whole** | **NOT substrate-derived**; current proof is `norm_num` on `(3/2) · 2 = 3` |

**New fact surfaced by this audit.** The r224 file already contains the strongest existing α-free substrate connection to any structural-law constant — the YM-side characterization of `‖χ(e^{iπα})‖ = 3` as `α ∈ 2ℤ`. This is legitimately class B in the transcendental-carrier audit's classification scheme (a π-free / α-free canonical object with a characterization property whose solutions include a canonical α-value). The finding was not surfaced in the transcendental-carrier audit because that audit was focused on π, not on the integer 3.

**Implication for future work.** The current state supports two conclusions:

1. **The substrate's `3` is real** (Candidate A, `chi(1) = 3` and Candidate B, T3's ternary branch count) but **has not been connected to the α-skeleton's product `α_RH · α_YM = 3` non-circularly**. The YM half of the product has a partial connection via r224; the RH half has none.
2. **The next real breakthrough would be an RH-side substrate invariant** — a function of a canonical PF object, defined without α_RH, whose value characterizes α_RH = 3/2. No such invariant is currently in the corpus.

---

## Summary

**Candidate A** (`chi(1) = 3` via r220): kernel-immediate but nameless; α-free, π-free, canonical. Cannot bridge to I9 without an RH-side invariant.

**Candidate B** (T3 spectrum): mathematically deep but spectrum uncomputed; not currently a formal 3-carrier.

**Current I9 proof route:** `α_RH_mul_YM_eq_three : α_RH * α_YM = 3 := by unfold α_RH α_YM; norm_num`. Pure definitional arithmetic.

**Existing partial YM-bridge (r224):** `chi_norm_three_iff_even_integer` and `chi_norm_alphaYM`. Genuine α-free-hypothesis characterization; discrete-set ambiguity (α ∈ 2ℤ contains α_YM = 2 but also α = 0, 4, …).

**Missing:** every RH-side arrow. No substrate invariant equal to α_RH = 3/2 exists.

**Five-arrow architecture (DIRECTIVE Part IX):**
- Arrow 1 (O → c(O) = 3): partial (unnamed in `chi(1)`, named in `chi_norm_alphaYM`).
- Arrow 2 (YM side): partial (r224 characterization up to 2ℤ ambiguity).
- Arrow 2 (RH side), Arrow 3 (factorization), Arrow 4 (RH identification): **entirely absent**.
- Arrow 5 (I9): proved via `norm_num`, not via substrate.

**Recommended landing** (READ-ONLY; NOT implementing):

- **PRIMARY: SEMANTIC RECONCILIATION.** Docstring cross-references in `PF/CrossMillenniumSharedInvariants.lean:149` and `PF/AlphaSkeletonUniqueness_r128.lean:118` making the current definitional-unfold proof route honest and citing r224 as the closest partial substrate connection.
- **OPTIONAL: `I9_YM_factor_matches_chi_norm_at_alphaYM`.** A documentation-style theorem that surfaces the r224 YM-side bridge at I9's location. Not a new mathematical result; a proof-carrying cross-reference.

**Rejected recommendations:**
- `chi_one_eq_three` as a new named theorem — DIRECTIVE Part XV explicitly labels this as "too weak" (immediate via `unfold; norm_num`).
- A T3-based eigenvalue theorem — spectrum uncomputed; Clay-grade infrastructure required.
- Any new "RH-invariant" defined by unfolding α_RH — circular per DIRECTIVE Part X.

**Correct scientific status.** The base-3 substrate genuinely contains the integer 3 (via `chi(1) = 3` and via the ternary branch count of T3). The α-skeleton contains the equation `α_RH · α_YM = 3`. **These two `3`s are not currently connected by a non-circular substrate-derived bridge.** The YM side has a partial connection via r224 up to the discrete `2ℤ` ambiguity; the RH side has no substrate connection at all.

The five-arrow architecture required for a full substrate derivation of I9 has arrows 1 and (partially) 2-YM; arrows 2-RH, 3, and 4-RH are all missing. Arrow 5 (I9 itself) currently exists only as definitional arithmetic.

**Not implementing without your authorization.** Per DIRECTIVE Part X.10: STOP after producing this audit.

---

**End of audit.**
