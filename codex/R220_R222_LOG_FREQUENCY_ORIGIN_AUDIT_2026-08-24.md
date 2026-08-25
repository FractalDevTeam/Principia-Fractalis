# PRINCIPIA FRACTALIS — r220 / r222 LOG-FREQUENCY ORIGIN AUDIT

**Date:** 2026-08-24
**HEAD:** `4f4ac20a9b43b68bca5f745e2c9aef1800aaeb20` (transcendental-carrier audit on origin/master)
**Files audited:** `PF/LogPeriodicity_r220.lean` (676 lines), `PF/LogCosineNextZero_r222.lean` (260 lines)
**Companion to:** `codex/PF_TRANSCENDENTAL_CARRIER_AUDIT_2026-08-24.md`
**Deliverable:** the READ-ONLY provenance audit mandated by the post-carrier-audit directive.

The question this document answers:

> **Does base-3 renormalisation of the digit-character summatory function `S(ω, N) = Σ_{n<N} ω^{D₃(n)}` genuinely force the value `logFrequency = 2π / log 3`, or is that value a chosen normalization / ansatz?**

If it does, the proposed ω-inversion theorem is a legitimate class-B characterization of π.

If it does not, the ω-inversion would be circular: it would recover `2π / log 3` from a premise (√3-adjacent-zero-shift) that was itself introduced by the same definitional choice.

---

## 1. HEAD

`4f4ac20a9b43b68bca5f745e2c9aef1800aaeb20`

## 2. The eight questions — DIRECTIVE Part IV, answered exactly

### Q1. Is `logFrequency := 2π / log 3` literally a definition?

**YES.** `PF/LogPeriodicity_r220.lean:272-274`:

```lean
/-- **The log-frequency.**  `2π / ln 3 = 5.719202...`  No free parameter: only
the base 3 enters. -/
noncomputable def logFrequency : ℝ := 2 * π / Real.log 3
```

There is NO theorem prior to this line that derives `2π / log 3` from anything. The subsequent identity `logFrequency_mul_logPeriod : logFrequency * logPeriod = 2 * π` (line 285) is proved by `unfold logFrequency logPeriod; field_simp` — a definitional unfold.

### Q2. Is there any theorem PRIOR proving one-full-2π rotation per `N ↦ 3N`?

**NO.** The actual substrate theorems in r220 §3 about S's phase are:

- `phase_advance_per_triadic_step` (line 342-346):
  ```
  (arg (χ^(k+1)) : Real.Angle) - (arg (χ^k) : Real.Angle) = (arg χ : Real.Angle)
  ```
  Phase advance = **`arg χ(ω)`**, per triadic step.

- `arg_S_pow_three` (line 350-352):
  ```
  (arg (S ω (3^k)) : Real.Angle) = k • (arg χ(ω) : Real.Angle)
  ```
  Phase is `k · arg χ(ω)`, linear in `k = log₃ N` with slope `arg χ(ω)`.

Neither says the phase advances by `2π` per triadic step. The value `2π` per triadic step corresponds to `arg χ(ω) ≡ 0 (mod 2π)`, i.e., `χ(ω)` positive real — a special case.

### Q3. What does `phase_advance_per_triadic_step` actually say?

Exactly: `arg(χ^(k+1)) - arg(χ^k) = arg(χ(ω))` in `ℝ / 2πℤ`.

The phase advance per triadic step is `arg χ(ω)`, an **ω-dependent quantity**, not `2π` and not fixed by the base alone.

### Q4. Does χ(ω) vary with ω?

**YES**, explicitly proved in r220 §4:

| Witness | Location | Content |
|---|---|---|
| `chi_I` | line 415 | `χ(I) = I` — hence modulus 1, argument `π/2` |
| `arg_chi_I` | line 458 | `Complex.arg (χ(I)) = π/2` |
| `chi_neg_one` | line 463 | `χ(-1) = 1` — hence modulus 1, argument `0` |
| `Mtwo_two_log_frequencies` | line 572-575 | `Complex.arg Complex.I ≠ Complex.arg (1 : ℂ)` |

At `ω = I`: `arg χ = π/2` — phase advances by **quarter turn** per triadic step.
At `ω = -1`: `arg χ = 0` — phase advances by **zero** per triadic step.
Neither is `2π`.

Algebraically `χ(ω) = 1 + ω + ω²`, so `arg χ(ω)` can take essentially any value in `(-π, π]` depending on ω.

### Q5. Can two choices of ω on the SAME base-3 substrate yield different phase advances?

**YES**, explicitly proved by `Mtwo_two_log_frequencies` (r220:572-575):

```lean
theorem Mtwo_two_log_frequencies :
    Complex.arg Complex.I ≠ Complex.arg (1 : ℂ) := by
  rw [Complex.arg_I, Complex.arg_one]
  positivity
```

Consequence per DIRECTIVE Part IV.Q5: **the base alone does NOT select the oscillatory frequency.** The base-3 substrate is compatible with any `arg χ(ω) ∈ (-π, π]`, obtained by varying ω.

Even more emphatically, `matrix_promotion_summary` (r220:580-590) shows that the r218 matrix promotion of the digit-character system on the SAME base-3 substrate carries **two independent log-frequencies simultaneously** — the eigenvalues of `χ_M` have distinct arguments.

### Q6. Is the continuous cosine `cos((2π / log 3) · log x + φ₀)` derived from S, or separately defined?

**SEPARATELY DEFINED.** `PF/LogPeriodicity_r220.lean:363-366`:

```lean
/-- The log-periodic modulation with phase offset `φ₀`:
`cos( (2π/ln 3) · ln x + φ₀ )`. -/
noncomputable def logModulation (φ₀ : ℝ) (x : ℝ) : ℝ :=
  Real.cos (logFrequency * Real.log x + φ₀)
```

`logModulation` is a **new function**, not a functional of `S`. Its π-content enters through the definitional `logFrequency := 2π / log 3` (line 274). The subsequent invariance theorem `logModulation_three_mul` (line 386-392) uses `logFrequency_log_three_mul` (line 369-376):

```lean
theorem logFrequency_log_three_mul (x : ℝ) (hx : 0 < x) :
    logFrequency * Real.log (3 * x) = logFrequency * Real.log x + 2 * π := by
  ...
  have h : logFrequency * Real.log 3 = 2 * π := by
    unfold logFrequency; field_simp
  ...
```

The `2π` on the RHS reduces to the definition of `logFrequency`. No S-dynamics theorem is invoked.

### Q7. Is there any theorem connecting the phase of `S(ω, 3^k)` to `logModulation` with the SAME phase increment?

**NO.**

- Actual S phase increment per triadic step: `arg χ(ω)` (`phase_advance_per_triadic_step`).
- `logModulation` phase increment per triadic step: `2π` (`logFrequency_log_three_mul`).

These are **not equal** in general. They agree only when `arg χ(ω) ≡ 0 (mod 2π)`, i.e., `χ(ω) > 0`. This holds at (e.g.) `ω = -1` where `χ = 1`, but fails at `ω = I` where `arg χ = π/2`.

**The narrative bridge "the ternary digit-character dynamics generates the frequency `2π / log 3`" is not proved.** What is proved is a different, weaker statement: the frequency is `arg χ(ω) / log 3` (ω-dependent), and the *scale period* is `log 3`. Setting the frequency to `2π / log 3` is a *normalization choice* imposing "one full 2π revolution per triadic step" on the separately-defined `logModulation`.

### Q8. Where does the √3 zero-spacing come from?

**Solely from `logFrequency = 2π / log 3`.** r222 makes this explicit in its docstring (lines 27-33) and in `sqrt_three_from_logFrequency` (line 233-237):

```lean
theorem sqrt_three_from_logFrequency :
    π / logFrequency = Real.log (Real.sqrt 3) := by
  rw [log_sqrt_three, logPeriod, logFrequency]
  ...
```

And the header remark at line 27-33:
```
logFrequency · log(√3) = logFrequency · (log 3 / 2)
                      = (logFrequency · logPeriod) / 2
                      = 2π / 2 = π.
```

The √3 factor arises because at frequency `logFrequency = 2π / log 3`, a scale shift of `√3` corresponds to a phase shift of exactly `π`, and `cos(x + π) = -cos(x)` preserves zeros. **The √3 has no independent derivation.** It is `exp(π / logFrequency)` (`sqrt_three_eq_exp_pi_div_logFrequency`, line 240).

If `logFrequency` were reset to any other value ω', the analogous adjacent-zero shift would be `exp(π / ω')`, not √3. r222's own §5 title acknowledges this: "The `√3` is forced by `logFrequency = 2π / ln 3` — nothing else."

## 3. Dependency graph

```
    Real.log                   Real.pi                Real.cos
       │                          │                       │
       └────────┐        ┌────────┘                       │
                ▼        ▼                                │
        logPeriod := log 3     ← definitional             │
                │                                         │
                │  ╔═══════════════════════════════╗      │
                └─▶║ logFrequency := 2π / log 3     ║      │
                   ║        ★ DEFINITIONAL ★        ║      │
                   ╚═══════════════════════════════╝      │
                                │                         │
                    field_simp  │                         │
                                ▼                         │
                    logFrequency · logPeriod = 2π         │
                                │                         │
                                ├─────────────────────┐   │
                                ▼                     ▼   │
                    logFrequency_log_three_mul     logModulation  ◀───┘
                    (uses def, gives +2π/step)          (uses def)
                                │                         │
                                │                         ▼
                                │              logModulation_three_mul
                                │              (invariant under x ↦ 3x)
                                │                         │
                                ▼                         │
                    log_sqrt_three (log√3 = log 3 / 2)    │
                                │                         │
                                ▼                         │
                    logFrequency · log(√3) = π            │
                                │                         │
                                ▼                         │
                    logFrequency_log_sqrt_three_mul       │
                    (uses def)                            │
                                │                         │
                                ▼                         │
                    gLogCos_next_zero_forced_by_frequency │
                    (√3 shift preserves zeros)            │
                                │                         │
                                ▼                         ▼
                    sqrt_three_from_logFrequency     Every downstream √3
                    (√3 = exp(π/logFrequency))       zero-shift theorem
```

**Separate (non-connecting) branch — the S dynamics:**

```
    D₃ = digitSum3       ω : ℂ (free parameter)
         │                        │
         ▼                        │
    S(ω, N)  ◀──────────────────  │
         │                        │
         ▼                        ▼
    S_pow_three_eq_chi_pow   chi(ω) := 1 + ω + ω²
         │                        │
         │  ┌───────────────────  │
         ▼  ▼                     │
    S(ω, 3^k) = χ(ω)^k            │
         │                        │
         ▼                        ▼
    norm_S_pow_three         arg_S_pow_three
    (‖S‖ = ‖χ‖^k)            (arg S = k · arg χ(ω))
         │                        │
         ▼                        ▼
    sigma_eq_logb_norm_chi   phase_advance_per_triadic_step
    (σ = log₃‖χ‖)            (phase increment = arg χ(ω),
                              ω-dependent, ≠ 2π in general)
```

**The two branches do not touch.** No theorem in r220 or r222 identifies the S phase increment `arg χ(ω)` with `logModulation`'s per-triadic-step phase increment `2π`. The connection is entirely narrative.

## 4. Sources of the four load-bearing constants

| Symbol | Value | Substrate-derived? | Notes |
|---|---|---|---|
| `logPeriod` | `log 3` | **YES, fully.** Ratio between successive triadic scale levels; direct from base-3. | Substrate-native. π-free. |
| `arg χ(ω)` | ω-dependent, generic value in `(-π, π]` | **YES, fully.** Genuine output of `S_three_mul`. | ω is a free parameter; base 3 does NOT fix `arg χ`. |
| `logFrequency` | `2π / log 3` | **NO.** Definitional (r220:274). | Chosen to impose "one 2π-cycle per triadic step" on `logModulation`. |
| `√3` (adjacent zero shift) | `exp(π / logFrequency) = exp(log 3 / 2)` | **NO.** Downstream of `logFrequency` (r222). | Independent derivation absent. |

**Where π enters:** π enters r220 exactly once — in the definition `logFrequency := 2π / Real.log 3` (line 274). Every subsequent π occurrence in r220 or r222 reduces to unfolding this definition.

**Where √3 enters:** √3 enters r222 as `exp(π / logFrequency)`. No substrate theorem produces `√3` from base-3 dynamics alone.

## 5. Is "frequency forced by base alone" justified?

**NO, as currently stated.**

The r220 docstring makes several claims that overstate:

- Line 40-42: "**There is no free parameter in that frequency.** It is not fitted, not tuned, and does not depend on `ω`, on `α`, or on any amplitude. Only the base 3 enters."
- Line 272-274 (docstring of `logFrequency`): "No free parameter: only the base 3 enters."
- Line 599 (in `log_periodicity_stone` docstring): "The log-period is `ln 3` and the log-frequency is `2π/ln 3`, and their product is `2π` — **no free parameter**."

**What is actually true:**
- The log-**period** (scale ratio between triadic levels) is `log 3` — **substrate-forced**, base-3 native. ✓
- The log-**frequency of `logModulation`** is `2π / log 3` — **chosen by definition** to give one full 2π-cycle per triadic step on the separately-defined cosine.
- The log-**phase-advance-per-triadic-step of the actual S dynamics** is `arg χ(ω)` — **ω-dependent, not fixed by the base alone.** Witnessed by `chi_I` (arg = π/2), `chi_neg_one` (arg = 0), and `Mtwo_two_log_frequencies`.

**Distinction to be made explicit:** the phrase "no free parameter" is correct FOR the separately-defined `logModulation` function once its frequency has been set to `2π / log 3`; it is INCORRECT as a statement about what the base-3 substrate dynamics fixes. The base gives the scale ratio; the ω selects the phase advance; the definition of `logFrequency` couples the two by imposing one 2π cycle per triadic step.

## 6. Would the proposed ω-inversion be non-circular?

**NO.**

The recommendation in the transcendental-carrier audit (`codex/PF_TRANSCENDENTAL_CARRIER_AUDIT_2026-08-24.md:13`) was:

```lean
theorem logFrequency_characterized_by_sqrt3_shift
    {ω : ℝ} (hω : 0 < ω)
    (hshift : ∀ (A σ φ₀ a : ℝ), A ≠ 0 → 0 < a →
      NextZero (fun t => A * t^σ * Real.cos (ω * Real.log t + φ₀)) a =
      Real.sqrt 3 * a) :
    ω = 2 * Real.pi / Real.log 3
```

The premise `NextZero ... = √3 · a` treats "adjacent zero shift is √3" as an independently available property. But:

- The √3 shift is **not** independently derived. r222 obtains it from `logFrequency = 2π / log 3` via `sqrt_three_from_logFrequency`.
- The adjacency itself (that √3 · a is the NEXT zero, not an even farther one) is not proved in the corpus — it would require a `NextZero` predicate that mathlib does not supply and PF has not defined.
- Even if adjacency were available, the shift value √3 corresponds to phase shift `logFrequency · log(√3) = π` — i.e., to the specific case `n = 1` in `logFrequency · log c = n π`. Selecting `n = 1` is an additional adjacency/minimality assumption.

**Circularity assessment.** The premise "√3-adjacent zero shift" and the conclusion "logFrequency = 2π / log 3" are equivalent via the same definitional identity (r222:sqrt_three_from_logFrequency). The proposed theorem would reformulate the definition without adding substrate content.

**Verdict.** The ω-inversion is **not authorized**. It is not a genuine class-B characterization; it is a definitional restatement dressed as a characterization.

## 7. Outcome classification

Per DIRECTIVE Part VII, the possible outcomes:

- **Outcome A (POSITIVE)** — substrate genuinely forces one full phase revolution per triadic step. **NOT SATISFIED.** Phase advance is `arg χ(ω)`, not `2π`. Witnesses `chi_I`, `chi_neg_one`, `Mtwo_two_log_frequencies` explicitly refute it.
- **Outcome B (CONDITIONAL)** — base 3 gives scale ratio 3, plus an additional independent law "modulation repeats after exactly one triadic step" forces `Ω = 2π / log 3`. **PARTIALLY.** If one accepts "one 2π-cycle per triadic scale step" as an ADDITIONAL AXIOMATIC INPUT, then the frequency is characterized. But this additional input is exactly the r220 definitional choice, so it is not a substrate derivation.
- **Outcome C (NEGATIVE / NON-SELECTIVE)** — phase advance is `arg χ(ω)` and ω is free, so ternary digit-character substrate does not uniquely select a phase frequency. **SATISFIED.** This is what the r220 §4 witnesses (`chi_I`, `chi_neg_one`) and §5 matrix promotion (`Mtwo_two_log_frequencies`) actually prove.

**VERDICT: OUTCOME C.**

## 8. Reclassification per DIRECTIVE Part VII (Outcome C)

The r220 `logFrequency = 2π / log 3` carrier should be reclassified from

- (transcendental-carrier audit: proposed class-B candidate "characterization via √3 shift")

to

- **Class D + E (normalization convention + definition-injected)**, with r220 §4 witnesses explicitly demonstrating non-selectivity.

This does **not** invalidate any r220 or r222 theorem:

**PROVED (unchanged):**
- Exact ternary scale recursion `S(ω, 3N) = χ(ω) · S(ω, N)` (`S_three_mul_scale`).
- Amplitude power law `‖S(ω, 3^k)‖ = ‖χ(ω)‖^k` (`norm_S_pow_three`).
- Phase advances by `arg χ(ω)` per triadic step (`phase_advance_per_triadic_step`).
- Phase varies with ω: `arg χ(I) = π/2`, `chi(-1) = 1` giving arg `0` (`arg_chi_I`, `chi_neg_one`).
- Matrix-promotion two-eigenvalue-arg example (`Mtwo_two_log_frequencies`).
- Separately-defined `logModulation` is invariant under `x ↦ 3x` (`logModulation_three_mul`).
- At `logFrequency = 2π / log 3`, `gLogCos` zeros recur under `√3` scaling (`g_logcos_next_zero_forced_by_frequency`).

**NOT PROVED (and NOT to be claimed):**
- The digit-character dynamics uniquely force `logFrequency = 2π / log 3`. ← this is the false claim.
- π is generated by the base-3 substrate. ← follows from the false claim.

## 9. Non-selectivity is already in the corpus

Per DIRECTIVE Part VI, a corollary of §4 witnesses (already proved):

- `chi_I : chi Complex.I = Complex.I`
- `chi_neg_one : chi (-1 : ℂ) = 1`
- `arg_chi_I : Complex.arg (chi Complex.I) = π / 2`
- `Mtwo_two_log_frequencies : Complex.arg Complex.I ≠ Complex.arg (1 : ℂ)`

These four kernel-clean theorems together establish: **for the same base-3 substrate, two different values of ω can produce two different phase advances per triadic step.** No new theorem is required to make the point formally.

The single line that would need to change is a DOCSTRING clarification in r220 lines 40-42, 272-274, and 599, distinguishing:

- log-period (substrate-forced, `log 3`)
- log-frequency of `logModulation` (chosen normalization, `2π / log 3`)
- log-frequency of the actual S dynamics (`arg χ(ω) / log 3`, ω-dependent)

No theorem edit needed. No `sorry`. No `axiom`. Kernel state preserved.

## 10. Recommended next landing

Per DIRECTIVE Part X. Priority:
1. If r220 already contains enough mathematics to show phase non-selectivity, recommend NO redundant theorem; recommend semantic reconciliation.
2. If one exact missing non-selectivity lemma is required, prove only that after authorization.
3. If a genuine independent one-cycle principle exists elsewhere in PF, recommend the theorem connecting it to r220.

**Applicable case: 1.**

The non-selectivity witnesses (`chi_I`, `chi_neg_one`, `arg_chi_I`, `Mtwo_two_log_frequencies`) are ALREADY in r220. No new theorem is needed to establish that base 3 does not fix `arg χ(ω)`.

**Recommended landing (READ-ONLY recommendation; NOT implementing):**

### **SEMANTIC RECONCILIATION** — docstring correction only

Update three docstring locations in `PF/LogPeriodicity_r220.lean`:

- **Lines 40-42** (§0 header): rewrite the "no free parameter" claim to distinguish `logPeriod` (substrate-forced) from `logFrequency` (normalization choice on the separately-defined `logModulation`).
- **Lines 272-274** (docstring of `noncomputable def logFrequency`): change "No free parameter: only the base 3 enters." to a claim honest about the definitional choice.
- **Lines 597-601** (docstring of `log_periodicity_stone`): distinguish substrate-forced log-period from normalization-chosen log-frequency.

Optionally, add a brief comment section that explicitly cites `chi_I`, `chi_neg_one`, and `Mtwo_two_log_frequencies` as the witnesses that the phase advance is ω-dependent — i.e., document the corpus's own non-selectivity witnesses.

**No new theorem. No proof edit. No `sorry`. No `axiom`. No kernel state change.** All 47 axiom checks at the end of r220 remain unchanged.

Optionally: add a `#check` directive or a brief `theorem` restating that `Complex.arg (chi Complex.I) ≠ Complex.arg (chi (-1 : ℂ))` — but this would be redundant with `Mtwo_two_log_frequencies`.

### Type designation per DIRECTIVE Part X

**Not Type 1, Type 2, or Type 3 in the theorem-landing sense.** This is a **semantic-reconciliation landing**: correcting overreach in docstring claims to match what the theorems actually prove.

### Why not attempt an alternative

- **Alternative A (Type 1 attempt).** Try to prove `logFrequency = 2π / log 3` from a substrate-canonical hypothesis. **REJECTED:** no such hypothesis exists; the substrate gives `arg χ(ω)` which is ω-dependent.
- **Alternative B (Type 2 attempt).** Bridge some canonical PF invariant to `logFrequency = 2π / log 3`. **REJECTED:** the only PF invariant that could bridge is the "one 2π-cycle per triadic step" condition, which is itself the definitional choice being characterized.
- **Alternative C (Type 3 attempt).** Prove a no-go: "no ternary digit-character construction uniquely selects `2π / log 3`." **REJECTED:** the r220 §4 witnesses already establish this de facto; a formal universally-quantified no-go over an unbounded class of constructions is not a smallest tractable theorem.
- **Alternative D (Type 3 attempt).** Prove a small extension of the existing witnesses, e.g., a lemma stating `Complex.arg (chi Complex.I) ≠ Complex.arg (chi (-1))`. **REJECTED:** essentially a corollary of `arg_chi_I` and `chi_neg_one`; would be redundant labeling.

## 11. Status lock

Per DIRECTIVE Part XI, carrying forward unchanged:

| Result | Status |
|---|---|
| r128 conditional one-anchor rigidity | PROVED |
| Structural-law provenance | 0/8 laws intrinsically PF-derived |
| r320 trace-range ratio for L5 | FORMALLY RULED OUT |
| Transcendental-carrier audit | 0 class-A/B π-generators currently formalized |
| r222 ω-inversion candidate | **REVOKED — circular, per §6 above** |

**New status.** The r222 ω-inversion is **not a genuine class-B candidate**. Its premise (√3-adjacent-zero shift) is not independently derived; it is a definitional consequence of the same `logFrequency := 2π / log 3` the theorem was proposed to characterize.

The corpus currently contains **zero class-A / class-B π-generators**, and the previous "one tractable class-B candidate" identification is retracted.

---

## Summary

r220's substrate theorem `phase_advance_per_triadic_step` gives phase advance = `arg χ(ω)` per triadic step, an **ω-dependent quantity**. r220 §4 explicitly proves non-selectivity: `arg χ(I) = π/2` vs `arg χ(-1) = 0` on the same base-3 substrate.

The claim "logFrequency = 2π / log 3 is fixed by the base alone" is a **normalization choice** imposing "one full 2π revolution per triadic step" on the separately-defined `logModulation`. It is not a substrate theorem.

The r222 √3-adjacent-zero shift is downstream of that definitional choice (`sqrt_three_from_logFrequency`, `sqrt_three_eq_exp_pi_div_logFrequency`), not independently derived.

**Outcome: C (non-selective).** The proposed ω-inversion theorem is circular and not authorized. The r220 substrate genuinely produces log-period `log 3` and phase-advance `arg χ(ω)`; it does not produce `2π / log 3`.

**Recommended next landing (READ-ONLY; NOT implementing):** semantic reconciliation of three r220 docstring locations to distinguish substrate-forced `logPeriod` from normalization-chosen `logFrequency`. No theorem edit. No new theorem. No kernel state change.

**Retracted:** the r222 ω-inversion is no longer a class-B candidate in the transcendental-carrier audit. The transcendental-carrier audit's summary should be updated to reflect **zero class-A / class-B π-generators currently formalized AND zero known tractable candidates**.

**Correct status statement.** The current r220-r222 substrate machinery proves that base-3 renormalisation fixes the scale ratio (`log 3`) but leaves the phase advance a free ω-dependent parameter (`arg χ(ω)`). Every occurrence of `logFrequency = 2π / log 3` and its downstream √3 shifts is either definitional or a downstream corollary of that definition. No PF-native theorem currently forces π from base-3 substrate content.

**Not implementing without your authorization.** Per DIRECTIVE Part X: STOP after producing this audit.

---

**End of audit.**
