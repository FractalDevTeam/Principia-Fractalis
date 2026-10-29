# YM: the 2026-10-17 build plan is stale by five tasks — the lane is at step 5 of 6

**Date:** 2026-10-29 (Legion, measured against the deployed tree on Acer).
Analysis only, no Lean landed. Labels **FACT** (measured) / **JUDGEMENT**.
Delta over `codex/YM_OS_SCOPE_SITE_REFLECTION_2026-10-17.md`, whose §7 build
table is the reference plan. Read that first; everything below is what the tree
now says about it.

---

## Why this note exists

I raised a false alarm from that audit today. Its §3 names the load-bearing
blocker as *"the θ that landed is the wrong involution… without `S ∘ θ = S`
nothing downstream can work,"* and I reported that the Wilson RP chain —
including r361–r362 — was built on a broken foundation. **It is not.** The fix
landed on 2026-10-18, the day after the audit, and the audit was never amended.

The error was mine and it is the one §1 of the binding instructions names:
*"Deployed artifact > committed file > commit message > transcript. Check the
thing that runs, not the thing that was described."* I read the audit and not
the code. This note checks the code.

## The build table against the deployed tree — FACT

| # | task (as planned 10-17) | planned | **deployed state** |
|---|---|---|---|
| 0 | Fix `timeReflectionLink` (base `θx − ê₀`, add inverse) | 30, trivial | **DONE.** `timeReflectionGaugeField` is the measured-invariant V2: temporal links get `shiftTimeNeg ∘ timeReflectionSite` **and** the inverse; spatial unchanged. `timeReflectionLink` is **retired** — its only three occurrences in the tree are docstrings saying so. |
| 1 | continuity + `IsFiniteMeasure (wilsonGibbsMeasure)` | 150–250, low | **DONE.** `wilsonActionTotal_continuous` (`WilsonActionContinuity:118`), `wilsonGibbsMeasure_isFiniteMeasure` (`:148`). |
| 2 | `Even L` + Λ₊/Λ₀/Λ₋ decidable classification + `Equiv` | 120–200, low–med | **DONE.** `linkSector`, `LinkSector.reflect`, `linkSector_linkTheta` under `Even L`, `plaquetteSector` (`WilsonSectorDecomposition_2026_10_19`). |
| 3 | `wilsonActionTotal (θU) = wilsonActionTotal U` | 250–450, **medium** | **DONE and this is the one that matters most** — `wilsonActionTotal_timeReflection` (`WilsonActionReflectionInvariance_2026_10_18:393`), proved via `wilsonActionDensity_timeReflection` + `timeReflectionPlaquette_bijective.sum_comp`. **`S ∘ θ = S` is a theorem.** The audit's blocker is closed. |
| 4 | no-straddling ⇒ `S = S₊ + S₀ + S₋` | 300–500, **HIGH — the core** | **DONE.** `no_straddling` (`WilsonSectorDecomposition_2026_10_19:481`), `wilsonActionTotal_sector_decomposition` (`WilsonSectorAction_2026_10_19:100`), refined 3-way form (`WilsonActionSectorDecomp3Way_2026_10_22:36`). |
| 5 | Fubini reduction to the `Λ₀` integral | 200–300, medium | **LIVE — the frontier.** This is `hFubini`. |
| 6 | apply the Gram lemma ⇒ `wilson_reflection_positivity` | 40, trivial | gated on 5 only. |

**So five of the seven steps are done, including the step the audit rated HIGH
and called "the core".** The plan is stale by five tasks, and the task rated
hardest is not the one remaining.

## What `wilson_reflection_positivity` still carries — FACT

Three hypotheses as landed (`WilsonReflectionPositivity_2026_10_20:112`):
`_hF_support`, `hΦ_integrable` and `hFubini`. `_hF_support` is **not a gap** —
it is the RP statement's own premise, that the test functions are supported in
the positive-time half; a reflection-positivity statement without it would be
false, not stronger. So the undischarged hypotheses are two.
**`hΦ_integrable` was discharged by r361**
(`wilson_reflection_positivity_withReducedPhiR_of_continuous`), for continuous
test functions. So **`hFubini` is the single remaining hypothesis**, and it is
exactly plan step 5.

## The frontier, named — JUDGEMENT

`hFubini` → then step 6's 40 trivial lines → **unconditional
`wilson_reflection_positivity`**, which is §2's stated acceptance criterion for
the lane (*"with an empty hypothesis list, kernel-clean, three-axiom bar"*).

`hFubini`'s own four-step chain was measured in r362: steps 1, 3 and 4 have
their ingredients landed (step 4's sector reflection
`wilsonActionMinusR_timeReflection` carries `Even L`), step 2 is the Λ₊/Λ₋
measure split — r362 supplied the Λ₊ iterated form. The remaining analytic work
is step 4's change of variable, turning the Λ₋ integral into `star Φ_i` by
inversion-invariance.

**Note for whoever picks it up:** the assembled `hFubini` will carry `Even L`,
since both `minusToPlus_measurePreserving` and
`wilsonActionMinusR_timeReflection` do. That is a real hypothesis on the
lattice, not a formality, and the headline should state it.

## What is NOT claimed

Not claimed: that `hFubini` is easy — r362's header records step 4's change of
variable as *"the one piece of the chain that is genuinely more than
bookkeeping."* Not claimed: that an unconditional lattice RP headline is a
mass-gap result, or any Clay statement. §2 is explicit that the mass-gap steps
come after, per separate scoping. And nothing here revises §0: no Clay problem
is proven in this repo.

## Recommended amendment

§3 and the §7 table of `YM_OS_SCOPE_SITE_REFLECTION_2026-10-17` should carry a
dated note that steps 0–4 landed 10-18 through 10-22, so the next reader does
not raise the alarm I raised. **Amending another asset's audit is not mine to
do** — this note records the measurement and the recommendation.
