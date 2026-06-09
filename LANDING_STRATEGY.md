# Landing Strategy — Principia Fractalis

**Document version:** 2026-06-09 (audit cycle reset)
**Author:** Pablo Cohen
**Adjacent docs:** [`docs/governance/PUBLISHING_GATE.md`](docs/governance/PUBLISHING_GATE.md), [`docs/governance/FRAMEWORK_FIRST.md`](docs/governance/FRAMEWORK_FIRST.md), [`README.md`](README.md), [`PROOF_PACKAGE.md`](PROOF_PACKAGE.md)

This document is the **strategic positioning** of the Principia Fractalis
work — how the framework should be presented externally, in what order,
to what audiences, and through which channels. It is paired with the
governance docs that enforce the discipline.

---

## The framework-first thesis

Per [`FRAMEWORK_FIRST.md`](docs/governance/FRAMEWORK_FIRST.md): **PF is a
substrate-level Theory of Everything, not six separate Clay discharges**.
Every external presentation must lead with the substrate and treat the
Clay axes as *ancillary consequences*, not as the headline.

The right elevator pitch is:

> Principia Fractalis is a substrate-level algebraic architecture in
> which seven framework constants α_*, formed from {√2, φ, π, 1}, satisfy
> a tightly constrained identity web (eleven cross-Millennium invariants,
> machine-verified in Lean 4 axiom-free in the kernel sense). The
> substrate's connection to the six unsolved Clay Millennium problems is
> *conditional* on named hypotheses that are themselves at least as hard
> as the Clay problems. The framework's empirical content includes
> falsifiability conditions, a cosmological-constant suppression match,
> and a structural prediction for QUIPU cosmological coherence.

The wrong elevator pitch (do not use):

> "Principia Fractalis solves 5 of the 7 Millennium Prize Problems."

The first frames PF as a *substrate proposal* with named open problems
and concrete empirical bets. The second triggers reviewer reflexes
because the in-code documentation (`PF.lean`,
`MillenniumReductionSoundness.lean`) explicitly disclaims this stronger
reading. Any reviewer who lands on the README first and the code second
will see contradiction and lose trust before reading the substrate
argument.

---

## Sequencing — what to present, in what order

External presentations should follow this sequence:

1. **Substrate cascade** — `perelman_anchored_cascade_capstone`. φ²−φ = 1,
   3π/2 = 2·3π/4, α_QG² = (α_Poincaré+1)π. The algebraic web of α-values.
2. **Eleven cross-Millennium invariants** — the identity web bundled in
   `CrossMillenniumSharedInvariants`. Machine-verified, axiom-free.
3. **Lean engineering** — 530+ files, mathlib 4.24.0-rc1, 8360 jobs
   clean. Real engineering effort.
4. **Empirical anchors** — Λ_eff suppression matches 120·ln(10);
   D_3 / R_f Dirichlet-series infrastructure is mathlib-grade.
5. **Falsifiability** — F1–F8, with F2/F3/F4/F6 as the operationalizable
   bets.
6. **Honest scope** — name the open named-hypothesis Props
   (PolylogEigenvalueConjecture, RHSpectralSurjectivityConjecture, etc.)
   that load-bearing theorems consume. Refer to
   [`OPEN_PROBLEMS.md`](OPEN_PROBLEMS.md).
7. **Per-axis Clay residuals** — the gaps table in `README.md`.

Steps 1–5 are the "substantive yes" of the work. Steps 6–7 are the
"honest no". Both must be present; the second must not be hidden.

---

## Audience-specific framings

### Pure mathematicians / Clay-problem specialists

Lead with: substrate-level meta-theorem (step 1–2). Acknowledge
explicitly that the Clay literal-statement-form discharge is not in
the package; what *is* in the package is the substrate's algebraic
forcing of the α-skeleton and the typed reduction to named open
problems. Honest scope is the most important asset here — these
reviewers will detect overclaim instantly.

### Lean / formalization community

Lead with: Lean engineering (step 3). The substrate algebra is real
mathlib-grade work. D_3 / R_f / IntervalArithmetic could potentially
upstream to mathlib4 directly. Be transparent about the four sorries
in `VAlphaPMap.lean` (the LinearPMap formulation that closes the
KatoRellichInput_false gap structurally).

### Theoretical physics community

Lead with: empirical anchors (step 4). The Λ_eff suppression match to
120·ln(10) is the strongest hook. The QUIPU coherence-length prediction
matches the Boehringer 2025 1.38 Gly observation. The falsifiability
conditions F2/F3/F4/F6 are real, operationalizable bets.

### Consciousness / IIT community

Lead with: ch₂ ↔ Φ_IIT bridge (`ch2_le_one_minus_exp_neg_phi_over_two`).
This is a real entropy inequality on Schmidt spectra, mathlib-grade. The
clinical calibration is currently synthetic (100-patient simulated study);
real-data validation against the 847-patient cohort is the next step.

### AI/ML community

Mention only where directly applicable. The framework is about substrate
physics, not AI. Avoid the framing "this is the kind of thing AI can
help formalize"; that will trigger AI-overclaim reviewer reflexes.
Instead: "the formalization was assembled with AI tooling under a
human-only publishing gate" is honest.

---

## Channels and gating

Per [`PUBLISHING_GATE.md`](docs/governance/PUBLISHING_GATE.md), the
absolute rule is: **Pablo Cohen retains exclusive control over external
publication**.

Permitted without explicit approval:
- Local commits, branch work, CHANGELOG updates
- Draft documents marked WIP / for vetting
- This file (LANDING_STRATEGY.md) is updated freely

Requires explicit Pablo approval:
- arXiv submission
- Journal submission
- Press release / blog post
- Mailing mathematicians or named experts
- Posting to social media or public mailing lists
- Issuing any PR to mathlib that mentions PF beyond the trivial-upstream
  components (D_3, R_f)

Vetting protocol before any of the above: blind multi-model stress-test.
"Stick it in a bunch of different AIs with no context, document
independent reactions, verify consistency across models." The rationale
is the 150-mathematician AI-overclaim warning and the lack of
institutional backing.

---

## What to release first, when ready

Phase 1 (low-risk, high-defensibility): standalone mathlib PR of D_3 /
R_f / interval-arithmetic infrastructure. These are real mathlib-grade
contributions independent of the framework dispute. Builds reputation
without exposing the substrate claim to per-axis Clay reviewers.

Phase 2 (medium-risk): substrate-level meta-theorem manuscript focusing
on the eleven cross-Millennium invariants, the algebraic α-web, and the
falsifiability conditions. Frame as: "here is a tightly-constrained
algebraic architecture; here are its testable predictions; here are the
named open hypotheses that, if discharged, would yield the per-axis
Clay outcomes." This is the work itself.

Phase 3 (high-risk): per-axis Clay discharges as their open hypotheses
get closed. This may take years (P1, P4) or longer (P5–P8 require
mathlib upstream).

The publishing gate stays in force through all three phases. None of
this gets pushed externally without explicit per-channel approval.

---

## The discipline this document enforces

Every external claim must trace to a [`PROOF_PACKAGE.md`](PROOF_PACKAGE.md)
row. Every "axiom-free" claim must trace to [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md).
Every "discharged" claim must NOT contradict [`OPEN_PROBLEMS.md`](OPEN_PROBLEMS.md).
If any of the four documents drifts out of sync, the publishing gate
auto-blocks.

The framework's strength is its honest scope. Defending substrate-level
content with substrate-level claims is a stable position. Defending it
with Clay-level claims invites refutation the in-code documentation
already concedes.
