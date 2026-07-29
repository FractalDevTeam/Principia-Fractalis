# The falsifiability registry (F1–F8) is not a faithful encoding — CONFIRMED

Source of finding: Codex audit, 2026-07-28, against
`PF_Lean4_Code/PF/Referee/FrameworkFalsifiabilityConditions.lean`.
Independently reviewed by Claude (Opus 5) the same day. **The finding is
correct and the defect is structural, not cosmetic.**

## The core defect (one sentence)

Every registered falsifier has the shape `∃ m : ℝ, |m − predicted| > ε`
(or a disjunction outside an interval), with **no constraint tying `m` to
any measurement**. Such a proposition is inhabited by an arbitrary real —
e.g. `H₀ = 0` satisfies F4's "Hubble bracket failure" — so each F-condition
is *mathematically true independent of any experiment*. They therefore do
not encode refutation conditions at all.

Whatever the surrounding comments claim, the kernel verifies only:
constants are what they are defined to be, arithmetic identities hold,
and `≥ δ` is incompatible with `< δ`.

## Per-condition status (Codex's classification, endorsed)

| F | registry Prop | what Lean actually proves | verdict |
|---|---|---|---|
| F1 | `∃ m, \|m − α_RH\| > 10⁻¹⁵` | `alpha_RH_predicted = 3/2`; trivial interval logic | **not an encoding**; bridge uses a *different* strengthened hypothesis (`measurement = 1`) and never consumes F1 |
| F2 | `∃ m, m < 0.94 ∨ m > 0.96` | `ch2_predicted = 0.95 ∈ [0.94,0.96]` | **retracted** (the `c₂ = 19/20` derivation was retracted); bridge proves only the low side |
| F3 | `∃ m, \|m − exp(−E)\| > ε` | a *definitional* identity (`frameworkSuppressedDensity` was defined by the same exponential) | **retracted/conditional**; `ε` unconstrained, may be ≤ 0; depends on retracted 0.95 |
| F4 | `∃ H₀, H₀ < 67 ∨ H₀ > 75` | `hubble_predicted = 69.8 ∈ [67,75]` | **not an encoding**; bracket also drifted [67,73] → [67,75] |
| F5 | `∃ α₁₄₄, α₁₄₄ ≠ √2 ∧ α₁₄₄ ≠ φ+¼` | every stored `alphaMeasured` in `the143Problems` equals a stored target | **not an encoding**; exact equality conflicts with all four tolerance variants in the docs (10⁻⁴, 2×10⁻³, ±0.05, exact) |
| F6 | `∃ ω, ω < 0.65 ∨ ω > 0.75` | `darkEnergyDensity_predicted = 0.7`, strict interval | **not an encoding**; provenance alternates 78π-derivation vs DESI/Pantheon+ |
| F7 | `∃ n : ℕ, n ≠ 78` | `78 = 48+26+4`; `brstH2_predicted = 78` | **not an encoding**; no BRST complex, no cohomology, no dim E₆ anywhere in the file |
| F8 | `∃ δ > 0, ∀ k, \|k log 3 − E\| ≥ δ` | `E > 0`, plus `≥ δ` vs `< δ` | **retracted/conditional**; the docs' fixed ½log3 tolerance and `k = 252` are NOT proved |

## What must change (design, not patching)

A faithful falsifier cannot quantify existentially over an unconstrained
real. The correct shape is a **structure carrying the measurement's
provenance plus a decision procedure**:

```lean
structure Measurement (name : String) where
  value      : ℚ            -- exact rational, not ℝ
  tolerance  : ℚ
  tol_pos    : 0 < tolerance
  provenance : String       -- instrument/dataset/run identifier
  -- and, where applicable, a certificate that `value` was produced by
  -- the stated protocol (a hash, a data file reference, or a Lean-side
  -- reconstruction from raw counts)

def Refutes (m : Measurement n) (predicted : ℚ) : Prop :=
  tolerance m < |m.value - predicted|
```

Then `Refutes` is *decidable* on rationals (`decide`/`norm_num`), it is
**false** for the framework's own numbers (which is the point — it is a
condition that has not fired), and it is **not** satisfiable by an
arbitrary witness. The current `∃ m, …` form should be deleted, not
weakened.

## Required actions (priority order)

1. **Do not cite F1–F8 as kernel-verified falsifiability anywhere** —
   papers, README, `six_as_one.pdf`, or talks. This is the immediate
   exposure: a referee who opens the file finds trivially-true Props
   labelled as experimental refutation conditions.
2. Mark **F2, F3, F8 retracted** in one place (they depend on the
   retracted `c₂ = 0.95` anchor) and say so in `OPEN_PROBLEMS.md`.
3. Rebuild F1, F4, F5, F6, F7 on the `Measurement`/`Refutes` pattern
   above, with **one** preregistered protocol and **one** numerical
   tolerance each — no more per-document variants.
4. Delete or rename the existing `IBM_Ten_Way_Disagreement`-style Props
   so nothing can cite them by their current names.
5. F7 in particular should either construct the BRST cohomology (large
   project) or be restated honestly as the arithmetic identity
   `78 = 48+26+4` with the E₆ interpretation flagged as unformalized.

## Why this matters more than it looks

The rest of the corpus's credibility rests on the axiom-discipline rule.
A registry of falsifiers that are *true by construction* is the same
category of error as the BSD `rfl` lookup table found on 2026-07-27 — and
it is in the file most likely to be read by a skeptic, because it is the
one that advertises falsifiability. Fixing it is a credibility gain, not
a loss: "we found our own falsifiers were vacuous and rebuilt them" is a
strong sentence.

Related: `memory/bsd-axis-audit.md` (the analogous rfl-tautology finding),
`HANDOFF_2026-07-28.md` §4.
