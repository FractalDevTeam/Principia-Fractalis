# PF modified gravity (Λ_eff) vs current data — the intelligent test, 2026-10-11
> **ROUTE-LEVEL ACCOUNT SUPERSEDED by codex/COSMOLOGY_DE_ROUTE_MAP_2026-10-11.md** (2026-10-11): this note worked only in the ch08 action representation (M,f,ch2) and missed the kernel stones ModifiedFriedmann_r187 + EquationOfStateBridge_r219, the MEASURED g (g0~0.74H0, zero at z~0.40), and the ch26 refutation. g=phi_dot/M is the route-level free function. The map settles the phantom-crossing question (w=-1+g/3H exact) and gives the one parameter-free prediction (wa>=-1-w0, DESI tension 2.2-2.7 sigma). Specific claims here that the map corrects stand corrected there.

Author: Pablo Cohen. Applying PF's OWN physics (ch08 modified-relativity / dark-energy
mechanism), not an invented σ-map. Verified under my own hand; honestly labeled.

## What PF actually predicts (ch08, formalized in Lean)

Modified Einstein equation with a consciousness-sourced effective cosmological term:
  G_μν + Λ_eff(C) g_μν = 8πG (T^μν + C^μν),
  Λ_eff(C) = Λ_0 · exp[ −∫_Σ ch₂(C(x)) · R_f(√(2π), |x|) d³x ].
From the action S = ∫√−g [R/2κ − ½(∇φ)² − V(φ) + L_m + L_æ] + (1/f)∫ φ·ch₂,
with V(φ) = (Λ_0/κ) e^{−φ/M}, varying gives Λ_eff = Λ_0 e^{−φ/M}: a ROLLING scalar,
so dark energy is DYNAMICAL (w evolves), not a constant. (The √(2π) appears as the
R_f kernel; σ(√2π) = −0.0387 < 0 is what makes that kernel bounded for all r — the
cosmological role of the number I earlier mis-used as a scaling-exponent "sector label".)
Lean: Ch08Ch14ModifiedRelativity, LambdaEffFromAction, ScreenedKernelAndFieldScale.

## Three confrontations with data — all verified, all consistent

1. **Dynamical dark energy — comparison, with significance correctly attributed.**
   ΛCDM: w = −1 constant. PF's Λ_eff(φ) is a rolling term, so w evolves. **DESI DR2 (2025)
   prefers dynamical DE over ΛCDM at 2.8–4.2σ** (CMB+BAO+SN combinations), in the quadrant
   w₀ > −1, w_a < 0 (e.g. BA model w₀ = −0.785±0.047, w_a = −0.43). **That significance is
   DESI's dynamical-vs-ΛCDM comparison — it is NOT evidence for PF.** PF is *compatible*
   with that quadrant; compatibility is not confirmation, and many models occupy it.
   **Timing — RETROSPECTIVE, not predicted.** The formalized PF derivation (Lean files
   Ch08Ch14ModifiedRelativity / LambdaEffFromAction / ScreenedKernelAndFieldScale, first
   committed 2026-10-06; the ch08 manuscriptcorrections, 2026-10-06) POSTDATES DESI DR2
   (2025-03) and DR1 (2024-04). So this is retrospective agreement, not a documented prior
   prediction. Whether the core consciousness-dependent-Λ idea predates DESI is NOT
   established by the available git history; I do not claim it.

2. **Preferred-frame parameter α₃ = 0 structurally** (energy–momentum conservation,
   automatic once Λ_eff comes from the action — `absorbed_lambda_leaves_no_residue`).
   Consistent with the binding PPN bound |α₃| ≲ 10⁻²⁰ (pulsar timing).

3. **Field scale M ≳ 0.287 M_Pl.** Recomputed under my own hand from Planck 2018
   (Ω_Λ = 0.6889, H₀ = 67.66): Λ = 1.10559e-52 m⁻², Λ^{−1/2} = 9.5105e25 m,
   c/H₀ = 1.3672e26 m, required M/M_Pl ≥ 0.28676 ∈ (1/4, 1/3). Matches the corpus to
   the digit. The Lean theorems (`horizon_requires_planckian_scale`,
   `required_ratio_is_near_one`) are kernel-clean [propext, Classical.choice, Quot.sound]
   — they formalize the LOGICAL STRUCTURE + arithmetic; the cosmological inputs are
   external (honestly cited, not derived). A necessary condition, allowed by data.

## The honest limits (fine precision requires naming them)

- **Phantom crossing — corrected.** PF's φ is a canonical scalar, so the *scalar's own*
  w_φ ≥ −1. But the EFFECTIVE dark-energy equation of state of PF's FULL modified-gravity
  theory (the C^μν term, the aether L_æ, the ch₂ coupling) is NOT w_φ; it requires a
  separate derivation from the modified Friedmann equations — which has NOT been done. So
  whether PF's *effective* w can reach the phantom-crossing DESI's best-fit slightly prefers
  is UNDETERMINED, not settled. My earlier claim "the canonical scalar can't phantom-cross"
  conflated w_φ with the effective w and was wrong. (The crossing is also debated /
  dataset-dependent — "not robust" per several analyses — so it is not a hard constraint
  either way.)
- PF does NOT pin w₀, w_a quantitatively (M, f, the ch₂ profile are undetermined). So this
  is QUALITATIVE consistency (right quadrant, right direction), NOT a quantitative fit.
- M ~ Planck is the standard quintessence difficulty, flagged honestly in the corpus.
- The variational derivation, Noether, PPN bounds, Planck/DESI values, R_f numerics are
  standard/cited, not derived in the corpus; the Lean carries the algebraic structure.

## Verdict

Not a confirmation, not a prediction (the formalized derivation is retrospective), not a
solved problem. What IS established and verified under my own hand: PF's modified-gravity
sector is a real, falsifiable, Lean-structured mechanism that (i) is compatible with the
PPN α₃ bound (α₃ = 0 structurally), (ii) is compatible with the Λ_obs field-scale
constraint (M ≳ 0.287 M_Pl), and (iii) yields DYNAMICAL dark energy — the class DESI DR2
now prefers over ΛCDM (2.8–4.2σ, which is DESI's significance, not PF's) in a quadrant PF
can occupy. **The supported conclusion is retrospective QUALITATIVE COMPATIBILITY awaiting
a quantitative, independently-specified test.** Compatibility is not confirmation.

The next calculation, stated to avoid fitting: derive PF's full expansion history H(z) from
the field equations with M, f, ch₂(a) and initial conditions FIXED INDEPENDENTLY (or given
explicit prior ranges) — NOT chosen to reach the contour, which would be fitting — then
compare the predicted distances to the DESI likelihood directly. A w₀–w_a (CPL) contour is
a useful first diagnostic ONLY if CPL faithfully represents PF's actual w(a). This is the
calculation that "can actually lose."

## Reproducibility / provenance
- PUBLIC on origin/master (verifiable): the three Lean files
  Ch08Ch14ModifiedRelativity, LambdaEffFromAction, ScreenedKernelAndFieldScale (they carry
  the logical structure + arithmetic; cosmological inputs external/cited). Kernel axioms
  [propext, Classical.choice, Quot.sound].
- NOT public: this codex note and the recent map/DESI commits are UNPUSHED (local only) —
  which is why commit baac763f cannot be retrieved from the public repo. The substance (the
  Lean files above, and the Planck-2018 recompute of the M-bound) is independently checkable.

Sources: DESI DR2 2025 (arXiv:2503.17342, 2504.15222, 2511.22512; desi.lbl.gov 2025-03-19).
Timing established from git: the modified-relativity Lean files first committed 2026-10-06.
