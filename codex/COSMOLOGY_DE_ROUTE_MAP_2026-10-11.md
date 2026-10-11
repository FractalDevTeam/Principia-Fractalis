# Cosmology / dark-energy derivation route — reusable architecture map, 2026-10-11

Author: Pablo Cohen. Purpose: a reusable, source-cited reconstruction of the FULL
dependency route for the dark-energy sector, so later work starts here instead of
re-deriving it. Supersedes the route-level framing of
`DERIVE_M_F_CH2_FROM_SUBSTRATE_2026-10-11.md` and `MODIFIED_GRAVITY_VS_DESI_2026-10-11.md`
(both worked only in the ch08 action representation and missed the r187/r219 stones,
the measured g, and the ch26 refutation). Verified against the live tree @149162e0 and
prior Acer campaigns (COSMOLOGY_W_BRIDGE_2026-08-10, CHURN_TO_STRESS_TENSOR_BRIDGE_AUDIT_2026-09-14,
ALPHA_SUPPLIED_VS_DERIVED_2026-10-01, PF_FRACTAL_ARCHITECTURE_2026-09-10).

## The route, stage by stage (both ends proven, middle open/postulated)

Spine arrow: substrate → emergent locality → modified relativity → cosmology observable.

| # | Stage | Object / source | Status |
|---|---|---|---|
| 0 | Substrate T_∞ | ch04; `T_infinity_rigidity`, faithful trace | **KERNEL-PROVEN** (unique up to iso + faithful trace; [propext,choice,sound]) |
| 1 | Spacetime emergence M⁴ = Aut(T_∞)/Aut₀ | ch04 Thm 4.18; `TimelessField.lean:156-162` | **POSTULATE / prose.** Lean stub `SpacetimeEmergence := Nonempty (endo)` — vacuous; no manifold, metric, or dimension |
| 2 | Layer-1 churn χ_k = ½‖ρ_{t+1}−ρ_t‖²_F | `FrobeniusChurn.lean:131-133` | **KERNEL-PROVEN properties** (nonneg/sym/zero-iff-eq/unitary-inv). NB: NOT a book object — χ_k/"churn"/Frobenius-temporal are absent from the manuscript; it is a verification-lane scalar on finite-level matrices |
| 3 | Temporal law d/dt ch₂ = ? | ch06:707-708 | **OPEN BY THE BOOK'S OWN ADMISSION** — "explicitly acknowledges the temporal law is not formulated." This is the dynamics the DE sector needs and does not have |
| 4 | Localization χ_k/ρ_t → spacetime points | — | **ABSENT.** No map from `Matrix (Fin (3^k))` states to x∈M⁴ (audit N4) |
| 5 | Consciousness stress tensor C^μν | ch08:79-81, ch12 Def 12.1 | **POSTULATE; B11 conditionally circular** — defined via T̂^μν per state, which presupposes M⁴ (stage 1) and a measure μ on states (both unbuilt) |
| 5′| scalar→tensor obstruction | audit §2.5 | **IMPOSSIBILITY (properly scoped):** a scalar cannot source a generic symmetric rank-2 tensor. Sym²(ℝ⁴)=10-dim, trace=1, traceless part=9 unfixed. So any C^μν=f(χ_k) is at most a 1-parameter *isotropic* family. Forbids scalar-ONLY bridges; does NOT forbid bridges using extra localization+geometry data (those are merely absent) |
| 6 | Modified Einstein / Λ_eff(C) | ch08:201, 205 | **POSTULATE** |
| 7 | Modified-Friedmann ODE | `ModifiedFriedmann_r187.lean` | **KERNEL-PROVEN:** Λ_eff=Λ₀·exp(−∫₀ᵗ g), Λ_eff′=−g·Λ_eff. g is an ARBITRARY continuous function — an INPUT, not derived |
| 8 | w-bridge | `EquationOfStateBridge_r219.lean` | **KERNEL-PROVEN:** w(t) = −1 + g/(3H), exact. Plus: g≥0 ⟺ w≥−1 (`not_phantom_of_nonneg_rate`); w=−1 ⟺ g=0; sign change ⟹ located crossing (IVT); and the CPL prediction below |
| 9 | Observable w(z) / DESI | COSMOLOGY_W_BRIDGE §2 | g **MEASURED** by inverting r219: g₀≈0.74–1.05 H₀, zero at z≈0.40±0.03 (stable across 3 SN samples) |

## The one parameter-free prediction (and it is mildly losing)

The framework's monotonicity thesis — "consciousness only suppresses Λ", i.e. g≥0,
which is exactly r187's `lambdaEff_antitone` hypothesis — yields a kernel-checked,
dataset-free CPL prediction (`cpl_nonphantom_forces_wa_bound`):

    if w(a)=w₀+wₐ(1−a) ≥ −1 on a∈(0,1],  then  wₐ ≥ −1 − w₀.

Confronted with DESI DR2 (2025), verified under my own hand (w₀ error propagated into
the floor):

| dataset | w₀ | wₐ measured | PF floor −1−w₀ | tension |
|---|---|---|---|---|
| DESI+CMB | −0.667±0.088 | −1.09±0.29 | −0.333 | 2.50σ |
| DESI+CMB+DESY5 | −0.752±0.057 | −0.86±0.22 | −0.248 | 2.69σ |
| DESI+CMB+Union3 | −0.65±0.10 | −1.27±0.40 | −0.350 | 2.23σ |

Measured wₐ sits BELOW the PF-allowed floor in all three → the monotone form is
**disfavored at ~2.3–2.7σ**. No PF parameter is fit; this is the framework's own
structural commitment confronting data, and losing mildly. Giving up monotonicity
removes the prediction entirely (g unconstrained = pure measurement; a g sign change
is then a *located* phantom crossing at z≈0.40, permitted by r187's ODE but forbidden
by its monotonicity theorem).

## What is refuted, and what g owes

- **ch26 volume mechanism REFUTED** (COSMOLOGY_W_BRIDGE §3): S_cons=exp[−0.95 V/V_char]
  with V_eff=(ct)³ implies g₀/H₀≈860 ⟹ w₀=+285.6 (excluded ~5000σ); the static
  alternative gives g≈0, w=−1, degenerate with Λ and 4.4σ from DESI. Both branches fail.
  Independent of ch26's own "engineered, not derived" admission at ch26:261.
- **Retirement condition for "g is derived":** a first-principles g(t) that either
  (i) hits g₀≈0.74 H₀ and a zero at z≈0.40, or (ii) if it predicts monotone g≥0,
  inherits the ~2.3–2.7σ tension above. It must route through a temporal law
  (ch06:707-708, open), a localization map (absent), and must evade or satisfy the
  §2.5 scalar→tensor obstruction.

## Representation note (reconciles my two earlier Oct-11 notes)

The ch08 action picture (V(φ)=Λ₀e^{−φ/M}, φ sourced by ch₂) and the r187/r219 picture
(Λ_eff=Λ₀exp(−∫g)) are the SAME exponential with **g = φ̇/M**. So "derive M, f, ch₂(a)"
and "derive g(t)" are one problem in two coordinates. The M≳0.287 M_Pl screening bound
(ch08 `ScreenedKernelAndFieldScale`, `horizon_requires_planckian_scale`) is a necessary
condition on that representation — observational (built from H₀, Λ), not substrate-derived.

## α-skeleton status (for anyone routing through it)
Per ALPHA_SUPPLIED_VS_DERIVED_2026-10-01: every α is a literal `def`; the rigidity
theorem is real and axiom-free but its content is "a 9-equation system with one supplied
value has a unique positive solution"; the invariants were read off the values. The
α-cascade is a coherence structure, NOT a derivation apparatus. Do not route a physical
prediction through "the substrate derives α".

## Machine reconciliation (2026-10-11)
- **Acer** `xluxx-Nitro-AN515-58:/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE`,
  branch master @149162e0 — the LIVE tree, authoritative, 8 commits ahead of origin,
  unpushed, 46 dirty files (preserved).
- **Legion local** `C:/Users/psolo/Principia-Fractalis`, branch `security-hardening`
  @45b386a — a DIVERGENT branch, not the live tree; left untouched.
- `D:/CLAUDE-i9` — a workspace of audit-read artifacts, not a checkout.

## Provenance
All Lean statements verified by reading source in the live tree @149162e0, 2026-10-11
(r187/r219 theorem statements + in-file #print axioms discipline blocks confirmed; no
build run this pass). DESI tension recomputed under my own hand. Codex campaign notes
cited inline; their load-bearing Lean claims cross-checked against the files.
