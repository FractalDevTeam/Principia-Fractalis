# Cosmology / dark-energy derivation route — reusable architecture map, 2026-10-11

Author: Pablo Cohen. Purpose: a reusable, source-cited reconstruction of the FULL
dependency route for the dark-energy sector, so later work starts here instead of
re-deriving it. (rev 2: four overclaims corrected per review — scalar→tensor scope,
marginal-σ withdrawn, g=φ̇/M scoped to background, CPL-domain scoped. Registers A/B/C
below separate verified deductions from modeling assumptions from empirical estimates.) Supersedes the route-level framing of
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
| 5′| scalar→tensor gap | audit §2.5 | **WITHDRAWN as stated; true statement is narrower.** The dimension count (Sym²ℝ⁴=10=1 trace+9 traceless) does NOT prove "scalar⟹isotropic tensor." It proves only: if the ONLY data available at a point are the churn scalar VALUE χ and the metric g_μν (no gradients ∂_μχ, no other fields), the sole symmetric rank-2 tensor is f(χ)·g_μν (isotropic). A scalar FIELD generically sources ANISOTROPIC stress via ∂_μχ∂_νχ (as every scalar in GR does). So this is not an obstruction to a scalar-field bridge; it only says "a pointwise function of χ's value, with no derivatives and no fields but the metric, is isotropic." Not Lean-worthy as an impossibility |
| 6 | Modified Einstein / Λ_eff(C) | ch08:201, 205 | **POSTULATE** |
| 7 | Modified-Friedmann ODE | `ModifiedFriedmann_r187.lean` | **KERNEL-PROVEN:** Λ_eff=Λ₀·exp(−∫₀ᵗ g), Λ_eff′=−g·Λ_eff. g is an ARBITRARY continuous function — an INPUT, not derived |
| 8 | w-bridge | `EquationOfStateBridge_r219.lean` | **KERNEL-PROVEN:** w(t) = −1 + g/(3H), exact. Plus: g≥0 ⟺ w≥−1 (`not_phantom_of_nonneg_rate`); w=−1 ⟺ g=0; sign change ⟹ located crossing (IVT); and the CPL prediction below |
| 9 | Observable w(z) / DESI | COSMOLOGY_W_BRIDGE §2 | g **MEASURED** by inverting r219: g₀≈0.74–1.05 H₀, zero at z≈0.40±0.03 (stable across 3 SN samples) |

## The candidate parameter-free prediction — in three registers

**(A) VERIFIED DEDUCTION (kernel, dataset-free).** `cpl_nonphantom_forces_wa_bound`
(r219): if w(a)=w₀+wₐ(1−a) ≥ −1 for all a∈(0,1], then **wₐ ≥ −1−w₀**. The binding
point is the a→0⁺ endpoint. Over a restricted domain a∈[a_min,1] the honest bound is
weaker: wₐ ≥ (−1−w₀)/(1−a_min). All kernel-checked.

**(B) MODELING ASSUMPTION (not derived).** The bound becomes a PF *prediction* only
under the monotonicity thesis g≥0 — which is **ASSUMED, not derived**: it is the
hypothesis `hg0 : ∀ s, 0 ≤ g s` of r187 `lambdaEff_antitone` (r187:140; r219:223 calls
it an assumption), encoding "consciousness only suppresses Λ." Two further assumptions
are needed and are NOT established: (i) that PF commits to g≥0 over the *whole* domain
incl. a→0 (early universe), not just the observed epoch — the a→0 endpoint drives the
strong bound; (ii) that the CPL form faithfully represents PF's actual w(a) (PF gives
w=−1+g/3H for its own g, not a CPL by construction).

**(C) EMPIRICAL ESTIMATE.** Robust, covariance-free fact: the DESI DR2 central values
give w₀+wₐ<−1 and violate the bound at EVERY domain cut tested (a→0 through z≤1), in
all three datasets (DESI+CMB, +DESY5, +Union3). **Significance: WITHDRAWN as I stated
it.** My earlier 2.23–2.69σ propagated *marginal* σ(w₀),σ(wₐ) and implicitly assumed
Cov(w₀,wₐ)=0; that is invalid — w₀,wₐ are strongly anti-correlated in CPL fits, so the
true σ(w₀+wₐ) requires the joint posterior. The published joint-covariance result is
DESI's own: dynamical DE preferred over ΛCDM at **2.8–4.2σ** (the 2D test; DESI DR2,
arXiv:2503.14743). The specific 1D test of w₀+wₐ+1<0 needs the published Cov(w₀,wₐ),
which I have not numerically extracted; I claim only the direction, not a σ.

**Net:** the direction (PF's monotone form sits on the disfavoured side of DESI) is
robust and parameter-free; the *magnitude* is DESI's joint number, not a marginal
propagation of mine. Giving up monotonicity removes even the direction (g unconstrained
= pure measurement; a g sign change is a *located* crossing at z≈0.40 by r219's IVT
theorem, permitted by r187's ODE but forbidden by its monotonicity theorem).

## What is refuted, and what g owes

- **ch26 volume mechanism REFUTED** (COSMOLOGY_W_BRIDGE §3): S_cons=exp[−0.95 V/V_char]
  with V_eff=(ct)³ implies g₀/H₀≈860 ⟹ w₀=+285.6 (excluded ~5000σ); the static
  alternative gives g≈0, w=−1, degenerate with Λ and 4.4σ from DESI. Both branches fail.
  Independent of ch26's own "engineered, not derived" admission at ch26:261.
- **Retirement condition for "g is derived":** a first-principles g(t) that either
  (i) hits g₀≈0.74 H₀ and a zero at z≈0.40, or (ii) if it predicts monotone g≥0,
  sits on the disfavoured side of DESI (direction robust; magnitude per DESI's joint
  posterior). It must route through a temporal law (ch06:707-708, open) and a
  localization map (absent). Note: the scalar→tensor step is NOT an obstruction for a
  scalar FIELD (gradients supply anisotropy); only a pointwise function of χ's value
  with no derivatives is isotropic.

## Representation note (reconciles my two earlier Oct-11 notes)

The identification **g = φ̇/M is a BACKGROUND-LEVEL conditional, NOT a demonstrated
model equivalence.** Matching Λ_eff=Λ₀exp(−∫₀ᵗ g) with Λ_eff=Λ₀e^{−φ/M} and
differentiating gives g=φ̇/M ONLY if (i) φ is homogeneous (φ=φ(t)), (ii) both are the
same Λ_eff with the same Λ₀. It is not shown that the two models' DYNAMICS agree:
r187's g is a phenomenological rate in a continuity-equation ODE; ch08's φ obeys a
sourced Klein–Gordon equation □φ=V'−ch₂/f. Demonstrating equivalence requires showing
the Klein–Gordon dynamics reproduces r187's g-ODE with matching source terms — NOT done.
So "derive M,f,ch₂(a)" and "derive g(t)" coincide only at the homogeneous background and
only under the posited-equal-Λ_eff assumption. The M≳0.287 M_Pl screening bound (ch08
`horizon_requires_planckian_scale`) is a necessary condition on the action representation
— observational (built from H₀, Λ), not substrate-derived.

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
