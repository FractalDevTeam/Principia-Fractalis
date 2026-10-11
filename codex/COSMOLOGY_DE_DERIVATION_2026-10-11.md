# PF dark energy, DERIVED from the action — strongest conditional result, 2026-10-11

Author: Pablo Cohen. The route map (`COSMOLOGY_DE_ROUTE_MAP_2026-10-11.md`) located the
g(t) route; this note turns the crank on it, deriving the homogeneous cosmology from PF's
own ch08 action instead of inventorying what is missing. Registers A/B/C separate verified
deduction from modeling assumption from empirical estimate. Central-value disagreement is
reported separately from statistical significance (which is not claimed).

## Result (one line)

On a homogeneous isotropic FRW background, PF's ch08 action **reduces to exponential
quintessence with a single free parameter M**, DERIVING (not positing) a thawing, strictly
non-phantom dark energy: w₀ ∈ [−0.99, −0.93] for M ∈ [0.287, 1] M_Pl, attractor
w* = −1 + 1/(3κM²) = −1 + M_Pl²/(24πM²). It lands in DESI's preferred quadrant
(w₀>−1, wₐ<0) but predicts a **milder deviation and NO phantom crossing** than the data's
central values.

## The derivation chain (register A unless flagged)

1. **Action** (ch08, register B — postulate): S = ∫√−g[R/2κ − ½(∇φ)² − V(φ)] + (1/f)∫φ·ch₂,
   with V(φ)=(Λ₀/κ)e^{−φ/M}.
2. **φ-EOM:** □φ = V'(φ) − ch₂/f. On FRW with φ=φ(t): φ̈ + 3Hφ̇ = −V' + ch₂/f.
   Since V'=−V/M, this is φ̈ + 3Hφ̇ = V/M + ch₂/f.
3. **Closure step — the action-admissible ch₂ vanishes on the isotropic background.** Of the
   five objects called ch₂, only the Pontryagin density Tr(F∧F) ∝ E·B can sit in the
   covariant action (LambdaEffFromAction step 0). E·B is a pseudoscalar: on ANY isotropic
   FRW background it is **zero** (no parity-odd background). So ch₂ = 0 and the source term
   drops: φ̈ + 3Hφ̇ = V/M.
4. **This is exactly exponential quintessence.** V=V₀e^{−φ/M}, i.e. λ ≡ M_Pl,red/M with
   λ² = 1/(κM²). (The screening-length bound M≳0.287 M_Pl ⟺ λ ≲ 0.695; κ=8π/M_Pl².)
5. **Background identification g=φ̇/M** (r187/r219, register B — background-level) gives the
   derived g-ODE: ġ + 3Hg = V/M² = m², where m² = Λ_eff/(κM²) is the SAME screening mass as
   `ScreenedKernel`. Closed, no free function.
6. **w is exact and non-phantom (register A — theorem).** w = −1 + g/(3H) (r219) equals the
   canonical w_φ = (½φ̇²−V)/(½φ̇²+V) = 1 − 2V/(½φ̇²+V) ≥ −1 for φ̇²≥0, V>0, equality iff
   φ̇=0. So w ≥ −1 everywhere — a theorem, matching r219 `wEff_ge_neg_one` and ch27:168
   ("never phantom"). Attractor (de Sitter, ρ_m→0): g*/H = 1/(κM²), w* = −1 + 1/(3κM²).

## Closure analysis (the reviewer's request)

- **Independent variables:** {φ, φ̇}, a (or H), ρ_m.
- **Equations:** φ-EOM (step 2), Friedmann H²=(κ/3)(ρ_m+½φ̇²+V), matter continuity
  ρ̇_m+3Hρ_m=0.
- **Only external input:** ch₂(t), the Pontryagin source history. On isotropic FRW it is
  zero (step 3) → **the system is FULLY CLOSED; no free function remains.**
- **Remaining parameters, not functions:** M (in the [0.287,1] M_Pl window), Λ₀ (fixed by
  Ω_Λ0), matter IC (fixed by Ω_m0). The DE history is a **one-parameter (M) family.** The
  free function g(t) of the route map has collapsed to a single number.
- **Where closure FAILS (the exact independent input, if isotropy is dropped):** a
  parity-odd / helical gauge background gives Tr(F∧F) ≠ 0; then ch₂(t) is a genuine
  independent input (the Pontryagin history of the cosmic gauge field). On the standard
  isotropic background it is identically zero, so closure holds there.

## Numbers (register C — integrated, Ω_m0=0.315, frozen-field thawing IC)

| M/M_Pl | λ=M_Pl,red/M | w* (attractor) | w₀ (integrated) | wₐ (CPL fit z≤3) | g₀/H₀=3(1+w₀) |
|---|---|---|---|---|---|
| 0.287 | 0.695 | −0.839 | −0.930 | −0.099 | 0.21 |
| 0.40  | 0.499 | −0.917 | −0.964 | −0.051 | 0.11 |
| 0.60  | 0.332 | −0.963 | −0.984 | −0.023 | 0.05 |
| 1.00  | 0.199 | −0.987 | −0.994 | −0.008 | 0.02 |

w₀ sits between −1 and w* (field still thawing toward the attractor today).

## Topological source vs consciousness entropy (the reviewer's point)

The action channel is **Pontryagin (topological)**, zero on isotropic FRW. The
consciousness-entropy ch₂=1−Tr(ρ²) **cannot** appear in the covariant action (step 0) and
so does **not** source the homogeneous DE roll. Therefore PF's DERIVED homogeneous dark
energy has **no consciousness content** — it is ordinary exponential quintessence.

ch27 reaches a quintessence-like w_DE (w₀≈−0.85 at ch27:179, ≈−0.95 at ch27:729) but by
**positing** a profile ch₂(z)=0.95 e^{−(z/0.5)²} (ch27:176) built on the non-action-admissible
entropy-ch₂ and a spatial gradient (∇𝒞)² (ch27:153). My derivation **reproduces ch27's
non-phantom quintessence from the action without that profile** — so the consciousness
dressing is not what produces the homogeneous w_DE; the exponential potential's own dynamics
is. (Same "novel ingredient not load-bearing" pattern as COSMOLOGY_W_BRIDGE §5 and the ΛCDM
comparison paper.) The relation PF actually requires for a genuine consciousness→DE link is
NOT identity of the two ch₂'s; it is a nonzero (helical) Pontryagin background — a specific,
testable ingredient absent from the isotropic model.

## Confrontation with DESI — direction only, no significance (register C)

- **PF derived** (M in window): w₀ ∈ [−0.99,−0.93], true w(a) ≥ −1 everywhere,
  g₀/H₀ ∈ [0.02, 0.21].
- **DESI DR2 central:** w₀ ≈ −0.65 to −0.75, wₐ ≈ −0.9 to −1.3, g₀/H₀ ≈ 0.74 (from the
  r219 inversion, COSMOLOGY_W_BRIDGE §2), phantom crossing at z≈0.40.
- **Two directions of disagreement:** (i) PF is strictly non-phantom; DESI central values
  prefer a crossing. (ii) PF's deviation is too MILD — derived g₀/H₀ ≤ 0.21 vs measured
  ≈0.74, i.e. w₀ too close to −1. Both are directions; **no σ is claimed** — the statistical
  strength needs the joint w₀–wₐ posterior (strongly anti-correlated), which I have not used.
  DESI's published joint preference for dynamical-over-ΛCDM is 2.8–4.2σ, a related but
  distinct 2D test.
- **CPL misrepresents PF's w(a):** a straight-line CPL fit of PF's non-phantom w(a) over z≤3
  yields w₀+wₐ ≈ −1.0 to −1.03 (table), i.e. it extrapolates below −1 at a→0 even though the
  true w never crosses. Concrete demonstration that comparing PF to DESI's CPL contour via
  w₀+wₐ is itself only approximate (the reviewer's domain caveat, realized). Non-phantom on
  [a_min,1] requires BOTH w₀≥−1 and wₐ ≥ (−1−w₀)/(1−a_min); PF satisfies both by construction.

## What this changes vs the route map / COSMOLOGY_W_BRIDGE

- At the homogeneous isotropic level, g(t) is **no longer a free function** — the action
  derives it, given M. This COMPLEMENTS COSMOLOGY_W_BRIDGE (which inverted DESI to *measure*
  g because it tested the phenomenological r187 ODE with g free); it does not contradict it.
  The measured g₀/H₀≈0.74 is the data; the derived g₀/H₀≤0.21 is the prediction; they
  disagree in magnitude (direction only).
- **Genuinely still open:** (i) M's value inside [0.287,1] M_Pl (screening+swampland give the
  window; no deeper principle yet selects a point); (ii) whether a helical Pontryagin
  background exists (the only route for topology/consciousness to enter the homogeneous DE);
  (iii) the full inhomogeneous C^μν (needs the manifold + localization map, still absent).

## Provenance
Derivation algebra and the exponential-quintessence reduction checked under my own hand;
background integrated numerically (scipy, Ω_m0=0.315, frozen-field IC, V₀ tuned to Ω_Λ0=0.685).
Lean stones cited: r187 (`lambdaEff_antitone`, hypothesis g≥0), r219 (`wEff`, `wEff_ge_neg_one`,
`cpl_nonphantom_forces_wa_bound`), ScreenedKernel (m², M-window). Chapter: ch27 §eos (posited
profile). No Lean built this pass; no claim depends on an unbuilt statement.
