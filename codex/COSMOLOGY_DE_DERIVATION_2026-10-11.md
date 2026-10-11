# PF dark energy, DERIVED from the action — strongest conditional result, 2026-10-11

> **rev 3 (per review):** retracts the universal "isotropy ⟹ Pontryagin=0" (true only for
> zero/Abelian/parity-symmetric backgrounds; a non-Abelian isotropic chromo-natural background
> has E·B≠0). Scopes the whole derivation to the Q=0 gauge branch — one allowed construction,
> not the universal PF background. Adds a both-conventions Planck-mass block. Scopes the IC
> finding to this construction. Clarifies DESI's 2.8–4.2σ is ΛCDM-deviation, not crossing
> significance. NO manuscript edit: the checks show PF's gauge sector is unspecified/open.

Author: Pablo Cohen. The route map (`COSMOLOGY_DE_ROUTE_MAP_2026-10-11.md`) located the
g(t) route; this note turns the crank on it, deriving the homogeneous cosmology from PF's
own ch08 action instead of inventorying what is missing. Registers A/B/C separate verified
deduction from modeling assumption from empirical estimate. Central-value disagreement is
reported separately from statistical significance (which is not claimed).

## Result (one line)

On a homogeneous isotropic FRW background **AND a zero/Abelian/parity-symmetric gauge
background (Q=0 branch — see step 3)**, PF's ch08 action **reduces to exponential
quintessence with a single free parameter M**, DERIVING (not positing) a thawing, strictly
non-phantom dark energy: w₀ ∈ [−0.99, −0.93] for M ∈ [0.287, 1] M_Pl, attractor
w* = −1 + 1/(3κM²) = −1 + M_Pl²/(24πM²). It lands in DESI's preferred quadrant
(w₀>−1, wₐ<0) but predicts a **milder deviation and NO phantom crossing** than the data's
central values. This is NOT the universal PF background: a non-Abelian isotropic (Q≠0)
background sources ch₂ and is a different cosmology PF does not currently specify.

## Planck-mass conventions (stated once, both ways)

PF's `ScreenedKernel` uses κ = 8π/M_Pl², so **M_Pl is the UNREDUCED Planck mass**;
M̄_Pl = M_Pl/√(8π) is reduced, κ = 1/M̄_Pl². Every bound in both conventions:
- screening bound: M ≳ 0.287 M_Pl (unreduced) = **1.44 M̄_Pl** (reduced).
- de Sitter slow-roll m ≤ H: M ≥ 0.345 M_Pl = √(3/8π) M_Pl (unreduced) = **√3 M̄_Pl** (reduced).
- quintessence exponent λ (V∝e^{−λφ/M̄_Pl}) = M̄_Pl/M; λ²=1/(κM²); for M=0.287 M_Pl, λ=0.695.
The table's "M/M_Pl" is UNREDUCED throughout.

## The derivation chain (register A unless flagged)

1. **Action** (ch08, register B — postulate): S = ∫√−g[R/2κ − ½(∇φ)² − V(φ)] + (1/f)∫φ·ch₂,
   with V(φ)=(Λ₀/κ)e^{−φ/M}.
2. **φ-EOM:** □φ = V'(φ) − ch₂/f. On FRW with φ=φ(t): φ̈ + 3Hφ̇ = −V' + ch₂/f.
   Since V'=−V/M, this is φ̈ + 3Hφ̇ = V/M + ch₂/f.
3. **Closure step — CORRECTED (rev 3).** Earlier I claimed "ch₂=Tr(F∧F)∝E·B vanishes on ANY
   isotropic background." **That is wrong, and conceded.** E·B is parity-odd, so it vanishes
   only if the gauge background also satisfies one of: **(a)** zero gauge background; **(b)**
   Abelian group (then isotropy forbids a preferred E·B direction); **(c)** parity symmetry.
   Spatial isotropy ALONE does NOT force it: a non-Abelian homogeneous *isotropic* ansatz
   A^a_i ∝ δ^a_i (the chromo-natural / gauge-flation ansatz, SU(2)) has **E·B ≠ 0**
   (E^a_i∝δ^a_i∂_t(aQ), B^a_i∝g_c(aQ)²δ^a_i ⟹ E·B∝g_c(aQ)²∂_t(aQ)·3 ≠ 0).
   **Moreover PF does not specify F.** The action writes "Tr(F∧F)" without fixing the gauge
   group, connection, or background; ch04's gauge/automorphism structure is an OPEN problem
   (the spacetime-emergence quotient is machine-proved to collapse, r333–r335); and ch06's
   ch₂ is the second Chern character of a coherent *sheaf* (a number, ch06:149), a different
   object from a dynamical gauge field's Pontryagin *density*. So the Pontryagin source is
   **underdetermined by the corpus.** What follows is therefore the **zero-gauge-background
   branch (Q=0)** — ONE allowed construction, in which the source drops and
   φ̈ + 3Hφ̇ = V/M. The non-Abelian branch (Q≠0) is a genuinely different cosmology (extra
   d.o.f. Q(t), gauge energy density, and a nonzero ch₂/f source) and is NOT computed here
   because PF supplies no connection/ansatz to compute it from.
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
- **Where this branch is not the whole story (the exact independent input):** a non-Abelian
  isotropic gauge background (chromo-natural ansatz A^a_i∝δ^a_i — isotropy NEED NOT be
  dropped) or any parity-broken background gives Tr(F∧F) ≠ 0; then ch₂(t) is a genuine
  independent input (the Pontryagin history of the cosmic gauge field), the system gains the
  gauge d.o.f. Q(t), and the quintessence closure above does not apply. Closure holds only on
  the Q=0 (zero/Abelian/parity-symmetric) branch. PF does not specify which background.

## Numbers (register C — integrated, Ω_m0=0.315, frozen-field thawing IC: φ_initial/M≈276, see finding 1)

| M/M_Pl | λ=M_Pl,red/M | w* (attractor) | w₀ (integrated) | wₐ (CPL fit z≤3) | g₀/H₀=3(1+w₀) |
|---|---|---|---|---|---|
| 0.287 | 0.695 | −0.839 | −0.930 | −0.099 | 0.21 |
| 0.40  | 0.499 | −0.917 | −0.964 | −0.051 | 0.11 |
| 0.60  | 0.332 | −0.963 | −0.984 | −0.023 | 0.05 |
| 1.00  | 0.199 | −0.987 | −0.994 | −0.008 | 0.02 |

w₀ sits between −1 and w* (field still thawing toward the attractor today).

## Topological source vs consciousness entropy (the reviewer's point)

**[rev 3 scope: this section's "zero on isotropic FRW" holds only on the Q=0 branch; see
step 3. On a non-Abelian isotropic background the Pontryagin source is nonzero and the
mechanism is underdetermined, not nulled.]**

The action channel is **Pontryagin (topological)**, zero on isotropic FRW *in the Q=0 branch*. The
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
- **DESI DR2 central:** w₀ ≈ −0.65 to −0.75, wₐ ≈ −0.9 to −1.3, phantom crossing at z≈0.40.
  (The "g₀/H₀ ≈ 0.74" of COSMOLOGY_W_BRIDGE §2 is NOT a measurement — it is the CPL fit
  translated through THIS model, g=3H(1+w), and is M-dependent; so compare w, not g.)
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

## What the derivation ALSO establishes (the record must carry these)

**1. The 10⁻¹²⁰ is an INITIAL CONDITION on THIS construction, not a result (scoped).** The suppression is
V_today/(Λ₀/κ) = e^{−φ_today/M}. For Λ₀ Planckian (Λ₀/κ ~ M_Pl⁴) and V_today ≈ (2.3 meV)⁴,
this requires **φ_initial/M ≈ 276** (reduced M_Pl; 283 non-reduced) — i.e. the field starts
≈120 decades down the exponential. The dynamics rolls φ by only Δφ/M ≈ g₀/H₀ ≈ 0.2 per
Hubble time (verified), so it does NOT generate the 276; it is **preset in the IC**. The
modeling input "V₀ tuned to Ω_Λ0=0.685" IS the cosmological-constant fine-tuning in disguise
(it fixes φ_initial/M ≈ 276). This model does not solve the CC problem; it relocates it into φ_initial. **Scope (per
review):** this shows THIS construction (Planckian Λ₀, exponential V, frozen IC, Q=0)
presets the hierarchy; it does NOT establish that every PF route does (a different Λ₀
normalization or a Q≠0 gauge-sourced route is not covered). (Consistent with
ch26:261 "engineered, not derived" and COSMOLOGY_W_BRIDGE §3.)

**2. On the Q=0 branch, consciousness has no effect on background cosmology — but this is
NOT universal (rev 3 retraction).** I earlier wrote "the action gives consciousness ZERO
background effect." That holds ONLY on the zero/Abelian/parity-symmetric branch. A
non-Abelian isotropic (chromo-natural) background has ch₂=Tr(F∧F)≠0 and WOULD source φ, so
the ch26 "Λ falls where consciousness is high" thesis is **not killed** on the background —
it is **underdetermined**, because PF specifies no gauge connection/ansatz (step 3). NO
manuscript null-result edit is warranted; the honest status is "the homogeneous consciousness
mechanism is neither established nor excluded, pending PF fixing its gauge sector." The
further obstacle: even with a nonzero Pontryagin density, the ch06 sheaf-ch₂ (a number) must
be identified with the gauge Pontryagin density (a 4-form) — two different objects — for the
"consciousness" reading to apply.

**3. The prediction is NOT PF-specific — it is the generic exponential-quintessence class.**
w ≥ −1, thawing, w₀ ∈ [−0.994,−0.930] with λ ∈ [0.20,0.70] is textbook exponential
quintessence (Ratra–Peebles / Wetterich 1988; Ferreira–Joyce 1998). **If confirmed it
confirms the class, not PF; if refuted it refutes PF's action along with the class.** The
only PF-specific content is the M window — and even its lower bound M ≳ 0.287 M_Pl is the
standard slow-roll condition m ≲ H in different clothes: m ≤ H ⟺ M ≥ 0.345 M_Pl (unreduced)
= √3 M̄_Pl (reduced); the screening 0.287 M_Pl = 1.44 M̄_Pl is the same condition with the
observed Ω_Λ factors. So PF here reduces to a known model; it does not add a distinguishing
cosmological signature.

**4. The falsifier, as a number.** Non-phantom is a theorem of this action, so **any
confirmed w(a) < −1 at any epoch excludes PF's action** (together with the whole canonical
single-field class). DESI DR2's central CPL fit has that feature; the ~2.8–4.2σ figure (DESI DR2,
arXiv:2503.14743) is the preference for **dynamical DE over ΛCDM** (a 2D w₀–wₐ deviation),
**NOT the significance of w<−1 / phantom crossing specifically** — the latter needs the 1D
projection with the joint w₀–wₐ covariance, not computed here. Direction reported only. Note: "measured g₀/H₀ ≈ 0.74" is **not a
measurement** — it is a translation of the CPL parameters through this very model
(g = 3H(1+w)) and depends on M; labeled as such.

## What this changes vs the route map / COSMOLOGY_W_BRIDGE

- At the homogeneous isotropic level, g(t) is **no longer a free function** — the action
  derives it, given M. This COMPLEMENTS COSMOLOGY_W_BRIDGE (which inverted DESI to *measure*
  g because it tested the phenomenological r187 ODE with g free); it does not contradict it.
  The measured g₀/H₀≈0.74 is the data; the derived g₀/H₀≤0.21 is the prediction; they
  disagree in magnitude (direction only).
- **Investigated (per review): does PF select a background? No.** PF constructs no dynamical
  cosmological gauge field — the `YangMills*.lean` corpus is spectral/mass-gap work (Stieltjes
  /Padé kernels, R_f(2,s)=ζ(s)), not a connection A^a_μ(x); no isotropic gauge ansatz exists
  anywhere (grep empty). The one cosmological Chern–Weil file,
  `PF/Cosmology/E6ChernWeil78piFirstPrinciplesAttempt.lean`, is a flagged ATTEMPT whose own
  docstring records that the Pontryagin integral (1/8π)∫Tr(F∧F)=78π is currently only an
  algebraic tautology / degenerate existential `∃N, N=78π`, that mathlib lacks Chern classes,
  Chern–Weil, and principal bundles entirely, and that this is "the deepest open in the entire
  PF Cosmology stack." So PF selects NEITHER branch; the Q=0 case is the trivial "no gauge
  field present," not a derived selection.
- **Genuinely still open:** (i) PF's gauge sector itself — group, connection, Q=0 vs
  non-Abelian (ch04 automorphism classification open; action does not fix F; the E6 Chern–Weil
  78π construction is PF's own deepest cosmology open); **this fork decides whether
  consciousness/topology affects the background at all**; (ii) M's value inside the window (no deeper principle selects a point);
  (iii) the sheaf-ch₂ (ch06, a number) vs gauge-Pontryagin-ch₂ (a density) identification;
  (iv) the full inhomogeneous C^μν (needs the manifold + localization map, still absent).

## Provenance
Derivation algebra and the exponential-quintessence reduction checked under my own hand;
background integrated numerically (scipy, Ω_m0=0.315, frozen-field IC, V₀ tuned to Ω_Λ0=0.685).
Lean stones cited: r187 (`lambdaEff_antitone`, hypothesis g≥0), r219 (`wEff`, `wEff_ge_neg_one`,
`cpl_nonphantom_forces_wa_bound`), ScreenedKernel (m², M-window). Chapter: ch27 §eos (posited
profile). No Lean built this pass; no claim depends on an unbuilt statement.
