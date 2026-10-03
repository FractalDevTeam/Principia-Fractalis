# STATUS SINCE THIS WAS WRITTEN — 2026-10-03, added on landing

This document was produced against a **stale, detached-HEAD mirror** (`60ddf275`).
Every claim below that bears on the book or the Lean tree was re-verified against
the live Acer `master` before landing, and the repairs it offered have been
**applied** rather than left as a list. What follows is the reconciliation; the
body of the document is unchanged.

## Confirmed, and acted on

- **The `ch_2` matrix bound is real and is now in the corpus.** The formula at
  ch06 `thm:neural-consciousness` has range `[−1/2, 1/2]` on every real matrix,
  so its own `> 0.95` gate is satisfied by **no** connectivity matrix and
  `Θ(ch_2 − 0.95)` is identically zero under it.
  `PF/Cosmology/VortexCavitationBridgeChecks.lean` is now **in-tree, built,
  gated PRISTINE** (all five criteria; `(b)` over 16/16 probeable declarations),
  and **wired into `PF.lean`**. The out-of-tree `/tmp` status recorded in §7 no
  longer applies.
- **The `−0.095` anchor has no definition anywhere.** Swept the live tree: the
  only 22 hits are `scipy`/`mne` **test data** inside an archived virtualenv —
  coincidence, not corpus. The unsigned `0.095` hits are exactly the
  `0.95 × 1/10` product, as §4.6 says.
- **ch10 Step 1, Step 3, Step 4 and the `ω_c` units**: all four confirmed by hand.
  Step 1's dropped ½ is now corrected in the displayed equation
  (`∂_j C_ij = ch₂ ΔΦ ∂_iΦ`, exactly), and `ν_eff` is relabelled a **postulate
  [II]**. Step 4's crossing point reproduces at `ch_2 = 0.0894`.
- **ch08 `dE/dt`**: confirmed dimensionally inconsistent *and* numerically
  unsupported — taken literally the formula gives `≈1.2×10⁵`, not `10⁻¹⁶`, in
  units of `J·m²·s⁻³·K⁻¹`.
- **ch22 `thm:topological-stability`**: confirmed false. Restated as the
  circulation invariance its proof actually establishes, with the **Crow
  instability** named.
- **The vortex Lean docstring** (`CounterRotatingVortices…:19`) called
  `ω₁ + ω₂ = 0` "total angular momentum vanishes". Corrected, and now backed by
  `counter_rotation_angular_momentum_zero_iff`.

## Two corrections to this document

1. **§4.2 overreaches on ch05 Prop `:139`.** The document calls the proposition
   "false as stated". It is not shown false: `v = (−y, x)` is a single planar
   centre, whereas the proposition concerns the meeting point of a counter-rotating
   **pair**. What *is* false — and the document is right about this — is the
   proof's parenthetical that a planar fixed point has zero curl. The distinction
   matters: a broken proof is not a false theorem.
   The proposition has been **re-proved**, not withdrawn, from the induced-velocity
   calculation: for circulations `Γ₁, Γ₂` at `(∓b/2, 0)` the midpoint velocity is
   `(Γ₁ − Γ₂)/(πb)`, which vanishes **iff `Γ₁ = Γ₂`** — the *co*-rotating case.
   Counter-rotation gives the *maximal* midpoint speed `2|Γ₁|/(πb) ≠ 0`. That is
   strictly sharper than the Poincaré–Bendixson argument it replaces.

2. **§8 item 4 under-states ch07.** It reports "total energy = 0 at emergence
   points" as contradicting a Lean theorem. The sharper and more damaging fact is
   that **ch07 contradicts itself two equations apart**: it sets
   `½|∇𝒱⁺|² + ½|∇𝒱⁻|²` to zero in the energy, then gives the same two gradients
   as `2|Γ/2πr|² ≠ 0` in the very next line. The corrected value is
   `ℰ(r₀) = ½𝓘 = |Γ/2πr₀|² ≠ 0`; only the *potential* term vanishes. Repaired in
   ch07 and in the ch08 intuitive box.

## Repairs applied (nine edits, six chapters)

ch05 `:139` proof + keyidea cross-reference · ch06 matrix-range remark and example
wording · ch07 emergence-point energy · ch08 intuitive box, `J^ν` divergence
constraint, `dE/dt` units · ch10 Step 1 algebra, consolidated `ν_eff` postulate
remark with the greenbox scoped, `ω_c` units · ch22 theorem restatement and proof
conclusion.

Every edit is a correction or a relabelling. **Nothing was withdrawn except two
arithmetic errors and one false statement of fact** (ch22's stability claim), and
in that case no weaker claim was substituted because the true behaviour is
instability. All fifteen cross-references introduced or cited were checked to
resolve, and every LaTeX environment in the six edited chapters balances.

## Still genuinely open — and these two are the author's

- **The flow → `(ch_2, Φ)` map with a physical scale for `Φ`.** This remains the
  blocking premise (§5.3), and the null result stands until it exists. Note it is
  now *worse* constrained than when this document was written: by
  `rem:Jnu-gradient-2026-10-03`, a region uniform in `𝒞` sources no momentum at
  all, so the map must supply a *gradient*, not merely a value.
- **Whether `−0.095` has an external derivation.** Inside the repository it has
  none, so it is not an anchor of anything. If the derivation exists outside, it
  is the missing premise; if it does not, the number should stop being cited.

One structural finding is worth carrying forward on its own: **`ch_2` is not a
single quantity across the book.** The matrix formula caps at `1/2`, the
normalised Chern–Weil density runs over `[0,1]`, and the entanglement form reaches
`1` on a Bell state. So `0.95` is reachable under some of the book's definitions
and provably unreachable under others, and which normalisation the threshold
belongs to is an open question of the framework's own statement. Recorded in
ch06 `rem:ch2-matrix-range-2026-10-03` rather than papered over.

---
# PF applied to double counter-rotating vortices: cavitation, energy, inertia, gravity

**Whole-TOE investigation — 2026-10-03.** Additive. No push, no merge, no commit.

**Verdict in one paragraph.** At the inspected commits, Principia Fractalis does
**not** yield a distinctive, quantitatively testable prediction for cavitation,
energy exchange, inertia or gravity in a counter-rotating vortex pair. The chain
from substrate to laboratory observable is broken at one identifiable place: there
is no map from a physical flow state to a substrate state (equivalently, to the
fields `ch_2(x,t)` and `Φ(x,t)` with a physical scale). With the only computable
`ch_2` formula the book supplies, the gate that switches the consciousness
stress on is provably closed for every flow, and the framework reduces to
ordinary Navier–Stokes. One observable survives as a *shape without a magnitude*:
a possible offset between true pressure and hydrodynamically reconstructed
pressure at the inception site. Everything else examined is either a postulate,
internally inconsistent, unit-dependent, or bounded far below measurement.

---

## 0. Provenance, scope, and how to read this

| | |
|---|---|
| Local commit inspected (this checkout, detached HEAD) | `60ddf275dc61977395c409435046d80a502fd5c1` (2026-09-19) |
| Live commit cross-checked (Acer, `master`, read-only) | `70c91411c9cd99b463fedc316c0e03d3d113a936` (2026-10-02) |
| Relation | **Diverged.** The local commit is not an ancestor of the live one; live is 94 commits past the merge base. |
| Line references | Local files. For ch05, ch07, ch08, ch11, ch14, and ch22 lines 1–612 the two commits are identical; ch10 and ch26 differ only in scope-note wording and the `Re_c` correction, not in any line cited here. |
| Running builds | Acer was running `lake build` jobs (r331d and box-0 panels) throughout. Nothing was written inside that repository. |
| Papers | Retrieved 2026-10-03 through an automated page summary, not from the PDFs. Every benchmark number below is marked **extracted** and must be re-checked against the PDFs before external use. |

Voice follows `codex/CANONICAL_VERDICT_LANGUAGE_2026-09-07.md`. The five strata
are kept apart throughout, labelled **[I]** substrate-derived, **[II]** postulated
law, **[III]** consequence of postulates, **[IV]** motivation, **[V]** empirical.
The mandatory caveat applies wherever "independent" or "not derived" appears:

> "Independent" means independent **relative to the formalized base theory and
> the exact constructions tested** — it does not establish independence from
> every future extension of Principia Fractalis.

The same limit applies to every negative result here: they are statements about
the book and Lean tree at the two commits above, and about the constructions
tested, not about every future extension.

Artifacts added (all untracked):

- `codex/PF_VORTEX_CAVITATION_WHOLE_TOE_INVESTIGATION.md` — this file
- `codex/pf_vortex_cavitation_calc.py` — every number in §2–§5 (stdlib Python)
- `PF_Lean4_Code/PF/Cosmology/VortexCavitationBridgeChecks.lean` — 11 theorems, status in §7

---

## 1. Whole-framework dependency map

Each row states what the branch **actually contributes** to the vortex question:
an equation, a parameter constraint, an observable, or nothing.

### 1.1 The chain

| # | Layer | Source | Stratum | Actual contribution to the vortex chain |
|---|---|---|---|---|
| 1 | Substrate: `T_∞`, UHF tower, unique trace with range `ℤ[1/3]` | ch04 Def 4.2–4.6, Thm 4.7; `TimelessField.lean`, `SubstrateAutQuotientCollapse.lean` | **[I]** | **Inactive.** No spatial coordinate, no time, no dimensional scale. Supplies nothing a flow can be mapped onto. |
| 2 | Spacetime emergence `M⁴ = Aut(T_∞)/Aut₀(T_∞)` | ch04:455 Thm 4.18 | **[II]**, refuted as stated | **Inactive.** The quotient is a single point: `tracePreserving_eq_top`, `substrateAutQuotient_subsingleton` (local HEAD commit; header reports a targeted build with clean axioms — not rebuilt here). Live ch04 carries the correction. No manifold, so no `x`, no `∇_μ`. |
| 3 | Selection laws: eight α-laws, values `α_NS = 3π/2`, `α_QG = √(2π)` | canonical verdict §2; ch03:231 | **[II]** → **[III]** | **Parameter labels only.** `α` enters as the argument of `R_f(α, s)`. No α-value multiplies any fluid quantity. |
| 4 | Resonance `R_f(α,s) = Σ e^{iπαD₃(n)} n^{-s}` | ch03:93 | **[I]** as mathematics | **Kernel domain mismatch.** `s` is a complex Dirichlet variable. ch08:205 and ch26:167 evaluate `R_f(√(2π), |x|)` at a *length*; ch22:247 at an *integer scale gap*. No unit conversion is given, so the kernel has no physical domain. |
| 5 | `ch_2` and the 0.95 threshold | ch06:146 (sheaf), :285–311 (normalized Chern–Weil, range `[0,1]`), :476 (matrix), :517 (entanglement); `ChernWeil.lean:24` | **[II]**; ch06:464 labels 0.95 an untested hypothesis | **Four inequivalent definitions.** Only the matrix formula can be evaluated on flow data. See §2.2 and §4.6. |
| 6 | Emergence / topology (Peixoto) | ch05:131–137, Prop :139, Thm :180 | **[II]/[IV]** | **A criterion, not a force:** "emergence point" = `|v| = 0`, `∇×v ≠ 0`. See §4.2: this is the axis of any vortex. |
| 7 | Vortex-pair structure | ch07:456–494; ch22:73 Def, :95, :194, :230, :257 | **[II]**; ch22:512–514 labels it asserted | **A geometry** (nested, `Γ_inner = −Γ_outer`) and a `3^{-n}` hierarchy. No equation of motion beyond NS. |
| 8 | Fluid dynamics | ch10:48–50 (`C_{μν}`), :61 (modified NS), :66 (`ν_c`), :83 Lemma, :163 Thm | **[II]**; ch10:320 "untested empirical postulate" | **The only fluid-level equation PF adds:** `∂_t u + u·∇u = −∇p + νΔu + ∂_j C_ij`, with claimed `ν_eff = ν[1 + (π/10)(0.95 − ch_2)]`. Analysed in §2.3. |
| 9 | Stress and sector exchange | ch08:79 Def, :108 Thm, :133 action, :198 Thm, :261 Thm | **[II]** | **`C^{μν}` gated by `Θ(ch_2 − 0.95)`**, a source `J^ν`, and discrete quanta `Q_ν^{(i)}` of unstated size. Analysed in §2.4, §4.3. |
| 10 | Gravity / inertia | ch08:198–205; ch14:93; `ModifiedFriedmann_r187.lean`; `GeneralRelativity.lean:76–84` | **[II]**; Lean GR props self-flagged vacuous | **FLRW-reduced ODE only** is kernel-checked. No local (laboratory) solution exists in book or Lean. Bounded in §2.5. |
| 11 | Cosmological observable | ch26:167, :246, :261; `LambdaEffTypedUpgrade.lean:152` | **[III]** of a fit; ch26:261 "engineered, not derived" | `Λ_eff/Λ_0 = exp(−78π·0.95·1.1875)`. A calibration to a known number. |
| 12 | Laboratory observable | ch10:455–482; ch22:491–500 | **[V]**, none preregistered | Three "signatures" in ch10 (spectral cutoff, `d_f`, `⟨ch_2⟩`). **None concerns cavitation, vortex pairs, inertia or gravity.** "cavitation" does not occur in either commit. |

### 1.2 Side branches

| Branch | Source | Actual contribution |
|---|---|---|
| Geometric Unity / BRST | ch11:256–326; `WeinsteinGUResonantRescue.lean` | The integer `78 = 48 + 26 + 4`, used once, as the `78π` in row 11. `E6ChernWeil78piFirstPrinciplesAttempt.lean` records that `78π` is not derived from a bundle. ch11:462 records both routes to `ch_2 = 0.95` as refuted at their numerical close (the Gaussian gives 0.7837). **Inactive for fluids.** |
| Mallett / Φ-vortex | ch11:540–585 | A frame-dragging ansatz `g_tφ = (4G/c⁴) ρ_Φ R_f ω_Φ` for circulating light. Carries the ordinary factor `G/c⁴`; no amplification. **No fluid content.** |
| Symmetries and conservation | ch14:93, :135–170, :203 | Noether's theorem (standard). ch14:93 gives the energy-exchange law used in §4.3. Angular momentum is conserved as usual: **constrains** the chain (§4.1), adds nothing. |
| Millennium axis: NS | ch22:366, :512; `NSCapstoneTypedBridge.lean` | Global regularity is open; the vortex-emergence argument is labelled heuristic. Regularity statements say nothing about pressure minima. **Inactive.** |
| Millennium axes: RH, YM, BSD, Hodge, P vs NP | Referee theorem C1–C6 | **Inactive.** No shared variable with the flow. |
| Churn → stress tensor | `codex/CHURN_TO_STRESS_TENSOR_BRIDGE_AUDIT_2026-09-14.md` §2.3–§2.8 | Already establishes: no localization map (L3), no manifold (L4), and a scalar cannot determine a rank-2 tensor (L5). The present finding is the fluid-side instance of the same gap. |
| Referee capstone C18 | `PrincipiaFractalisSubstrateTheorem.lean:292, :394` | The vortex bundle is one conjunct; the antecedent is discarded (`intro _h_antecedents`), as the file's own audit note states. **No derivation from substrate to vortex.** |

### 1.3 What the existing vortex Lean file proves

`CounterRotatingVorticesZeroPointFreeEnergy.lean` is real-number arithmetic:
`ω₁ + ω₂ = 0`, `ω₁² + ω₂² > 0`, `exp(X) > 1`, `2 < exp(X)`, and
`(E·e^X)·e^{−X} = E`. Its docstring is accurate that it "does NOT claim
laboratory extractability". Three points need recording:

- Line 19 says the pair's "total angular momentum vanishes (`ω₁ + ω₂ = 0`)". Angular velocity is not angular momentum (§4.1).
- `FreeEnergyExtractable` compares `ω₁² + ω₂²` (units s⁻²) with the pure number `exp(276.44)`. Its truth value changes with the unit of `ω` (§4.4).
- Clause C5 multiplies by `e^X` and then by `e^{−X}`. It is an identity about any real number and encodes no coupling.

---

## 2. Macro and micro analysis

### 2.1 Macro: what a counter-rotating pair is in ordinary hydrodynamics

For two line vortices of circulation `±Γ`, core scale `a`, separation `b`
(Lamb–Oseen profile `u_θ = Γ(1 − e^{−r²/a²})/(2πr)`):

- core pressure deficit `p_∞ − p(0) = ρΓ² ln2 / (4π²a²)`;
- laminar core growth `a²(t) = a₀² + 4νt`;
- velocity at the midpoint `2Γ/(πb)`, **nonzero** — the induced velocities add;
- linear impulse per unit length `ρΓb`, nonzero; the pair self-propels at `Γ/(2πb)`;
- long-wave (Crow) instability, stretching of the weaker vortex, `a` shrinking at conserved `Γ`, and `Δp ∝ Γ²/a²` rising. This is the inception mechanism both benchmark papers report (§3).

### 2.2 Micro: the only computable `ch_2`, applied to a velocity gradient

The book gives one formula that takes a real matrix and returns a number
(ch06:476): `ch_2(W) = (Tr(W²) − (Tr W)²) / (2‖W‖_F²)`.

Put `W = ∇u = S + A` (strain plus rotation). Incompressibility gives `Tr W = 0`, so

```
ch_2(∇u) = (‖S‖² − ‖A‖²) / (2(‖S‖² + ‖A‖²)) = −Q / ‖∇u‖²  ,   Q = ½(‖A‖² − ‖S‖²)
```

`Q` is the standard Q-criterion, and `∇²p = 2ρQ`. So under this map `ch_2` is
minus the normalized pressure Laplacian.

**Kernel-checked consequences** (§7; no hypothesis on `W` for the first):

- `ch2Matrix_le_half`: `ch_2(W) ≤ 1/2` for every real square matrix.
- `neg_half_le_ch2Matrix_of_trace_eq_zero`: `ch_2(W) ≥ −1/2` when `Tr W = 0`.
- `ch2Matrix_lt_threshold`: `ch_2(W) < 19/20`. **The gate is unreachable.**
- `ch2Matrix_pureRotation = −1/2`, `ch2Matrix_pureStrain = +1/2`: both bounds are attained.

Numerically for a Lamb–Oseen vortex (script S5): `ch_2 = −0.500` on the axis,
`0` at `r = 1.1209a` (the velocity maximum), `+0.500` in the far field.
The vortex axis — the book's emergence point — sits at the value **farthest**
from 0.95. The book's own worked example (ch06:488–506) returns 0.50, which is
the maximum the formula allows.

*Status of the map:* "flow ↦ `ch2Matrix(∇u)`" is **my construction** from the
book's formula, tested because it is the only evaluable candidate. It is not a
claim the book makes. The book's other three definitions give no value for a flow.

### 2.3 Micro: the Consciousness Regularization Lemma (ch10:83–135)

This lemma is the sole source of the fluid-level number `ν_eff`. Three defects,
each checkable by hand:

1. **Step 1 algebra (ch10:94–100).** For constant `ch_2`,
   `∂_j[ch_2(∂_iΦ ∂_jΦ − ½δ_ij|∇Φ|²)] = ch_2 ΔΦ ∂_iΦ`, exactly. The book's extra
   term `(ch_2/2)∂_i|∇Φ|²` comes from writing `∂_i|∇Φ|²` where `½∂_i|∇Φ|²`
   belongs. The force is `f = ch_2 ΔΦ ∇Φ`: it depends on `Φ` and not on `u`.
2. **Step 3 closure (ch10:116–129).** Substituting `ΔΦ = −(10/π)ΦΨ_FRO` gives
   `f = −(5/π) ch_2 Ψ_FRO ∇(Φ²)`. With `Ψ_FRO` uniform — the case the proof
   uses, via `C_Φ = inf Ψ_FRO` — this is a **pure gradient**. A pure gradient
   does zero work on a divergence-free velocity field, `∫ u·∇g = 0`. The claimed
   bound `∫ u_i ∂_j C_ij ≤ −(π/10)ν_c‖∇u‖²` therefore fails for any flow with
   `∇u ≠ 0` and `ν_c > 0`: the left side is zero.
3. **Step 4 (ch10:131–136).** The step asserts
   `(10/π)·ch_2·0.95 ≈ (π/10)(0.95 − ch_2)`. The left side rises from 0 to 2.87
   as `ch_2` goes 0 → 0.95; the right side falls from 0.298 to 0. They agree
   only at `ch_2 = 0.0894` (script S2).

Consequently `ν_eff = ν[1 + (π/10)(0.95 − ch_2)]` is a **postulate [II]**, not a
consequence of the stated stress tensor. Under the lemma's own closure the
stress adds no dissipation. Its entire effect is a pressure offset (§5.2).

**Dimensional consistency.** `ℓ_c = √(ν_c/ω_c)` with `ω_c = π/10` (ch10:442) has
units of length only if `ω_c` is a frequency, and no unit is stated ("units
where `ν = 1`" fixes one combination of length and time, not both). The value
is unit-dependent: for water at `ch_2 = 0.60`, `ℓ_c` = 1.06 mm, 33 µm or 63 mm
for `π/10` per second, per millisecond or per hour (script S3). The book's air
example evaluates to 1.5 mm, not the printed 1.0 mm.

### 2.4 Micro: the stress, the gate and the measure

`C^{μν} = ∫_{T_∞} ⟨ω|T̂^{μν}|ω⟩ Θ(ch_2(ω) − 0.95) R_f(α_ω, s) dμ(ω)` (ch08:79).

- `T̂^{μν}` and `dμ` are not constructed (bridge audit B11, N5).
- ch10:48–50 gives a *different* tensor, `ch_2(∂_μΦ∂_νΦ − ½g_{μν}(∂Φ)²) + ch_2² g_{μν}V(Φ)`, with **no gate**. ch08 and ch10 disagree on whether sub-threshold matter is coupled at all.
- ch22:401–405 asserts `ch_2(ℰ) = 0.95 + 0.05·H(ℰ)/H_max` at emergence points. The set of emergence points has dimension `log2/log3 ≈ 0.631` (ch22:257), hence zero volume. A bounded integrand supported there contributes nothing; a nonzero contribution requires the delta-supported quanta `Q_ν^{(i)}` of ch08:261, whose magnitude is nowhere given.

### 2.5 Macro: gravity and inertia, bounded

All four numbers are from script S7.

| Quantity | Value | Meaning |
|---|---|---|
| Kinetic energy density of the benchmark flow (`u = 10 m/s`) | `5.0×10⁴ J/m³` | |
| Its mass-equivalent over rest mass | `5.6×10⁻¹⁶` | Ordinary GR source change; no PF term amplifies it. |
| Observed vacuum energy density `Λ_obs c⁴/(8πG)` | `5.3×10⁻¹⁰ J/m³` | The **most** that suppressing `Λ_eff` to zero in a region can exchange. One-off, not a power. |
| De Sitter acceleration `Λ_obs c² r/3` at 1 m | `3.3×10⁻³⁶ m/s²` | The **most** that local suppression can change `g`. Gravimeters resolve about `10⁻¹¹ m/s²`. |

Raising local `ch_2` *lowers* `Λ_eff`. The bare reservoir `Λ_0` is reached only
by lowering `ch_2` everywhere, and by ch14:93 raising `Λ_eff` *costs* matter
energy. The reservoir is not a source in either direction.

Transplanting the ch26:246 normalization to one litre at `ch_2 = 0.85` gives an
exponent `2×10⁴⁶`, against 276 for the observable universe. The normalization
was built for one number and has no laboratory reading (ch26:261 says as much).

---

## 3. The two public studies

Both study the **same configuration**: tip vortices of two hydrofoils, mounted
side by side, of unequal strength and opposite sign, convecting downstream at
chord Reynolds number about `1.7×10⁶`. The first is a simulation of the
experiment in the second group's facility.

| | Madabhushi & Mahesh, JFM **1027** A15 (14 Jan 2026) | Knister, Ganesh & Ceccio, JFM **1034** A37 (5 May 2026) |
|---|---|---|
| Method | Incompressible LES, dynamic Smagorinsky, overset grids, ~1.4×10⁹ cells, finest `h = 0.0007c` | Volumetric PTV (shake-the-box + VIC#), high-speed video, hydrophone at 500 kHz, cavitation susceptibility meter |
| Geometry | One flat-tipped rectangular foil, one tapered rounded-tip foil; `c = 169 mm`; circulation ratio about −0.5 | Two cambered NACA66 foils, `c = 167 mm`; primary at +6°, secondary at 0°, −2°, −4°; matching and tapered planforms |
| Measured / computed | `C_p` fields; vapour threshold `C_{p,v} ≈ −2.0`; instantaneous core `C_p` down to −2.4…−3.0; mean minimum about −0.75 at `x/c = 0.7` | Core pressure from velocimetry; inception event rates; "pop" and 3.1–3.3 kHz "chirp" acoustics; nuclei spectra; `σ = 1.34–2.14` |
| Where inception occurs | Weaker vortex, `x/c = 1.1–1.7`, once per Crow cycle, lasting ~3% of the cycle | Secondary (weaker) vortex cores |
| Mechanism | Crow instability (`λ/c ≈ 0.3`) → stretching → core radius down ×1.5 → pressure down 3–4×; lowest pressure where axial stretching is *lowest* | Core radius down 30–50%; pressure drop tracks `Γ²/r_c²` (correlation −0.85 to −0.90), not axial jetting |
| Assumptions | No multiphase model; inception ≡ `C_p < C_{p,v}`; Lamb–Oseen core definition | Spherical gas nuclei (Blake radius); negligible nuclei capture and diffusion; isolated line-vortex pressure model |
| Uncertainty | Grid convergence < 3% in minimum pressure; 4 Crow cycles, 4 events | Pressure reconstruction ~10%; nuclei population a factor ~4; rate prediction within a factor 2–3, under-predicted for case N.4 |
| Data / code | No availability statement found | Supplementary movies; no data or code statement found |

All entries **extracted**. One inconsistency to resolve at the PDF: the summary
gave an 11 mm trailing-edge separation, while `λ/c ≈ 0.3` with `λ/b₀ ≈ 3`
implies `b₀ ≈ 17 mm`. The circulation `Γ ≈ 0.264 m²/s` used in §5 is
**inferred** by me from the mean `C_p`, not taken from either paper.

### 3.1 Four geometries, kept distinct

| Geometry | Description | Zero-velocity point with `ω ≠ 0`? | Total circulation | Who uses it |
|---|---|---|---|---|
| **A. Side-by-side tubes** | Two parallel line vortices, opposite sign, separation `b` | **No.** Midpoint velocity is `2Γ/(πb)`. Co-moving stagnation points lie in irrotational fluid. | `Γ₁ + Γ₂`; nonzero when strengths differ | Both benchmark papers |
| **B. Nested counter-rotation** | Inner vortex inside a coaxial outer vortex, `Γ_inner = −Γ_outer` | Yes, on the common axis — as for any single vortex | Zero by definition | ch22:61–91 (PF's definition) |
| **C. Coaxial vortex rings** | Two rings on one axis, opposite circulation (head-on collision) | On the axis by symmetry, in irrotational fluid | Zero per meridional plane | Not in either paper; ch10:493 mentions rings only to assert `ch_2 ≈ 0.85` |
| **D. Solid rotors** | Two rigid bodies, `ω₂ = −ω₁` | Not a fluid | n/a | `CounterRotatingVortexPair` in Lean (two scalars) |

**Which benchmark matches PF's geometry: neither.** Both papers are geometry A
with unequal strengths. PF's formal definition is geometry B; its Lean object is
geometry D; ch07 and ch08 use loose "pair" language that resembles A, but the
property they rely on — cancellation at the meeting point — does not hold in A.
No public benchmark for geometry B was sought or found in this pass.

---

## 4. Cross-branch consistency findings

### 4.1 (a) Opposite angular velocities do not cancel angular momentum

`L = I₁ω₁ + I₂ω₂ = (I₁ − I₂)ω₁` when `ω₂ = −ω₁`. **Kernel-checked:**
`counter_rotation_angular_momentum_zero_iff` — zero iff `ω = 0` or `I₁ = I₂`.
For geometry B with uniform patches and `R_out = 2R_in`,
`L_z = −¾ ρΓR_in²` per unit length (script S6). For geometry A, angular impulse
about the midpoint vanishes for equal strengths but linear impulse `ρΓb` does not.
Affected text: Lean file line 19; ch22:194–200, which also cites Kelvin's
theorem (a statement about circulation on material loops) as if it gave
stability at all Reynolds numbers. Both benchmarks observe the Crow instability
in the configuration that theorem would call stable.

### 4.2 (b) A zero-velocity point does not establish zero total energy

- **Kernel-checked:** `counter_rotation_energy_pos` — `½I₁ω² + ½I₂ω² > 0`. The existing Lean file already proves `ω₁² + ω₂² > 0`; ch07:451, ch08:270 ("total energy = 0") contradict the project's own theorem.
- ch07:478–485 evaluates an energy density at one point and reads it as "total energy at emergence point". The same lines give `|∇𝒱^±|² = (Γ/2πr)²` at `r → r₀`, which diverges rather than vanishing.
- The criterion `|v| = 0, ∇×v ≠ 0` holds on the axis of **every** axisymmetric vortex, including a two-dimensional one: for `v = (−y, x)` the origin has `v = 0` and curl 2. ch05 Prop :139 ("cannot exist in two-dimensional phase space") is therefore false as stated; its proof assumes a fixed point must have zero curl.
- Physically that locus is the pressure minimum, which is where cavitation begins. PF's "emergence point" and the classical inception site coincide; PF attaches no pressure term to it.

### 4.3 (e) Source current versus the divergence of the gravity equation

Take ch08:198: `G_{μν} + Λ_eff g_{μν} = 8πG(T_{μν} + C_{μν})`. Apply `∇^μ`,
using the Bianchi identity and `∇g = 0`:

```
∂_ν Λ_eff = 8πG ∇^μ(T_{μν} + C_{μν}) = 8πG J_ν        ⇒   J_ν = ∂_ν Λ_eff / (8πG)
```

Three consequences:

1. `J_ν` must be an **exact gradient**. The current defined at ch08:108–114, a sum of `δ⁴(x − x_i)` terms, is not the gradient of a function. The two definitions of `J` are incompatible.
2. `Λ_eff` is defined as an integral over a whole slice `Σ` (ch08:205), so it depends on the slice alone: `∂_i Λ_eff = 0`, hence `J_i = 0`. **A self-consistent PF has no momentum source** — no thrust and no inertia modification for any apparatus.
3. The energy component is `J_0 = Λ̇_eff/(8πG)`, which is ch14:93 up to the factor `8πG`. The work rate of the extra stress is fixed by `Λ̇_eff` and capped by the total in §2.5.

The derivation at ch08:139–143 varies an action with **constant** `Λ` and then
states the result with `Λ_eff(𝒞)`. A field-dependent `Λ_eff` inside the action
would add terms to the `𝒞` equation that the book does not write.

### 4.4 (c) A reservoir inequality does not establish extractable power

`FreeEnergyExtractable pair := ω₁² + ω₂² < exp(X)`. **Kernel-checked:**
`reservoir_inequality_not_scale_invariant` — for any `R > 2` the inequality
`2ω² < R` holds at `ω = 1` and fails after rescaling the unit of `ω` by `R`.
A statement that flips under a change of units is not about physics. Separately,
`A < B` between an energy and a reservoir carries no rate, no coupling and no
direction of flow. ch08:290 supplies the only rate, `c²·k_B·(d ch_2/dt)·N`; its
units are `J·m²·K⁻¹·s⁻³`, not watts, and with the stated inputs it evaluates to
`1.2×10⁵` in those units, not the printed `10⁻¹⁶ J/s` (script S8).

### 4.5 (d) Vacuum-term suppression does not determine local gravity or inertia

Covered by §2.5 and §4.3(2): the suppression is a global functional, its spatial
gradient vanishes, and its largest possible local effect is `3.3×10⁻³⁶ m/s²`
per metre.

### 4.6 The −0.095 anchor against the +0.95 threshold

Traced by full-history search in this checkout and by `git grep` at the live commit.

| Number | Where it is defined | Convention |
|---|---|---|
| **+0.95** (= 19/20) | ch06:180, :197 (called a "phenomenological anchor"); ch08:79; `TimelessField.lean` `CrystallizesConsciousness`; `ChernWeil.lean:20` | Threshold on a **normalized** `ch_2 ∈ [0,1]` (ch06:311; Lean stub `bounded : 0 ≤ value ∧ value ≤ 1`) |
| **−0.095** | **Nowhere in either current tree.** One historical occurrence: `VERIFICATION_ASSESSMENT_TURING_COMPLETENESS.md`, added in commit `d58c8e5c` (2025-11-19), removed in `8f0704f8` | Inside a block headed "MISSING … NEEDED": `theorem chern_enables_computation : ch₂ = -0.095 → enables_universal_computation Φ`. A wish-list statement about Turing universality. Never defined, never derived, no fluid or cosmological context. |
| **0.095** (unsigned) | `FrameworkExperimentalWinsCapstone.lean:170` (`1 + 0.095·π`); `BookEval019Discharge.lean:58` (`sin 0.405π = cos 0.095π`) | The product `0.95 × (1/10)` from the `π/10` factor. Not a Chern quantity. |

Reconciliation:

- −0.095 and +0.95 are **not** two conventions for one quantity. No definition, sign convention or version in the tree maps one to the other. The factor of ten and the sign have no source.
- Under the normalized Chern–Weil definition and under the Lean stub, a negative `ch_2` is **inadmissible**.
- Under the matrix formula (§2.2) the admissible range is `[−½, ½]`: −0.095 is attainable (it is the value where `‖A‖²/‖S‖² = 1.469`), and **+0.95 is not**.
- So each number is admissible only under a definition that excludes the other. They cannot both be anchors of one scalar. Neither was substituted for the other anywhere in this analysis: +0.95 is used wherever the book uses it, and −0.095 is used nowhere, because the tree gives it no meaning.

If −0.095 has a derivation outside the repository, that derivation is the input
this investigation is missing (§6 decision 2).

### 4.7 Scalar, score, Chern quantity, tensor, stress

| Object | Type | Relation actually established |
|---|---|---|
| Information field `ℐ` (ch07:488–490) | scalar density | Defined pointwise as `|∇𝒱⁺|² + |∇𝒱⁻|²`; no link to `ch_2` |
| Threshold score `Θ(ch_2 − 0.95)` | `{0,1}` | A gate on the integrand of `C^{μν}`; closed under §2.2 |
| Chern quantity `ch_2` | four inequivalent scalars | None shown equal to another |
| Tensor `C^{μν}` | symmetric rank 2 | Postulated; ch08:79 and ch10:50 differ; a scalar cannot fix its nine traceless components (bridge audit §2.8, commit `8597f848`) |
| Stress in the fluid | `∂_j C_ij` | With the ch10 form, a pure gradient under the book's closure (§2.3) |

### 4.8 The ordinary hydrodynamic limit

PF reduces to incompressible Navier–Stokes exactly when `∂_j C_ij` is a gradient
or zero. That holds (i) under the matrix map, where the gate is closed; (ii) for
`Φ` constant; (iii) under the ch10 Step-3 closure with uniform `Ψ_FRO`. In case
(iii) the velocity field is unchanged and only the pressure is offset. No case
in the book produces a velocity-level departure from Navier–Stokes with a
derived magnitude.

---

## 5. Quantitative prediction, or what prevents one

### 5.1 The one fluid-level number, taken at face value

Treat `ν_eff = ν[1 + (π/10)(0.95 − ch_2)]` as a postulate despite §2.3, and ask
what it does in the benchmark (script S4).

| Step | Value |
|---|---|
| Weaker-core Lamb–Oseen scale `a₀ = r_c/1.1209` | 5.71 mm |
| Transit time `x/c = 0.67 → 1.7` at 10 m/s | 17.4 ms |
| Laminar growth `4νt/a₀²` | `2.1×10⁻³` |
| Largest PF addition (`ch_2 = 0`, factor 0.298) | `6.4×10⁻⁴` in `a²`, hence in `Δp` |
| Shift at `C_p = −2` | `|ΔC_p| ≈ 1.3×10⁻³` |
| Benchmark resolution | ~10% (PTV pressure), <3% (LES grid) |
| Ratio | **PF shift is ~157× below the experimental uncertainty** and ~47× below the LES grid error |

At this Reynolds number core evolution is governed by stretching and turbulent
transport, which do not depend on molecular viscosity, so the true sensitivity
is smaller still. A uniform multiplier on `ν` is also unobservable in principle:
any viscometer measures `ν_eff`. Only *differences* in `ch_2` between flow
classes could show, and the book assigns no `ch_2` to a vortex pair.

**Conclusion:** the benchmark papers neither support nor constrain this term.

### 5.2 The strongest thing the chain supports: a pressure-offset observable

From §2.3, under the book's own closure the consciousness force is
`−∇[(5/π) ch_2 Ψ_FRO Φ²]`. Then the Navier–Stokes pressure `p_NS` (what the
velocity field implies, and what velocimetry reconstructs) and the true pressure
differ:

```
Π(x) ≡ p_true − p_NS = −ρ (5/π) ch_2 Ψ_FRO Φ(x)²        [per the ch10 closure]
```

| | |
|---|---|
| Observable | `Π` at the inception site: measured inception pressure minus pressure reconstructed from the velocity field |
| Units | Pa |
| Ordinary physics | `Π = 0`, apart from known corrections (nuclei tension, unresolved fluctuations) |
| PF value | **Undetermined.** Requires the amplitude of `Φ` in physical units and `Ψ_FRO`; the book fixes neither. The sign is fixed (true pressure lower, inception earlier) only if `ch_2 Ψ_FRO > 0`. |
| What existing data say | Knister et al. predict event rates from reconstructed pressure plus measured nuclei and agree within a factor 2–3. With nuclei uncertain by a factor ~4, this cannot resolve offsets below roughly `10⁴ Pa` (10% of `|C_{p,v}|q`, script S9). Order of magnitude only; not a formal limit. |
| Prospective falsification criterion | Not statable until `Φ` has a scale. Once a premise gives `Π₀` in pascals: PF is refuted in this channel if the measured offset is consistent with zero at a resolution finer than `Π₀`. |

This is a structural consequence **[III]** of a postulated tensor and a
postulated closure **[II]**. It is not evidence, and it is not yet a prediction.

### 5.3 The smallest missing premise, and exactly where it enters

> **(P★) State map with scale.** A rule assigning to a physical flow state
> `(u, p, ρ)` at `(x, t)` the framework fields `ch_2(x,t)` and `Φ(x,t)`, with a
> stated physical unit for `Φ` (equivalently, a value in s⁻¹ for `ω_c`).

It enters at four places, and nowhere else:

| Entry point | What is undetermined without (P★) |
|---|---|
| ch08:79, `dμ(ω)` and `⟨ω|T̂^{μν}|ω⟩` | Which substrate states a flow populates; hence all of `C^{μν}` |
| ch10:48–50, `Φ` in `C_{μν}` | The stress magnitude; hence `Π` in §5.2 |
| ch10:118–121, `ΔΦ = −(10/π)ΦΨ_FRO` | Whether `Φ` responds to `u` at all — without that, no work rate (check e) |
| ch10:442, `ω_c = π/10` | The physical length `ℓ_c`; hence every spectral signature |

(P★) is the fluid-side form of layer L3 in the churn bridge audit. It is a
physical postulate; nothing in strata [I]–[III] supplies it. Two things are
already known about any candidate:

- If (P★) reads `ch_2` off `∇u` by the ch06:476 formula, the gate is closed for every flow (kernel-checked) and PF predicts **exactly** ordinary hydrodynamics plus, at most, the ungated ch10 term.
- If (P★) is to open the gate, it must use a definition of `ch_2` under which a moving fluid reaches 0.95, and the book offers none that can be evaluated on a fluid.

### 5.4 A conditional chain, for completeness

If one adopts **both** the matrix map and the `ν_eff` postulate (neither
derived, the first not in the book), a number follows without any free
coefficient: a viscometer measures simple shear (`ch_2 = 0`), a vortex axis is
pure rotation (`ch_2 = −½`), so laminar core growth would be

```
d(a²)/dt = 4 κ ν_visc ,   κ = [1 + (π/10)(1.45)] / [1 + (π/10)(0.95)] = 1.121
```

against `κ = 1` in ordinary hydrodynamics. A laminar vortex experiment
(`Re_Γ ≲ 10⁴`) resolving the growth rate to ±5% would decide it: `κ` within
`[0.95, 1.05]` refutes the chain. My expectation is that published laminar
vortex data already sit at `κ ≈ 1`; I did not retrieve such data in this pass,
so that is an expectation, not a finding. This chain is listed so that it is not
later mistaken for a PF prediction: it rests on two postulates and on §2.3
being set aside.

---

## 6. Next executable research step

**One step, bounded:** write (P★) down, or record that it is not available.

1. **Decision (Pablo):** state the intended flow → `ch_2` map. Candidates: the ch06:476 matrix formula on `∇u` (then the result of this document is final: null); a different formula (then supply it); none yet (then the vortex sector is recorded as stratum **[IV]** motivation).
2. **Decision (Pablo):** state the source of the −0.095 anchor. If it comes from a calculation, the calculation and its `ch_2` definition are needed; under the matrix formula it corresponds to `‖A‖²/‖S‖² = 1.469`, which names a specific location in a vortex and would itself be a candidate for (P★).
3. **If a map is supplied:** the calculation script takes it in one function. Compute `Π(x)` (§5.2) on the published LES geometry, state `Π₀` in pascals with its uncertainty, and register the decision rule before requesting data from either group.
4. **Independent of 1–3, book repairs this investigation makes available:** ch10 Lemma (Step 1 algebra, Step 3 zero-work, Step 4 monotonicity, `ω_c` units); ch05 Prop :139; ch07:478–485 and ch08:270 ("total energy = 0"); ch08:290–297 (units and arithmetic); ch22:194 (Kelvin's theorem); the docstring at line 19 of the vortex Lean file. None is applied here.

Resource ceiling for step 3: one working session. Stopping condition: a number
in pascals with a decision rule, or a written statement that `Φ` has no scale.

---

## 7. Verification record (§B0)

**Module:** `PF_Lean4_Code/PF/Cosmology/VortexCavitationBridgeChecks.lean`
(mathlib-only imports; sha256 `4e6bcc64…f418b0`).

| | |
|---|---|
| Toolchain | `leanprover/lean4:v4.24.0-rc1` |
| Mathlib | `eed770a434957369c6262aa3fb1d6426419016d4` (the live project's pinned package) |
| Command | `lean --root=/tmp/pf_vcb -o VortexCavitationBridgeChecks.olean VortexCavitationBridgeChecks.lean`, with `LEAN_PATH` from the live project's `lake env`, at `nice 19`, in `/tmp` on the Acer |
| Result | exit 0; `.olean` written (548 kB, sha256 `abb099a6…f23c3cf`); no errors, no warnings |
| `#print axioms` | all 11 theorems: `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no `ofReduceBool` |
| Source scan | no `sorry`, `admit`, `native_decide`, `axiom` |

**What this does and does not meet.** An olean exists and the axiom report is
clean, so the 11 statements are kernel-checked. They were checked
**out of tree**: not through `lake build PF.Cosmology.VortexCavitationBridgeChecks`,
not imported by `PF.lean`, not committed. Directive §7's "committed provenance
and clean rebuild from committed source" is therefore **not** met, and the
olean in `/tmp` is not a durable artifact.

| Theorem | Statement | Binders |
|---|---|---|
| `ch2Matrix_le_half` | `ch2Matrix W ≤ 1/2` | `W` only |
| `neg_half_le_ch2Matrix_of_trace_eq_zero` | `−1/2 ≤ ch2Matrix W` | `W`, `W.trace = 0` |
| `ch2Matrix_lt_threshold` | `ch2Matrix W < 19/20` | `W` only |
| `thresholdGate_ch2Matrix_eq_zero` | gate is 0 | `W` only |
| `gated_source_eq_zero` | `T * gate = 0` | `W`, `T` |
| `ch2Matrix_pureRotation` | `= −1/2` | none |
| `ch2Matrix_pureStrain` | `= 1/2` | none |
| `counter_rotation_angular_momentum_zero_iff` | `I₁ω + I₂(−ω) = 0 ↔ ω = 0 ∨ I₁ = I₂` | reals |
| `exists_counter_rotating_with_angular_momentum` | a witness | none |
| `counter_rotation_energy_pos` | energy `> 0` | `I₁, I₂ > 0`, `ω ≠ 0` |
| `reservoir_inequality_not_scale_invariant` | flips under rescaling | `R > 2` |

These are elementary. Their weight is in what they are *about*: the book's own
formula and the existing Lean definitions. None formalizes an experimental
effect, and none is derived from the substrate.

**Not verified in this pass:** the pre-existing modules cited in §1 were read,
not rebuilt (this checkout has no `.lake`). Claims about them rest on their
source and on their headers' own build statements.

---

## 8. Summary in directive §10 order

1. **Central claim status.** "Applying the whole TOE to counter-rotating vortices yields a distinctive testable prediction": **not established.** The chain is underdetermined at one premise, (P★).
2. **What became proved (olean + clean axioms, out of tree).** The 11 theorems of §7 — chiefly that the book's matrix `ch_2` never exceeds 1/2, so the 0.95 gate is closed on every real matrix.
3. **What is written, not proved.** Everything in §2.3, §4.3, §5: hand derivations and a numerical script. The Bianchi argument, the zero-work argument and the pressure-offset formula are **not** formalized.
4. **What became weaker.** ch10's regularization lemma (three defects); ch05 Prop :139 (false as stated); "total energy = 0" at emergence points (contradicted by the project's own Lean theorem); the ch08 definition of `J^ν` (incompatible with the field equation's divergence); the −0.095 anchor (no definition in the tree).
5. **Blocking obligation.** (P★): the flow → `(ch_2, Φ)` map with a physical scale.
6. **Assumption or circularity changes.** None introduced. One recorded: `C^{μν}` is defined through `T̂^{μν}` on a manifold the framework's own theorem collapses to a point.
7. **Kernel and rebuild status.** New module checked out of tree only. Not committed, not in-project built. No existing build touched.
8. **Decision required.** §6 items 1 and 2; and whether to land these three files on the live repository.
9. **Next decisive action.** Pablo states the map and the −0.095 source; then one session computes `Π₀` or records that it cannot be computed.
