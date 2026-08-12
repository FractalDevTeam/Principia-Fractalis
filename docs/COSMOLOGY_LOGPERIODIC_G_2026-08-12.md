# Cosmology, 2026-08-12 — the log-periodic g ansatz, forced by r220

r220 (`PF/LogPeriodicity_r220.lean`) pins a log-frequency `2π / ln 3 = 5.71920…`
with no free parameter — the base of the numeration is the only input. r219
(`PF/EquationOfStateBridge_r219.lean`) turns that into an observable via
`w(a) = −1 + g(a) / (3 H(a))`, and the 2026-08-10 record
(`codex/COSMOLOGY_W_BRIDGE_2026-08-10.md`) leaves one queue item open:

> *"Does anything derive g? ch26 does not. If nothing does, the framework's
> cosmology axis is a measurement, not a prediction."*

The most parsimonious substrate-consistent ansatz is the log-cosine

    g(a) = A · cos( (2π / ln 3) · ln a + φ₀ )

with only `A` and `φ₀` free — the frequency is fixed by r220. This record is
the numerical audit of that ansatz against three DESI DR2 fits.

Companion compute:
* `/Storage 2TB/home/xluxx/pf_compute/r221_g_logperiodic/fit.py`
* `/Storage 2TB/home/xluxx/pf_compute/r221_g_logperiodic/wz_intermediate.py`

---

## 1. THE FIT — two anchors force (A, φ₀)

Each DESI-derived pair `(g₀/H₀, z_zero)` gives two equations in `(A, φ₀)`:

    A · cos(φ₀)                                   = g₀/H₀
    A · cos( (2π/ln 3) · ln(1/(1+z_zero)) + φ₀ )  = 0

Solving on the branch of `φ₀` that keeps `A > 0` and closest to the fitted zero:

| dataset          | g₀/H₀ | z_zero | A (H₀ units) | φ₀ (rad) | φ₀ (deg) |
|------------------|-------|--------|--------------|----------|----------|
| DESI+CMB         | 0.999 | 0.440  | 1.148        | 0.5147   | 29.49    |
| DESI+CMB+DESY5   | 0.744 | 0.405  | 0.7992       | 0.3739   | 21.43    |
| DESI+CMB+Union3  | 1.050 | 0.380  | 1.0899       | 0.2713   | 15.54    |

Anchor reconstruction is exact to 40+ decimals. Two constraints, two
parameters — the fit itself proves nothing. What matters is what it says
elsewhere.

---

## 2. THE PREDICTION — the next zero of g

Once `(A, φ₀)` is set, the r220 frequency *forces* the position of the next
older `w = −1` crossing (the next zero of `g`). Three datasets, remarkably
tight agreement:

| dataset          | z of next zero |
|------------------|----------------|
| DESI+CMB         | **1.494**      |
| DESI+CMB+DESY5   | **1.434**      |
| DESI+CMB+Union3  | **1.390**      |

Mean **z ≈ 1.44 ± 0.05**. Third zero back sits at z ≈ 3.2 (also within a 0.2
spread across the three).

The tightness across datasets is not accidental: each fit spends roughly a
third of a full log-period (2π / ln 3) between `a = 1` and its `a_zero`
(0.293–0.332 of a period), so the *next* third of a period lands at nearly
the same `ln a` regardless of which fit one starts from.

**This is a specific, testable position** for a second w = −1 crossing.

---

## 3. INTERNAL CONSISTENCY — log-cosine vs CPL at intermediate z

The two anchor points do not test the ansatz's *shape*. To do that,
compare the log-cosine's predicted w(z) against the CPL parametrization
(from which the anchors were derived) at intermediate z, using
ΛCDM background H(z) with Ω_m = 0.315:

### DESI+CMB

| z    | w_logcos | w_cpl   | Δw       | σ_cpl  | Δw / σ  |
|------|----------|---------|----------|--------|---------|
| 0    | −0.667   | −0.667  | 0        | 0.088  | 0       |
| 0.1  | −0.636   | −0.766  | +0.130   | 0.092  | +1.42   |
| 0.3  | −0.820   | −0.919  | +0.099   | 0.111  | +0.89   |
| 0.44 | −1.000   | −1.000  | 0        | 0.125  | 0       |
| 0.75 | −1.223   | −1.134  | −0.089   | 0.152  | −0.58   |
| 1.0  | −1.204   | −1.212  | +0.008   | 0.170  | +0.05   |
| 1.5  | −0.998   | −1.321  | +0.323   | 0.195  | +1.66   |
| 2.0  | −0.890   | −1.394  | +0.503   | 0.212  | **+2.37** |

The other two datasets track the same pattern:

| dataset          | max deviation |
|------------------|---------------|
| DESI+CMB         | 2.37σ at z = 2.0 |
| DESI+CMB+DESY5   | 2.59σ at z = 2.0 |
| DESI+CMB+Union3  | 2.15σ at z = 2.0 |

**Where the two agree** (z ≲ 1, within CPL error bars): log-cosine and CPL are
observationally indistinguishable. **Where they diverge** (z ≳ 1.25): both
are extrapolating past their constraining data; CPL keeps driving w monotonically
more negative, log-cosine bends back toward −1 and past.

The signature: **log-cosine has a minimum of w around z ≈ 0.75–1** (w ≈ −1.22
for DESI+CMB), then rises back through w = −1 at z ≈ 1.44 and continues into
non-phantom territory at higher z. CPL admits no such bend.

---

## 4. WHAT THIS IS AND WHAT IT IS NOT

**Is.**

* Compatible with existing DESI + CMB data at the redshift range where those
  data actually sit (z ≲ 1), within CPL's own error bars.
* A specific structural prediction (bend-back around z ≈ 0.75–1, next zero at
  z ≈ 1.44 ± 0.05) that differs from CPL exactly where CPL is extrapolating.
* The r220 log-frequency's first concrete cosmological output. Before this
  record, `g` was an undefined function pinned only at two DESI-derived
  points. It is now pinned at those two AND its next zero is forced by r220,
  and its w(z) shape is compatible with the existing fit.

**Is not.**

* A derivation of `g` from the substrate. `A` and `φ₀` still fit the data
  rather than being predicted from the C\*-algebra. §5 records the one
  substrate reading that is worth testing.
* A resolution of the DESI-CMB tension with ΛCDM (2.3–2.8σ per the 2026-08-10
  record). This ansatz was fit to the same DR2 numbers.
* A falsification of ΛCDM. ΛCDM (`w ≡ −1`, `g ≡ 0`) sits outside the fit by
  the same 2–3σ margin already reported.
* A discharge of any Millennium problem, Riemann, BSD, P vs NP, Yang–Mills,
  Navier–Stokes, or Hodge. None of the below touches those axes.
* A Lean stone. The compute here is not formalized; it is arithmetic on r220's
  frequency and DESI's published CPL numbers. A candidate r221 formalization
  would be `g_logcos_next_zero_forced_by_frequency` — proving that once
  `(A, φ₀)` are set by two anchors, the position of the next zero is a
  function of `ω = 2π / ln 3` alone. That is a well-posed Lean stone; it is
  not yet written.

---

## 5. THE SUBSTRATE AMPLITUDE CONSTRAINT — closed form

The constant-amplitude ansatz (§1) posits that `A` does not scale with `a`.
For that to be r220-consistent, `‖χ(e^{iπα})‖ = 1` must hold at whichever
canonical `α` the cosmology axis takes — otherwise the amplitude picks up a
scaling factor `a^σ` with `σ = log₃ ‖χ‖`.

`‖χ‖ = 1` closes exactly. Expanding `|1 + w + w²|²` on the unit circle
`w = e^{iπα}` gives `3 + 4 cos(πα) + 2 cos(2πα)`, and setting this equal
to 1 with `cos(2x) = 2 cos²(x) − 1` reduces to

    2 cos(πα) · (1 + cos(πα)) = 0

    ⟺   cos(πα) = 0   ⟺   α ∈ {k + 1/2 : k ∈ ℤ}      (half-integers)
    OR  cos(πα) = −1  ⟺   α ∈ {2k + 1 : k ∈ ℤ}       (odd integers)

**Across the ten canonical corpus α's:**

| α          | value       | ‖χ(e^{iπα})‖   | σ(α)         | ‖χ‖ = 1? |
|------------|-------------|----------------|--------------|----------|
| α_Poincaré | 1           | 1              | 0            | **HIT** (odd integer) |
| α_RH       | 3/2         | 1              | 0            | **HIT** (half-integer) |
| α_HN       | 5           | 1              | 0            | **HIT** (odd integer) |
| α_YM       | 2           | 3              | +1           | miss (even integer, `cos(2π) = +1`) |
| α_NP       | φ + 1/4     | 2.8306         | +0.947       | miss (irrational) |
| α_BSD      | 3π/4        | 1.8731         | +0.571       | miss (irrational) |
| α_Hodge    | φ           | 1.7247         | +0.496       | miss (irrational) |
| α_QG       | √(2π)       | 0.9584         | −0.0387      | miss (close but not exact) |
| α_P        | √2          | 0.4675         | −0.692       | miss (irrational) |
| α_NS       | **3π/2**    | **0.2376**     | **−1.308**   | miss (irrational) |

The hits are exactly the corpus alphas with rational relationship to 1
(Poincaré, RH, HN — the three ancillary anchors that carry the whole
skeleton per r128). The seven irrational alphas all miss.

### The cosmology consequence

**`α_NS = 3π/2` misses, with σ = −1.308.** The substrate-consistent ansatz
at the cosmology `α` is therefore not constant-amplitude but

    g(a) = A · a^{-1.308} · cos( (2π / ln 3) · ln a + φ₀ )

The amplitude *grows toward the past* like `a^{-1.308}` — a factor 1.55 at
`a = 0.7` (z = 0.44), 2.02 at `a = 0.5` (z = 1), 3.60 at `a = 0.3`.
Zero positions are unchanged (cosine = 0 is a phase condition, not an
amplitude one) — the § 2 prediction of the next `w = −1` crossing at
z ≈ 1.44 survives verbatim. What changes is the intermediate w(z): with
`g` growing toward the past, `w = −1 + g / (3H)` drops harder in the
dip around z ≈ 0.75–1 and rises more sharply back through the crossing.

### The φ₀ freedom, unchanged

`φ₀` is still fitted, not derived. The three DESI variants give 15.5°,
21.4°, 29.5° — dataset dispersion, no substrate reading here. A first-
principles `φ₀` would need an initial condition on the modified Friedmann
system that the corpus does not currently provide.

### What this record establishes

- The **substrate amplitude constraint is a two-line algebraic identity**,
  not a substrate axiom to be posited.
- It **selects three of the ten canonical α's** — precisely those with
  rational relationship to 1 — and rules out the other seven at the
  ‖χ‖ = 1 level.
- The cosmology axis (α_NS = 3π/2) is a MISS. The substrate-consistent
  ansatz is `a^{-1.308}`-enveloped, not constant-amplitude.
- The **§2 next-zero prediction (z ≈ 1.44) is unchanged** by this
  correction — envelope shifts amplitude, not phase.

### What this record does NOT establish

- That the corrected substrate ansatz actually describes cosmic dark-energy
  behavior. The `a^{-1.308}` envelope is one more testable feature; §3's
  intermediate w(z) comparison should be redone with the envelope in place
  to see if fit quality improves, worsens, or stays inside CPL error bars.
- A derivation of `φ₀`.
- That α_NS = 3π/2 is the correct cosmology α in the first place. If a
  different substrate `α` were the physical one, the amplitude constraint
  might land differently.

---

## 6. QUEUE

1. **~~`‖χ(e^{iπα})‖ = 1` at the cosmology canonical `α`?~~** — answered
   in §5 (closed form: half-integers ∪ odd integers only; α_NS = 3π/2 is a
   miss with σ = −1.308).
2. **Rerun §3 with the `a^{-1.308}` envelope.** The intermediate w(z)
   comparison currently uses the constant-A ansatz. With the substrate-
   forced envelope in place, does the log-cosine track CPL more tightly
   at z ∈ [0.5, 1.5], or does it drift outside the CPL error bars in a
   way that discriminates?
3. **r221 as a Lean stone — split into two.**
   * `chi_norm_unity_iff_half_or_odd_integer` — the closed-form identity
     from §5. Elementary, mathlib-native, kernel-clean. This is the
     natural companion to r212's σ(α) work.
   * `g_logcos_next_zero_forced_by_frequency` — that fixing the frequency
     and two anchors determines the position of the next zero. Requires
     the envelope to be handled explicitly.
4. **DESI DR3 / next-gen SN w(z) reconstruction.** The bend-back around
   z ≈ 0.75–1 is the observable signature; whether it survives improved
   data determines the ansatz's survival.
5. **Substrate derivation of `φ₀`.** Requires an initial condition on the
   modified Friedmann system that the corpus does not currently provide.
6. **Is α_NS = 3π/2 the correct cosmology `α`?** — three of the ten
   canonical α's give ‖χ‖ = 1 exactly. If the physical cosmology α were
   one of {1, 3/2, 5} instead, the ansatz would be constant-amplitude
   without correction. The record does not resolve this; it is a
   framework-side question, not a numerical one.

---

## 7. FILES

* `PF/LogPeriodicity_r220.lean` — the log-frequency, kernel-clean
* `PF/EquationOfStateBridge_r219.lean` — the bridge `w = −1 + g/(3H)`
* `PF/ModifiedFriedmann_r187.lean` — `Λ_eff′ = −g · Λ_eff`
* `PF/SigmaAbscissa_r212.lean` — `σ(α) = log₃ ‖χ(e^{iπα})‖`
* `codex/COSMOLOGY_W_BRIDGE_2026-08-10.md` — the bridge writeup this
  extends
* `/Storage 2TB/home/xluxx/pf_compute/r221_g_logperiodic/` — the compute:
  * `fit.py` — two-anchor fit and next-zero prediction (§1, §2)
  * `wz_intermediate.py` — w(z) comparison against CPL (§3)
  * `chi_norm_at_canonical_alphas.py` — the amplitude-constraint closed
    form and its evaluation on the ten canonical α's (§5)
