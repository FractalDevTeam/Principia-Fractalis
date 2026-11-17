# Fractal-audio paper p.20 / p.21 reproduction audit

**Date:** 2026-11-16
**Source paper:** `.academia-profile/pdfs/academia-128468852.pdf` (31 pages)
**Auditor:** external co-scientist; audit received as status report into this session
**Verdict in one line:** p.21 scalar formula is reconstructible exactly; p.20 audio pipeline is not reconstructible from the PDF alone; Table 4's benchmark advantages are not reproduced under the one implementation the auditor could extract.

This document records the audit's findings for the project's verification ledger. The corresponding entry in the book's rigor ledger is in `frontmatter/revision2_changes.tex`, section "Negative results, which are also results."

## What was reproduced exactly (p.21)

The scalar function printed in §5.2.3 on p.21 was transcribed into the auditor's `method.py` verbatim (only whitespace and descriptive docstrings shortened). For positive frequency $f$:

$$
S_3(n) = \text{base-3 digit sum of } n, \qquad L_3(n) = \lfloor \log_3 n \rfloor + 1
$$

$$
M(f) = \min(50,\, \lfloor 20000/f \rfloor)
$$

$$
F(f, \alpha) = \sum_{n=1}^{M(f)} \cos\!\left(\frac{\pi \alpha\, S_3(n)}{L_3(n)}\right) \cdot n^{-f/440}
$$

Exact-float checks (for $\alpha = 1.618$):

| $f$ (Hz) | $F(f, 1.618)$ |
|---------:|--------------:|
| 20       | $+0.759218$ |
| 100      | $+0.081235$ |
| 200      | $-0.200231$ |
| 440      | $-0.214395$ |
| 1000     | $+0.162337$ |
| 4000     | $+0.360886$ |
| 20000    | $+0.362275$ |

Details that survived the transcription precisely:

- **Normalized digit phase** — $S_3(n)/L_3(n)$, not $S_3(n)$ alone. For $n = 3$ (base-3 "10"): $S_3 = 1$, $L_3 = 2$; phase $\pi \alpha / 2$.
- **Frequency-dependent exponent** — $n^{-f/440}$, not $n^{-\alpha}$ or $n^{-f}$.
- **Finite truncation** — 50 terms for $0 < f \leq 400$ Hz; fewer above, creating response steps at $20000/m$ Hz.
- **DC** — $f = 0$ causes division by zero in the printed code; no DC value in the paper.
- **High-frequency behavior** — for $10000 < f \leq 20000$: $M = 1$, $F = \cos(\pi \alpha)$. For $f > 20000$: empty loop, $F = 0$.
- **Signed output** — $F$ may be positive, negative, or zero; the paper does not say to take magnitude, clip, or convert to power gain.

**Difference from the complex $R_f$ series of Eq. (3), §2.1.3, p.6**: Eq. (3) is complex-valued, infinite-sum, has no digit-count divisor in its phase, and uses an independent argument $x$ as exponent. The p.21 function $F$ is neither Eq. (3) itself nor its truncated real part under any natural substitution, because $F$ divides $S_3$ by $L_3$. These are two distinct objects in the paper.

## What was not reproducible from the PDF (p.20)

The paper's §5.2 architecture names four audio-pipeline components:

1. Frequency Domain Mapping
2. Sacred Geometry Filter Banks
3. Inverse Fractal Transform
4. Harmonic Enhancement

None have operational formulas elsewhere in the PDF. The p.21 scalar function cannot by itself produce a WAV: it returns one real number per frequency, but the frequency-domain mapping (bin-to-Hz convention, DC handling), filter-bank coefficients, transform direction, and harmonic-generation rules are not specified.

## The auditor's chosen implementation (one explicit test, not a recovery)

To test *anything*, the auditor had to supply the missing specifications. Choices made and recorded:

| Choice | Implementation | Consequence |
|--------|---------------|-------------|
| Sampling / record | mono, 48 kHz, $N = 131072$ samples ($\approx 2.73$ s), float64 | one offline block, bin spacing 0.366 Hz |
| Frequency map | $f_k = k \cdot f_s / N$, evaluate in Hz | not FFT-bin index or normalized frequency |
| DC extension | $H[0] = 0$ for every $\alpha$ | arbitrary DC removal; scalar undefined there |
| Gain convention | $H[k] = F(f_k, \alpha) / F(440, \alpha)$ for $k > 0$ | signed unity at 440 Hz; no absolute value, auto-level, or output-fitting |
| Spectral processing | $X = \text{rfft}(x)$; $Y[k] = H[k] \cdot X[k]$; $y = \text{irfft}(Y, N)$ | retains complex phase except $\pi$ reversals where $H < 0$ |
| Boundaries / inverse | full-record rFFT, periodic boundaries, no window | circular; can pre-ring and wrap at record edges |
| Filter bank / enhancement | none added | no basis to infer unspecified filter banks or nonlinear harmonic generation |
| Input/output levels | no peak normalization or limiting in metrics | signal coloration and gain count as error vs clean ground truth |

The 440-Hz normalization was fixed before any test. For $\alpha = 1.618$, the resulting response has $H(20) \approx -3.541$, $H(440) = 1$, $H(1000) \approx -0.757$, $H(4000) \approx -1.683$. A 1-kHz or 4-kHz tone is therefore phase-inverted relative to the clean reference, and the clean-reference SNR carries that as error.

## The comparator — a matched FIR, response-equivalence control

Baseline: a 16385-tap symmetric frequency-sampling FIR (`scipy.signal.firwin2`), Kaiser $\beta = 8.6$, targeting the same signed normalized $H(f)$ on 32769 sample frequencies. Linear phase removed by centering taps around circular lag zero. Applied through the same cached rFFT engine as the cosine gain, so execution-engine differences don't attribute to formula differences.

For $\alpha = 1.618$, over 20–19500 Hz: RMS signed-gain error $0.00148$; excluding target magnitudes below $-30$ dB, 95th-percentile magnitude mismatch $0.000165$ dB; FIR gain at 440 Hz $0.99473$ vs target $1$. The match is approximate at narrow notches, below 20 Hz, and near the 20-kHz discontinuity.

## Results — what the measured numbers show

**White noise, input SNR 10 dB, $\alpha = 1.618$** (three seeds, means; identity returns 10 dB throughout):

| Wanted signal | Cosine ref SNR (dB) | FIR ref SNR (dB) | Cosine component SNR (dB) | FIR component SNR (dB) |
|---------------|---------------------:|-----------------:|---------------------------:|-----------------------:|
| 439.82 Hz sine | $+6.50 \pm 0.01$ | $+6.50$ | $+6.50$ | $+6.46$ |
| 1000.12 Hz sine | $-5.18 \pm 0.00$ | $-5.19$ | $+4.03$ | $+4.06$ |
| 4000.12 Hz sine | $-8.71 \pm 0.00$ | $-8.71$ | $+11.02$ | $+11.02$ |
| Harmonic chord | $+0.85 \pm 0.01$ | $+0.85$ | $+6.21$ | $+6.20$ |
| Log sweep | $-7.59 \pm 0.01$ | $-7.59$ | $+10.47$ | $+10.47$ |
| Transient | $-5.25 \pm 0.01$ | $-5.25$ | $+4.94$ | $+4.94$ |
| White probe | $-7.83 \pm 0.01$ | $-7.83$ | $+9.98$ | $+9.98$ |
| Pink probe | $-12.48 \pm 0.00$ | $-11.93$ | $+16.96$ | $+16.24$ |

**Reading.** The clean-reference SNR goes *down* on most signals (negative = output deviates from clean more than noise alone would have deviated) because the fractal response colors the input substantially — phase inversions at 1 and 4 kHz, redistributed gain, etc. The component SNR (processed wanted signal vs processed noise) looks better, but that excludes coloration and so cannot stand alone as a fidelity claim.

**Clean-tone THD+N** (clean input, no additive noise, $\alpha = 1.618$): $-249$ to $-245$ dB. That is the float64 numerical floor — the auditor's linear implementation does not generate any new harmonics. The paper's reported $0.11\%$ figure requires the unspecified nonlinear "Harmonic Enhancement" pipeline, which the auditor could not reconstruct.

## Table 4 benchmarks — transcribed, not reproduced

The paper's Table 4 (p.20) reports:

| Metric | Conventional | Fractal | Improvement | Paper's $p$ |
|--------|-------------:|--------:|------------:|------------:|
| Ops/sample | $456.3 \pm 12.7$ | $83.2 \pm 5.3$ | $81.8\%$ | $< 10^{-4}$ |
| SNR (dB) | $67.3 \pm 2.1$ | $92.8 \pm 1.4$ | $37.9\%$ | $< 10^{-4}$ |
| THD (%) | $0.83 \pm 0.12$ | $0.11 \pm 0.04$ | $86.7\%$ | $< 10^{-4}$ |
| Latency (ms) | $12.4 \pm 1.8$ | $2.7 \pm 0.5$ | $78.2\%$ | $< 10^{-4}$ |

None of these are verifiable from the PDF alone. The test chain, comparator algorithms, operation-count model, sample rate, block size, and trial-level data are not specified sufficiently in the paper. The auditor's independent measurements on the one reconstructable implementation:

- **Ops/sample proxy:** the cached-gain FFT implementation uses $2(5N\log_2 N) + 2K = 22{,}413{,}314$ arithmetic operations per $N = 131072$ block, $\approx 171$ ops/sample under a radix-2 full-complex proxy (conservative). Real FFTs exploit symmetry; the actual pocketfft count is not instrumented. Either way this is above Table 4's $83.2$.
- **Runtime:** median $2.64$ ms per 131072-sample block ($\alpha = 1.618$, cosine); vs identity $2.61$ ms, FIR $2.70$ ms. 95th-percentile overlap. This is offline compute on one AMD EPYC host (shared sandbox, uncontrolled affinity) — not a real-time streaming latency. The $2.7$ ms Table 4 "latency" was transcribed; the $2.64$ ms measured offline compute time *is not the same quantity* and cannot be presented as reproducing it.
- **SNR:** measured *clean-reference* SNRs go down; there is no measured $67 \to 92$ dB improvement in these tests.
- **THD:** clean-tone residual at numerical floor; no path to $0.11\%$ without the nonlinear enhancement stage.

## What this does not touch

The audit is scoped to one engineering paper and one implementation choice. It does not touch:

- The Lean 4 corpus or any theorem therein.
- The ToE meta-capstone at `PF/PrincipiaFractalisToEMetaCapstone_2026_11_16.lean`.
- The $\alpha$-skeleton identities (9 kernel-verified algebraic facts).
- The Clay-axis substrate discharges (RH, P vs NP, YM, NS, BSD, Hodge, Poincaré, Fermat).
- The substrate algebra $\mathcal{T}_\infty$ and its faithful tracial state.
- The clinical consciousness findings of Ch.30–32 (a separate EEG-based observable).
- The cosmology predictions of Ch.26–29 (a separate empirical track).

These are formal objects whose proofs are independent of the engineering pipeline on p.20.

## What this does touch

The specific paper `academia-128468852.pdf`'s claims on p.20 and Table 4 are not independently reproducible from the PDF. That paper's p.21 formula stands; its system claims do not, until the operational specifications for the four named pipeline components are published alongside.

## Deliverables (auditor's side, external to this machine)

Per the audit's final listing, the reproduction bundle contains:

- `method.py` (full script with literal scalar transcription and assertions)
- `results.csv` (1296 individual noisy cases)
- `results_summary.csv` (432 condition/method group means)
- `clean_spectral_metrics.csv` (72 clean cases)
- `tone_metrics.csv` (513 clean/noisy tone cases)
- `runtime.csv` (9 timing summaries)
- `setup_runtime.csv` (4 coefficient-construction timings)
- `baseline_match.csv` (4 FIR response fits)
- `scalar_checks.csv` (52 exact scalar evaluations)
- `frequency_responses.csv` (all 65537 nonneg FFT frequencies × 9 gain arrays)
- `metadata.json` (parameters, seeds, exact tones, SHA-256, software/hardware)
- 4 PNG figures (response, SNR, spectral/transient, tone/runtime)
- 3 WAVs (harmonic chord, sweep, transient — 4-segment comparison each)
- `reproduction_bundle.zip` + `SHA256SUMS.txt`

These are not committed to this repository; they live with the auditor. This document records the findings and their status in the project's own verification ledger.

## Action taken

- Book: entry added to `frontmatter/revision2_changes.tex` section "Negative results, which are also results." Positions this as a recorded negative finding, not buried.
- Codex: this document (`codex/FRACTAL_AUDIO_P20_P21_REPRODUCTION_2026-11-16.md`) carries the audit's technical specifics.
- No change to the Lean corpus or to any Clay-axis theorem.
- No change to the ToE meta-capstone.

The paper's p.21 formula is reproducible; the paper's p.20 system is not; the project's formal core is unaffected.
