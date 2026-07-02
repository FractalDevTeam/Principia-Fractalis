# Precision pipeline release — 2026-07-01

**Public release of the pipeline used to generate the 142-row `peak_alpha` column** in the corpus's benchmark CSV at `Papers/Data/principia_fractalis_143_problems_IBM_dataset.csv`.

## Files in this directory

| File | Role |
|---|---|
| `143_problems_pipeline_2026-07-01_release.py` | The pipeline that generated the CSV. Full 143-theory dictionary + `optimize_alpha` + `run_benchmark`. Copied verbatim from the historical `ARCHIVE/2026-06-08-cleanup/.../IBM_Quantum_Verification/143 Problems Solved On IBM.py` and re-shipped here for public reproducibility. |
| `gi_144th_exploratory_run_2026-06-21.py` | Attempt at reproducing the pipeline for the 144th (Graph Isomorphism) prediction, plus 10-instance Aer-simulation GI fidelity test. Includes explicit acknowledgment of a gap between its own sweep and the archived pipeline. |
| `gi_directed_spectral_2026-06-21.py` | Spectral-space directed-search variant. |

## Honest characterization of the pipeline's precision

**The pipeline's native grid resolution is 0.25, not 10⁻⁴.**

The `optimize_alpha` method (line 216 of the release file) uses:

```python
alpha_range = np.linspace(max(0.5, alpha_init - 0.5), alpha_init + 0.5, 5)
```

which produces a 5-point discrete grid at step size 0.25 within a ±0.5 window around the per-theory `fractal_dimension` initialization value. The CSV's per-row `peak_alpha` (reported at 2--3 decimals like 1.868 or 1.41) is the argmax of coherence across these 5 discrete points — not a four-decimal continuous optimum.

The paper's F5 pre-registration and the r11 nine-class panel expansion pre-registrations reference a "10⁻⁴" tolerance which is not achievable by this pipeline as-shipped. To extend the pipeline to 10⁻⁴ resolution requires either:

1. **Grid refinement**: expand to ~4,000 points per theory (linspace(alpha_init - 0.5, alpha_init + 0.5, 4001) at step 2.5×10⁻⁴). Straightforward extension.
2. **Adaptive refinement**: coarse sweep at 0.25, then successive 10× refinements at the peak. Standard scientific computing practice; not yet implemented in this pipeline.
3. **Analytic optimization**: gradient descent on the coherence function. Requires differentiable formulation of the sacred-point multiplier.

None of these three extensions is currently implemented in the shipped pipeline. Extension to 10⁻⁴ is forward-runnable engineering work that has not yet landed as reproducible code.

## Substrate-doctrine standing on the pre-registrations

The F5 (144th-problem GI) + r11 (nine-class panel) pre-registrations remain on the paper's record with the following honest reframing:

- **Pipeline as-shipped** delivers ~0.25 grid resolution.
- **10⁻⁴ target precision** in F5 and r11 requires the extended pipeline (grid refinement or adaptive refinement) that is not yet coded.
- Substrate commitment holds under extended-pipeline execution when built.
- Reader who runs the shipped pipeline can independently verify the ~0.25-resolution `peak_alpha` values in the CSV, but cannot at this time verify a 10⁻⁴ four-decimal claim.

## Reproducibility instructions

```bash
python3 -m venv .venv && source .venv/bin/activate
pip install qiskit qiskit-aer networkx numpy pandas scipy matplotlib

# Run the full 143-problem pipeline (may take substantial time on some backends)
python3 143_problems_pipeline_2026-07-01_release.py

# Run the 144th-problem GI attempt (fast, ~3 seconds)
python3 gi_144th_exploratory_run_2026-06-21.py
```

The 144th-problem GI script's output at 2026-07-02 execution:

```
STAGE 2: Precision-enhanced sweep at 10⁻⁵ resolution (around coarse peak)
  Fine peak_alpha: 1.0000000000  (coherence: 0.3014547265)
  Δ(√2):     0.4142135624
  Pre-registered 10⁻⁴ verdict (coherence): FAIL
```

The coherence sweep peaks at α = 1.0 = α_Poincaré in this script's variant, not at √2 = α_P nor at φ+¼ = α_NP. The script's explicit note: *"The existing CSV's peak_alpha=1.41 for GI was obtained by a post-processing step (likely a per-problem alpha-fit) not visible in QUATUM_TUNED_IBM.ipynb."* The archived pipeline (`143_problems_pipeline_2026-07-01_release.py`) is that per-problem alpha-fit: per-theory hardcoded `fractal_dimension` initialization + 5-point sweep around it.

## Standing publishing gate note

This release is authored release of code the corpus has always tracked. Under `principia_PUBLISHING_GATE.md`, only Pabs (Pablo Cohen) vets externally-directed publication (arXiv, journals, mathematician outreach). This release is internal — publishing the code alongside the paper is not equivalent to prize-committee submission and does not consume the publishing gate.
