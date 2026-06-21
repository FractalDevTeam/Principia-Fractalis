"""
GI directed spectral measurement — 144th-problem deeper run.

The exploratory coherence-sweep on QUATUM_TUNED_IBM.ipynb's
fractal_resonance_function found peak at α=1.0 (boundary effect — function
monotonically decreasing in α on [1, ∞)). That measurement doesn't actually
ENGAGE GI's specific structure; it just sweeps α with no GI input.

This script takes a different approach: encode GI's graph Laplacian spectrum
into the substrate-resonance machinery, then measure what α the resulting
spectral interference pattern actually peaks at.

Method:
  1. Generate 10 GI instance pairs (G1, G2) via random regular graphs
  2. Compute graph Laplacian L = D - A (where D = degree matrix, A = adjacency)
  3. Compute Laplacian eigenvalues λ_1, ..., λ_n (the graph's spectrum)
  4. Construct a substrate-resonance signal modulated by the spectrum:
     for each α and each eigenvalue λ_i, accumulate
     S(α, λ_i) = Σ_n 0.5^((α-1)·n) · cos(2^n · π · λ_i / λ_max)
     (this is the framework's fractal_resonance_function evaluated at the
     normalized eigenvalue λ_i / λ_max instead of an arbitrary x ∈ [0, 1])
  5. Coherence C(α) = mean of S(α, λ_i)^2 over all eigenvalues
  6. Find α_peak = argmax_α C(α) on a fine grid
  7. Compare α_peak to the framework's NP-class prediction φ+1/4

Framework's stated prediction (book Ch 34A): α_GI = φ+1/4 (NP-class).

Substrate's exposure: if the GI Laplacian spectrum, encoded through the
substrate's resonance machinery, peaks at α ≈ φ+1/4, the framework's
NP-classification has structural empirical support. If it peaks elsewhere,
the substrate's prediction is on display.
"""
import math
import numpy as np
import networkx as nx
from datetime import datetime

SQRT2 = math.sqrt(2)
PHI = (1 + math.sqrt(5)) / 2
ALPHA_P = SQRT2          # framework P-class predicted α
ALPHA_NP = PHI + 0.25    # framework NP-class predicted α
SACRED = [3, 6, 9, 12, 21, 33, 47]


def fractal_resonance_at(alpha: float, x: float, n_terms: int = 20) -> float:
    """The framework's fractal_resonance_function (matches notebook)."""
    result = 0.0
    for n in range(1, n_terms):
        scaling = 0.5 ** ((alpha - 1) * n)
        term = scaling * math.cos((2 ** n) * math.pi * x)
        for sp in SACRED:
            if abs(n - sp) < 0.5:
                term *= 1.2
        result += term
    return 0.5 + 0.5 * result / (n_terms - 1)


def gi_spectral_coherence(graph: nx.Graph, alpha: float, n_terms: int = 20) -> float:
    """Coherence of the substrate-resonance signal at α, modulated by the
    graph's Laplacian spectrum.

    The GI-specific input is the normalized Laplacian eigenvalue spectrum.
    Each eigenvalue λ_i (normalized to [0,1] by λ_max) drives one
    fractal_resonance_function evaluation; we take the mean-squared coherence
    across all eigenvalues.
    """
    L = nx.laplacian_matrix(graph).todense()
    eigs = np.linalg.eigvalsh(L)
    eigs = np.real(eigs)
    eigs = eigs[eigs > 1e-10]  # drop zero eigenvalue (always present in connected component)
    if len(eigs) == 0:
        return 0.0
    eigs_normalized = eigs / np.max(eigs)
    vals = [fractal_resonance_at(alpha, float(x), n_terms) for x in eigs_normalized]
    return float(np.mean([v * v for v in vals]))


def find_peak_alpha(graph: nx.Graph, alpha_grid: np.ndarray, n_terms: int = 20) -> tuple[float, float, np.ndarray]:
    """Find α that maximizes the GI-spectral-modulated coherence."""
    cohs = np.array([gi_spectral_coherence(graph, a, n_terms) for a in alpha_grid])
    idx = int(np.argmax(cohs))
    return float(alpha_grid[idx]), float(cohs[idx]), cohs


def generate_gi_instance(seed: int, n_vertices: int = 16, degree: int = 4) -> tuple[nx.Graph, nx.Graph]:
    """Generate (G1, G2) where G2 = relabel(G1). Larger graph for richer spectrum."""
    rng = np.random.default_rng(seed)
    G1 = nx.random_regular_graph(degree, n_vertices, seed=int(rng.integers(0, 1_000_000)))
    perm = list(range(n_vertices))
    rng.shuffle(perm)
    mapping = {i: perm[i] for i in range(n_vertices)}
    G2 = nx.relabel_nodes(G1, mapping)
    return G1, G2


def main() -> None:
    print("=" * 78)
    print("GI DIRECTED SPECTRAL MEASUREMENT — 144th-problem deeper run")
    print(f"Date: {datetime.utcnow().isoformat()}Z")
    print("=" * 78)
    print()
    print(f"Framework's stated NP-class prediction for GI (book Ch 34A):")
    print(f"  α_GI = φ + 1/4 = {ALPHA_NP:.10f}")
    print(f"Substrate's exposure: does the GI Laplacian spectrum, encoded through")
    print(f"the substrate-resonance machinery, peak at α ≈ φ+1/4?")
    print()
    print("Coarse alpha-sweep over [1.0, 2.5] at 10^-3 resolution:")
    print("-" * 78)

    coarse_grid = np.arange(1.0, 2.501, 0.001)
    peak_alphas_p1 = []
    peak_alphas_p2 = []
    peak_alphas_consistency = []

    for seed in range(10):
        G1, G2 = generate_gi_instance(seed)
        peak_a1, peak_c1, _ = find_peak_alpha(G1, coarse_grid)
        peak_a2, peak_c2, _ = find_peak_alpha(G2, coarse_grid)
        peak_alphas_p1.append(peak_a1)
        peak_alphas_p2.append(peak_a2)
        # isomorphism check: G2 should give SAME peak as G1 if substrate is
        # isomorphism-invariant
        peak_alphas_consistency.append(abs(peak_a1 - peak_a2))
        d_np = abs(peak_a1 - ALPHA_NP)
        d_p = abs(peak_a1 - ALPHA_P)
        closer = 'NP' if d_np < d_p else 'P'
        print(f"  Seed {seed:2d}: G1 peak_α={peak_a1:.4f}  G2 peak_α={peak_a2:.4f}  |Δ|={abs(peak_a1-peak_a2):.4f}  closer-to: {closer}-class (Δ_NP={d_np:.4f}, Δ_P={d_p:.4f})")

    print()
    mean_p1 = float(np.mean(peak_alphas_p1))
    mean_p2 = float(np.mean(peak_alphas_p2))
    mean_consistency = float(np.mean(peak_alphas_consistency))
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print(f"10-instance G1 mean peak_α:        {mean_p1:.6f}")
    print(f"10-instance G2 mean peak_α:        {mean_p2:.6f}")
    print(f"G1-vs-G2 mean |Δ| (isomorphism):   {mean_consistency:.6f}")
    print(f"  (low |Δ| = substrate-resonance machinery is isomorphism-invariant)")
    print()
    print(f"Framework's NP-class prediction:    α_NP = {ALPHA_NP:.6f}")
    print(f"Framework's P-class prediction:     α_P  = {ALPHA_P:.6f}")
    print(f"10-instance mean Δ from α_NP=φ+1/4:  {abs(mean_p1 - ALPHA_NP):.6f}")
    print(f"10-instance mean Δ from α_P=√2:      {abs(mean_p1 - ALPHA_P):.6f}")
    print()
    pre_reg_tolerance = 1e-4
    if abs(mean_p1 - ALPHA_NP) <= pre_reg_tolerance:
        verdict = f"PASS (NP-class predicted): mean peak_α within 10⁻⁴ of φ+1/4"
    elif abs(mean_p1 - ALPHA_P) <= pre_reg_tolerance:
        verdict = f"PASS (P-class predicted via fallback): mean peak_α within 10⁻⁴ of √2"
    else:
        d_np = abs(mean_p1 - ALPHA_NP)
        d_p = abs(mean_p1 - ALPHA_P)
        closer = 'NP' if d_np < d_p else 'P'
        verdict = f"AT THIS PRECISION/METHOD: peak_α does not land within 10⁻⁴ of either canonical value (closer: {closer}-class, Δ={min(d_np,d_p):.4f})"
    print(f"VERDICT: {verdict}")
    print()
    print("Honest interpretation:")
    print("  - This is the framework's substrate-resonance machinery applied DIRECTLY to")
    print("    the GI graph Laplacian spectrum — not a blind α-sweep, but an actual")
    print("    encoding of GI's structure into the substrate's coherence function.")
    print("  - If the peak lands at φ+1/4 (NP-class), the book's classification is")
    print("    structurally corroborated.")
    print("  - If it lands at √2 (P-class), the framework would need to update its")
    print("    classification (or the CSV's existing GI=1.41 reflects the right class).")
    print("  - If it lands elsewhere, the framework's binary-classification rule may")
    print("    not be the natural prediction for GI under this measurement approach.")
    print()
    print(f"Run complete at {datetime.utcnow().isoformat()}Z")


if __name__ == '__main__':
    main()
