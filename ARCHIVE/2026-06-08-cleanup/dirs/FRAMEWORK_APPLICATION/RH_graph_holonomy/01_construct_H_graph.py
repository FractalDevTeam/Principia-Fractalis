"""
01_construct_H_graph.py

Wave 8 / Option (b): RH via higher-connectivity 2D graph with
non-trivial Z_3 plaquette holonomy.

Construction:
  - N x N square lattice (vertices indexed by (m,n) in {0,...,N-1}^2)
  - Hermitian operator H_alpha^graph on C^(N*N)
  - Diagonal: Berry-Keating-style Weyl scaling D(m,n) = 2 pi m n / log(m n + 2)
  - Edges (nearest-neighbor + nearest-diagonal):
       horizontal:  c_h * phi_h(m,n)
       vertical:    c_v * phi_v(m,n)
       diagonal:    c_d * phi_d(m,n)
  - Phases use framework Z_3:
       phi_e = exp(i * pi * alpha * D_3(encode(edge)))
  - Mechanism 3 modulation: scale ch_2 multiplies off-diagonals
       (Hermitian limit at ch_2 = 0.95)

Plaquette holonomy for unit square (m,n)->(m+1,n)->(m+1,n+1)->(m,n+1)->(m,n):
  W = phi_h(m,n) * phi_v(m+1,n) * conj(phi_h(m,n+1)) * conj(phi_v(m,n))
This is the GAUGE-INVARIANT Wilson loop.

Output: H_graph_built.pkl with dense Hermitian matrix and metadata.
"""

import numpy as np
import scipy.sparse as sp
import pickle
import os

OUT = os.path.dirname(os.path.abspath(__file__))


# ------------------------------------------------------------------
# Framework helpers
# ------------------------------------------------------------------
def D3(n: int) -> int:
    """Base-3 digital sum."""
    s = 0
    n = abs(int(n))
    while n > 0:
        s += n % 3
        n //= 3
    return s


def encode_h(m: int, n: int, N: int) -> int:
    """Unique edge ID for horizontal edge starting at (m,n)."""
    return 1 + m * N + n


def encode_v(m: int, n: int, N: int) -> int:
    """Unique edge ID for vertical edge starting at (m,n)."""
    return 1 + N * N + m * N + n


def encode_d(m: int, n: int, N: int) -> int:
    """Unique edge ID for diagonal edge starting at (m,n)."""
    return 1 + 2 * N * N + m * N + n


def vertex_index(m: int, n: int, N: int) -> int:
    return m * N + n


def berry_keating_weyl(m: int, n: int) -> float:
    """Diagonal scaling D(m,n) = 2 pi (m+1)(n+1) / log((m+1)(n+1) + 2)."""
    # Use (m+1)(n+1) to avoid zeros at boundary
    mn = (m + 1) * (n + 1)
    return 2.0 * np.pi * mn / np.log(mn + 2.0)


# ------------------------------------------------------------------
# Phase choices
# ------------------------------------------------------------------
def phase_framework(edge_id: int, alpha: float) -> complex:
    """Framework Z_3 phase: exp(i pi alpha D_3(edge_id))."""
    return np.exp(1j * np.pi * alpha * D3(edge_id))


def phase_random(edge_id: int, alpha: float, rng) -> complex:
    """Random phase from U(1)."""
    theta = rng.uniform(0, 2 * np.pi)
    return np.exp(1j * theta)


def phase_trivial(edge_id: int, alpha: float) -> complex:
    return 1.0 + 0.0j


# ------------------------------------------------------------------
# Build H_graph
# ------------------------------------------------------------------
def build_H_graph(
    N: int,
    alpha: float,
    ch_2: float = 0.95,
    c_h: float = 1.0,
    c_v: float = 1.0,
    c_d: float = 0.5,
    phase_mode: str = "framework",
    rng=None,
):
    """
    Construct dim x dim Hermitian sparse matrix, dim = N*N.

    phase_mode in {'framework', 'random', 'trivial'}.

    Returns (H, info) where H is sparse Hermitian COO, info is dict.
    """
    dim = N * N
    rows, cols, data = [], [], []

    # 1) Diagonal
    for m in range(N):
        for n in range(N):
            i = vertex_index(m, n, N)
            rows.append(i)
            cols.append(i)
            data.append(berry_keating_weyl(m, n))

    # 2) Off-diagonals; Hermitian-symmetric pairs
    def get_phase(eid: int) -> complex:
        if phase_mode == "framework":
            return phase_framework(eid, alpha)
        elif phase_mode == "random":
            return phase_random(eid, alpha, rng)
        elif phase_mode == "trivial":
            return phase_trivial(eid, alpha)
        else:
            raise ValueError(phase_mode)

    edge_records = []

    # Horizontal edges (m,n) -> (m+1,n)
    for m in range(N - 1):
        for n in range(N):
            i = vertex_index(m, n, N)
            j = vertex_index(m + 1, n, N)
            eid = encode_h(m, n, N)
            phi = get_phase(eid)
            amp = ch_2 * c_h * phi
            rows.append(i)
            cols.append(j)
            data.append(amp)
            rows.append(j)
            cols.append(i)
            data.append(np.conj(amp))
            edge_records.append(("h", m, n, eid, phi))

    # Vertical edges (m,n) -> (m,n+1)
    for m in range(N):
        for n in range(N - 1):
            i = vertex_index(m, n, N)
            j = vertex_index(m, n + 1, N)
            eid = encode_v(m, n, N)
            phi = get_phase(eid)
            amp = ch_2 * c_v * phi
            rows.append(i)
            cols.append(j)
            data.append(amp)
            rows.append(j)
            cols.append(i)
            data.append(np.conj(amp))
            edge_records.append(("v", m, n, eid, phi))

    # Diagonal edges (m,n) -> (m+1, n+1) (creates triangles)
    for m in range(N - 1):
        for n in range(N - 1):
            i = vertex_index(m, n, N)
            j = vertex_index(m + 1, n + 1, N)
            eid = encode_d(m, n, N)
            phi = get_phase(eid)
            amp = ch_2 * c_d * phi
            rows.append(i)
            cols.append(j)
            data.append(amp)
            rows.append(j)
            cols.append(i)
            data.append(np.conj(amp))
            edge_records.append(("d", m, n, eid, phi))

    H = sp.coo_matrix((data, (rows, cols)), shape=(dim, dim)).tocsr()
    # Force exact Hermiticity to wipe FP noise
    H = 0.5 * (H + H.conj().T)

    info = {
        "N": N,
        "dim": dim,
        "alpha": alpha,
        "ch_2": ch_2,
        "c_h": c_h,
        "c_v": c_v,
        "c_d": c_d,
        "phase_mode": phase_mode,
        "n_edges": len(edge_records),
    }
    return H, info, edge_records


# ------------------------------------------------------------------
# Plaquette holonomy verification
# ------------------------------------------------------------------
def plaquette_holonomy_square(m: int, n: int, N: int, alpha: float) -> complex:
    """
    Square plaquette (m,n) -> (m+1,n) -> (m+1,n+1) -> (m,n+1) -> (m,n).
    W = phi_h(m,n) * phi_v(m+1,n) * conj(phi_h(m,n+1)) * conj(phi_v(m,n))
    Uses ONLY horizontal & vertical edges.
    """
    p1 = phase_framework(encode_h(m, n, N), alpha)
    p2 = phase_framework(encode_v(m + 1, n, N), alpha)
    p3 = phase_framework(encode_h(m, n + 1, N), alpha)
    p4 = phase_framework(encode_v(m, n, N), alpha)
    return p1 * p2 * np.conj(p3) * np.conj(p4)


def plaquette_holonomy_triangle_lower(m: int, n: int, N: int, alpha: float) -> complex:
    """
    Lower triangle (m,n) -> (m+1,n) -> (m+1,n+1) -> (m,n).
    Uses horizontal, vertical, conj(diagonal).
    Vertices: (m,n), (m+1,n), (m+1,n+1)
    Edges:
       (m,n)->(m+1,n): horizontal h(m,n) [+phase]
       (m+1,n)->(m+1,n+1): vertical v(m+1,n) [+phase]
       (m+1,n+1)->(m,n): diagonal reversed d(m,n) [conj phase]
    """
    p1 = phase_framework(encode_h(m, n, N), alpha)
    p2 = phase_framework(encode_v(m + 1, n, N), alpha)
    p3 = phase_framework(encode_d(m, n, N), alpha)
    return p1 * p2 * np.conj(p3)


def plaquette_holonomy_triangle_upper(m: int, n: int, N: int, alpha: float) -> complex:
    """
    Upper triangle (m,n) -> (m,n+1) -> (m+1,n+1) -> (m,n).
    """
    p1 = phase_framework(encode_v(m, n, N), alpha)
    p2 = phase_framework(encode_h(m, n + 1, N), alpha)
    p3 = phase_framework(encode_d(m, n, N), alpha)
    return p1 * p2 * np.conj(p3)


def main():
    N = 20
    alpha = 3.0 / 2.0
    ch_2 = 0.95
    print(f"Building H_graph: N={N}, alpha={alpha}, ch_2={ch_2}, dim={N*N}")

    rng = np.random.default_rng(0xFAB)
    H_fw, info_fw, edges_fw = build_H_graph(N, alpha, ch_2=ch_2, phase_mode="framework")
    H_rnd, info_rnd, _ = build_H_graph(N, alpha, ch_2=ch_2, phase_mode="random", rng=rng)
    H_tr, info_tr, _ = build_H_graph(N, alpha, ch_2=ch_2, phase_mode="trivial")

    # Hermiticity check
    for tag, H in [("framework", H_fw), ("random", H_rnd), ("trivial", H_tr)]:
        diff = (H - H.conj().T)
        herr = np.max(np.abs(diff.toarray()))
        print(f"  Hermiticity error ({tag}): {herr:.2e}")

    # Verify plaquette holonomies under framework phases
    print("\n--- Plaquette holonomy (framework Z_3 phases, square plaquettes) ---")
    holos = []
    for m in range(min(5, N - 1)):
        for n in range(min(5, N - 1)):
            W = plaquette_holonomy_square(m, n, N, alpha)
            holos.append(W)
            print(f"  W_sq({m},{n}) = {W.real:+.4f} {W.imag:+.4f}j  |W|={abs(W):.4f}  arg/pi={np.angle(W)/np.pi:+.4f}")

    print("\n--- Plaquette holonomy (triangles) ---")
    for m in range(min(3, N - 1)):
        for n in range(min(3, N - 1)):
            Wl = plaquette_holonomy_triangle_lower(m, n, N, alpha)
            Wu = plaquette_holonomy_triangle_upper(m, n, N, alpha)
            print(f"  W_tri_low({m},{n}) = arg/pi={np.angle(Wl)/np.pi:+.4f}  |W|={abs(Wl):.4f}")
            print(f"  W_tri_up ({m},{n}) = arg/pi={np.angle(Wu)/np.pi:+.4f}  |W|={abs(Wu):.4f}")

    # How many distinct holonomies across the lattice?
    all_W = []
    for m in range(N - 1):
        for n in range(N - 1):
            all_W.append(plaquette_holonomy_square(m, n, N, alpha))
    all_W = np.array(all_W)
    # Quantize phases mod 2 pi/3
    quantized = np.round((np.angle(all_W) / (2 * np.pi / 3))).astype(int) % 3
    unique, counts = np.unique(quantized, return_counts=True)
    print(f"\nSquare-plaquette holonomy distribution (Z_3 sectors), N_plaq={len(all_W)}:")
    for u, c in zip(unique, counts):
        frac = c / len(all_W)
        print(f"   k = {u} ({['+1','exp(2pi.i/3)','exp(-2pi.i/3)'][u]}): {c} ({frac:.2%})")

    nontrivial = sum(1 for W in all_W if abs(W - 1.0) > 1e-6)
    print(f"Non-trivial plaquettes (|W - 1| > 1e-6): {nontrivial}/{len(all_W)} ({nontrivial/len(all_W):.2%})")

    out = {
        "H_framework": H_fw,
        "H_random": H_rnd,
        "H_trivial": H_tr,
        "info_framework": info_fw,
        "info_random": info_rnd,
        "info_trivial": info_tr,
        "N": N,
        "alpha": alpha,
        "ch_2": ch_2,
        "holonomies_square": all_W,
        "holonomy_z3_distribution": dict(zip(unique.tolist(), counts.tolist())),
    }
    path = os.path.join(OUT, "H_graph_built.pkl")
    with open(path, "wb") as f:
        pickle.dump(out, f)
    print(f"\nSaved: {path}")


if __name__ == "__main__":
    main()
