"""
Mellin-twisted dilation generator experiments.

Hypothesis: the right operator for the universal spectral identity
    lambda_0(alpha) = pi/(10*alpha)
is a Mellin dilation generator on L^2(R_+, dx/x) twisted by V_alpha,
NOT the bare convolution H_alpha.

On L^2((1, beta), dx/x), via the log substitution u = log x,
the space becomes L^2((0, log beta), du), and
    -i d/d(log x) = -i d/du
which is the translation generator P = -i d/du. Its self-adjoint
extensions on a bounded interval (0, L) are well-known: with periodic
BC the spectrum is {2*pi*n/L : n in Z}, with theta BC it shifts.

We test several twists of this base operator by V_alpha(|log x|) = V_alpha(|u|).
"""
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla
from scipy.linalg import eigh
import sys

ALPHA_VALUES = [
    ("sqrt2", np.sqrt(2.0), np.pi / (10.0 * np.sqrt(2.0))),
    ("3/2",   1.5,           np.pi / (10.0 * 1.5)),
    ("2",     2.0,           np.pi / (10.0 * 2.0)),
]

EPS_VALUES = [
    ("eps=0.1",   0.1),
    ("eps=1",     1.0),
    ("eps=pi/10", np.pi / 10.0),
    ("eps=10",    10.0),
]


def V_alpha(d, alpha, n_terms=60):
    """V_alpha(d) = sum_{n=0}^inf 2^{-n} cos(pi * alpha^n * d)."""
    d = np.asarray(d, dtype=np.float64)
    out = np.zeros_like(d)
    for n in range(n_terms):
        out += (2.0 ** (-n)) * np.cos(np.pi * (alpha ** n) * d)
    return out


def build_grid(L, N):
    """u in (0, L), N interior points; spacing h = L/(N+1)."""
    h = L / (N + 1)
    u = np.linspace(h, L - h, N)
    return u, h


def momentum_operator(N, h, bc="periodic"):
    """
    P = -i d/du as a Hermitian sparse matrix.
    Use centered finite differences:
        (Pf)_j = -i (f_{j+1} - f_{j-1}) / (2h)
    With periodic BC (consistent with translation generator on a circle
    representing one dilation period u in [0, L)) it is exactly self-adjoint.
    """
    # Imaginary off-diagonals: +i/(2h) on subdiagonal, -i/(2h) on superdiagonal
    # so that P = -i*(D_+ - D_-)/2 = -i*(forward - backward)/2 = -i d/du centered.
    diag_up = -1j / (2.0 * h) * np.ones(N - 1, dtype=np.complex128)
    diag_dn =  1j / (2.0 * h) * np.ones(N - 1, dtype=np.complex128)
    P = sp.diags([diag_dn, diag_up], offsets=[-1, 1], format="lil",
                 dtype=np.complex128)
    if bc == "periodic":
        # wrap: f_{N} <-> f_0
        P[0, N - 1] =  1j / (2.0 * h)
        P[N - 1, 0] = -1j / (2.0 * h)
    elif bc == "dirichlet":
        pass  # boundary terms vanish, but P is NOT self-adjoint here; OK only for inspection
    return P.tocsr()


def derivative_operator(N, h, bc="periodic"):
    """d/du centered FD (real)."""
    diag_up =  1.0 / (2.0 * h) * np.ones(N - 1)
    diag_dn = -1.0 / (2.0 * h) * np.ones(N - 1)
    D = sp.diags([diag_dn, diag_up], offsets=[-1, 1], format="lil")
    if bc == "periodic":
        D[0, N - 1] = -1.0 / (2.0 * h)
        D[N - 1, 0] =  1.0 / (2.0 * h)
    return D.tocsr()


def diag_V(u, alpha):
    """V_alpha(|u|) as a diagonal sparse matrix."""
    vals = V_alpha(np.abs(u), alpha)
    return sp.diags(vals, format="csr"), vals


def construction_a_additive(alpha, eps, L, N):
    """L = P + eps*V, additive."""
    u, h = build_grid(L, N)
    P = momentum_operator(N, h, bc="periodic")
    V, _ = diag_V(u, alpha)
    return (P + eps * V.astype(np.complex128)).toarray(), u


def construction_b_multiplicative(alpha, eps, L, N):
    """
    L = (eps*V) * P  symmetrized to (V P + P V)/2 to ensure self-adjointness.
    eps scales the twist strength.
    """
    u, h = build_grid(L, N)
    P = momentum_operator(N, h, bc="periodic")
    V, _ = diag_V(u, alpha)
    Vc = (eps * V).astype(np.complex128)
    M = 0.5 * (Vc @ P + P @ Vc)
    return M.toarray(), u


def construction_c_sandwich(alpha, eps, L, N):
    """L = V P V (symmetric automatically since V is real diagonal)."""
    u, h = build_grid(L, N)
    P = momentum_operator(N, h, bc="periodic")
    V, _ = diag_V(u, alpha)
    Vc = (eps * V).astype(np.complex128)
    M = Vc @ P @ Vc
    return M.toarray(), u


def construction_d_sturm_liouville(alpha, eps, L, N):
    """
    L = -d/du (W(u) d/du) with W(u) = 1 + eps*V_alpha(|u|).
    Implemented as -D^T diag(W) D with periodic BC.
    This is REAL, self-adjoint (positive-semidefinite if W >= 0 ).
    """
    u, h = build_grid(L, N)
    D = derivative_operator(N, h, bc="periodic")
    _, vvals = diag_V(u, alpha)
    W = sp.diags(1.0 + eps * vvals, format="csr")
    M = -(D.T @ W @ D)
    return M.toarray().astype(np.complex128), u


def diagonalize(M, k=20):
    """Return ALL sorted eigenvalues (real parts) of the Hermitian-ized matrix.
    k is a hint for the report but we return all so we can split + and - parts."""
    M = 0.5 * (M + M.conj().T)
    w = eigh(M, eigvals_only=True)
    return w


def find_closest(spectrum, target):
    """Return (closest_eigenvalue, abs_gap, relative_pct, index).
    Searches over ALL eigenvalues but reports the closest match to target."""
    s = np.asarray(spectrum)
    # Closest to target by absolute distance, over the WHOLE spectrum (incl. negatives)
    if len(s) == 0:
        return (None, np.inf, np.inf, -1)
    idx = int(np.argmin(np.abs(s - target)))
    val = float(s[idx])
    gap = abs(val - target)
    rel = 100.0 * gap / target
    return (val, gap, rel, idx)


def find_lowest_positive(spectrum):
    s = np.asarray(spectrum)
    pos = s[s > 1e-10]
    if len(pos) == 0:
        return None
    return float(np.min(pos))


def run_one(constr_name, constr_func, alpha_name, alpha, target, eps_name, eps,
            k_periods, N):
    L = k_periods * np.log(alpha)
    M, u = constr_func(alpha, eps, L, N)
    w = diagonalize(M, k=20)
    cv, gap, rel, idx = find_closest(w, target)
    lowest_pos = find_lowest_positive(w)
    # Take 20 closest-to-target eigenvalues for inspection
    order = np.argsort(np.abs(w - target))
    near = w[order[:20]]
    pos20 = w[w > 1e-10][:20]
    hit_1pct = (rel < 1.0)
    return {
        "construction": constr_name,
        "alpha_name": alpha_name,
        "alpha": alpha,
        "target": target,
        "eps_name": eps_name,
        "eps": eps,
        "k_periods": k_periods,
        "L": L,
        "N": N,
        "lowest20pos": pos20.tolist(),
        "near20": sorted(near.tolist()),
        "lowest_pos": lowest_pos,
        "closest_pos": cv,
        "gap_abs": gap,
        "gap_pct": rel,
        "hit_1pct": hit_1pct,
    }


def main():
    constructions = [
        ("A_additive",        construction_a_additive),
        ("B_multiplicative",  construction_b_multiplicative),
        ("C_sandwich",        construction_c_sandwich),
        ("D_sturm_liouville", construction_d_sturm_liouville),
    ]

    N = 800
    K_LIST = [1, 2, 3, 4]

    hits = []
    closest_overall = []

    for cname, cfunc in constructions:
        for aname, alpha, target in ALPHA_VALUES:
            for ename, eps in EPS_VALUES:
                for k in K_LIST:
                    try:
                        res = run_one(cname, cfunc, aname, alpha, target,
                                      ename, eps, k, N)
                    except Exception as e:
                        print(f"FAIL {cname} alpha={aname} {ename} k={k}: {e}",
                              file=sys.stderr)
                        continue
                    tag = (f"{cname} | alpha={aname} | {ename} | k={k} | "
                           f"target={target:.5f} | closest={res['closest_pos']}"
                           f" | gap={res['gap_pct']:.2f}%")
                    if res["hit_1pct"]:
                        print("HIT  ", tag)
                        hits.append(res)
                    closest_overall.append(res)

    # Summary: top 15 closest overall
    def safe(v, fmt=".5f"):
        if v is None or (isinstance(v, float) and not np.isfinite(v)):
            return "None"
        return format(v, fmt)

    closest_overall.sort(key=lambda r: r["gap_pct"]
                         if (r["gap_pct"] is not None and np.isfinite(r["gap_pct"]))
                         else 1e18)
    print("\n=== TOP 25 CLOSEST CONFIGURATIONS (any alpha) ===")
    for r in closest_overall[:25]:
        print(f"  {r['construction']:20s} alpha={r['alpha_name']:5s} "
              f"{r['eps_name']:10s} k={r['k_periods']} "
              f"target={safe(r['target'])}  closest={safe(r['closest_pos'])}  "
              f"gap={safe(r['gap_pct'], '.2f')}%")

    print(f"\n=== TOTAL <1% HITS: {len(hits)} ===")

    # Per-alpha best
    print("\n=== BEST PER ALPHA ===")
    for aname, alpha, target in ALPHA_VALUES:
        candidates = [r for r in closest_overall if r["alpha_name"] == aname]
        candidates = [c for c in candidates if c["closest_pos"] is not None]
        candidates.sort(key=lambda r: r["gap_pct"])
        if candidates:
            r = candidates[0]
            print(f"  alpha={aname:5s} target={safe(r['target'])}  best="
                  f"{r['construction']} {r['eps_name']} k={r['k_periods']} "
                  f"closest={safe(r['closest_pos'])} gap={safe(r['gap_pct'], '.3f')}%")

    # Lowest positive eigenvalues per construction at alpha=sqrt2, eps=pi/10
    print("\n=== INSPECTION: lowest 8 positive eigenvalues at alpha=sqrt2, eps=pi/10 ===")
    for r in closest_overall:
        if r["alpha_name"] == "sqrt2" and r["eps_name"] == "eps=pi/10":
            pos = r["lowest20pos"][:8]
            tag = f"{r['construction']:20s} k={r['k_periods']}"
            print(f"  {tag}: " + " ".join(f"{x:.4f}" for x in pos))

    print("\n=== INSPECTION: NEAR-TARGET (20 closest to pi/(10 alpha)) at alpha=sqrt2, eps=1, k=4 ===")
    for r in closest_overall:
        if (r["alpha_name"] == "sqrt2" and r["eps_name"] == "eps=1"
                and r["k_periods"] == 4):
            tag = f"{r['construction']:20s}"
            print(f"  {tag}: " + " ".join(f"{x:.4f}" for x in r["near20"][:10]))

    return hits, closest_overall


if __name__ == "__main__":
    main()
