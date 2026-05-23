"""
Non-compact variant: L^2(R_+, dx/x) (= L^2(R, du) under u = log x).

Here V_alpha(|u|) is the confining potential. Build:
    H = P^2 + V_alpha(|u|)      (Schrodinger style, positive spectrum)
    L_add = P + V_alpha(|u|)    (additive twist)
    L_S   = V P V               (sandwich)
on u in (-U, U) with Dirichlet BC at +- U (representing decay at 0 and inf).

Goal: see if any construction has lowest-positive eigenvalue at pi/(10*alpha).
"""
import numpy as np
import scipy.sparse as sp
from scipy.linalg import eigh
from mellin_twisted import V_alpha, momentum_operator, find_closest

ALPHA_VALUES = [
    ("sqrt2", np.sqrt(2.0), np.pi / (10.0 * np.sqrt(2.0))),
    ("3/2",   1.5,           np.pi / (10.0 * 1.5)),
    ("2",     2.0,           np.pi / (10.0 * 2.0)),
]
EPS_LIST = [0.1, 1.0, np.pi / 10.0, 10.0]


def build_sym_grid(U, N):
    """u in (-U, U) excluding endpoints; spacing h."""
    h = 2.0 * U / (N + 1)
    u = -U + h * np.arange(1, N + 1)
    return u, h


def laplacian_dirichlet(N, h):
    main = -2.0 * np.ones(N) / h**2
    off  =  1.0 * np.ones(N - 1) / h**2
    return sp.diags([off, main, off], [-1, 0, 1], format="csr")


def diag_V(u, alpha):
    return sp.diags(V_alpha(np.abs(u), alpha), format="csr")


def run(constr, alpha, target, eps, U, N):
    u, h = build_sym_grid(U, N)
    V = diag_V(u, alpha)
    if constr == "schrodinger":
        # -d^2/du^2 + eps*V
        L = -laplacian_dirichlet(N, h) + eps * V
        M = L.toarray().astype(np.complex128)
    elif constr == "P+V":
        P = momentum_operator(N, h, bc="dirichlet")  # not strictly s.a. on (-U,U) Dirichlet, but its hermitianization is well-defined
        M = (P + (eps * V).astype(np.complex128)).toarray()
        M = 0.5 * (M + M.conj().T)
    elif constr == "sandwich":
        P = momentum_operator(N, h, bc="dirichlet")
        Vc = (eps * V).astype(np.complex128)
        M = (Vc @ P @ Vc).toarray()
        M = 0.5 * (M + M.conj().T)
    elif constr == "schrod_neg":
        # Allow eps<0 effective potential well shape: -d^2/du^2 - |eps|*|V|
        L = -laplacian_dirichlet(N, h) - abs(eps) * sp.diags(np.abs(V_alpha(np.abs(u), alpha)), format="csr")
        M = L.toarray().astype(np.complex128)
    else:
        raise ValueError(constr)
    w = eigh(0.5 * (M + M.conj().T), eigvals_only=True)[:20]
    cv, gap, rel, idx = find_closest(w, target)
    return w, cv, gap, rel


def main():
    N = 1200
    U_LIST = [5.0, 10.0, 20.0]

    rows = []
    for aname, alpha, target in ALPHA_VALUES:
        for U in U_LIST:
            for eps in EPS_LIST:
                for constr in ["schrodinger", "P+V", "sandwich", "schrod_neg"]:
                    try:
                        w, cv, gap, rel = run(constr, alpha, target, eps, U, N)
                    except Exception as e:
                        print(f"FAIL {constr} alpha={aname} U={U} eps={eps}: {e}")
                        continue
                    rows.append((rel, constr, aname, U, eps, target, cv, w[:5].tolist()))

    rows.sort(key=lambda r: r[0])
    print("=== TOP 20 NONCOMPACT CLOSEST ===")
    for r in rows[:20]:
        rel, constr, aname, U, eps, tgt, cv, w5 = r
        print(f"  {constr:12s} alpha={aname:5s} U={U:4} eps={eps:.4f}  "
              f"target={tgt:.5f}  closest={cv}  gap={rel:.2f}%   "
              f"lowest5={[f'{x:.4f}' for x in w5]}")

    hits = [r for r in rows if r[0] < 1.0]
    print(f"\n<1% hits: {len(hits)}")


if __name__ == "__main__":
    main()
