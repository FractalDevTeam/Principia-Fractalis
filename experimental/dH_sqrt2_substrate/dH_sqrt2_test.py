"""
d_H = sqrt(2) substrate test for Principia Fractalis Ch 21.

Constructs the IFS attractor K in [0,1]^2 with contraction ratio r = 2^(-1/sqrt(2))
so that d_H = log(2)/log(1/r) = sqrt(2).

Tests whether the manuscript's claimed eigenvalue lambda_0 = pi/(10*sqrt(2)) ~ 0.22214
appears as a literal eigenvalue of the natural H_P operator on this substrate.
"""
import numpy as np
from numpy.linalg import eigvalsh, eigh
from itertools import product
import json
import os

OUT = "/home/xluxx/Principia-Fractalis/experimental/dH_sqrt2_substrate/"
os.makedirs(OUT, exist_ok=True)

# --- IFS construction ---------------------------------------------------------
SQ2 = np.sqrt(2.0)
r = 2.0 ** (-1.0 / SQ2)                # ~0.61257
d_H_target = np.log(2) / np.log(1.0 / r)   # = sqrt(2) by construction

print(f"r = {r:.10f}")
print(f"d_H (constructed) = {d_H_target:.10f}, sqrt(2) = {SQ2:.10f}")
print(f"|d_H - sqrt(2)| = {abs(d_H_target - SQ2):.2e}")

# IFS maps: f1(p) = r*p, f2(p) = r*p + (1-r)*(1,1)
def f1(p):
    return r * p
def f2(p):
    return r * p + (1.0 - r)

def attractor_points(k):
    """Enumerate K_k = {f_{w1}...f_{wk}(0,0) : w in {1,2}^k}.
    Order by binary index: bit i (LSB) = w_{i+1} index (1=f1, 2=f2).
    """
    N = 1 << k
    pts = np.zeros((N, 2), dtype=float)
    codes = np.zeros((N, k), dtype=np.int8)  # store codes for ultrametric
    for i in range(N):
        p = np.zeros(2)
        # apply f_{w1} OUTERMOST: standard IFS composition reads code left to right
        # We'll define code as w = (w1, w2, ..., wk) with w1 = MSB of i
        for j in range(k):
            bit = (i >> (k - 1 - j)) & 1
            codes[i, j] = bit
        # apply f_{w_k} ... f_{w_1}(0,0) — outermost (w_1) applied last
        # Standard: x_w = f_{w_1} o f_{w_2} o ... o f_{w_k} (anchor)
        # so we apply from right to left
        for j in range(k - 1, -1, -1):
            bit = codes[i, j]
            p = f2(p) if bit == 1 else f1(p)
        pts[i] = p
    return pts, codes

# --- box-counting dimension verification -------------------------------------
def box_count_dimension(pts, scales=None):
    if scales is None:
        scales = np.logspace(-0.3, -2.5, 12)  # eps from ~0.5 down to ~0.003
    counts = []
    for eps in scales:
        # discretize to a grid of size eps
        grid = np.floor(pts / eps).astype(np.int64)
        unique = set(map(tuple, grid))
        counts.append(len(unique))
    counts = np.array(counts, dtype=float)
    logN = np.log(counts)
    logE = np.log(1.0 / scales)
    # linear fit over the middle range to avoid saturation
    sel = slice(2, -2)
    slope, intercept = np.polyfit(logE[sel], logN[sel], 1)
    return slope, scales, counts

# Generate deep attractor for dimension check
print("\n=== Box-counting dimension check ===")
pts_deep, _ = attractor_points(14)  # 16384 points
dim_est, scales, counts = box_count_dimension(pts_deep)
print(f"Box-counting dim estimate (k=14, 16384 pts): {dim_est:.4f}")
print(f"Target d_H = sqrt(2) = {SQ2:.4f}")
print(f"Note: 2-piece IFS satisfies Open Set Condition => d_H exact = sqrt(2)")

# --- kernel + operator -------------------------------------------------------
def V_kernel(d, alpha, a, N=20):
    """V_alpha(d) = sum_{n=0}^N a^(-n) cos(pi * alpha^n * d)"""
    n = np.arange(N + 1)
    weights = a ** (-n)
    # vectorized: d can be array; build outer
    # For matrix construction we compute per-pair distance
    return np.sum(weights * np.cos(np.pi * (alpha ** n) * d))

def build_H_euclidean(pts, alpha, a, N=20):
    """H_{ij} = (1/M) * V_alpha(||x_i - x_j||_2), M = number of points (= 2^k)."""
    M = pts.shape[0]
    # pairwise euclidean
    diff = pts[:, None, :] - pts[None, :, :]
    D = np.sqrt(np.sum(diff * diff, axis=-1))
    # build V on D
    n = np.arange(N + 1)
    weights = a ** (-n)
    H = np.zeros_like(D)
    for nn, w in zip(n, weights):
        H += w * np.cos(np.pi * (alpha ** nn) * D)
    H *= (1.0 / M)
    # symmetrize (numerical)
    H = 0.5 * (H + H.T)
    return H

def build_H_ultrametric(codes, alpha, a, N=20):
    """Intrinsic ultrametric: d_K(x,y) = (1-r)^(-1) * r^(common_prefix_length).
    Smaller common prefix => bigger distance.
    Common prefix = number of leading bits equal.
    """
    M, K = codes.shape
    # compute common-prefix length matrix
    CP = np.zeros((M, M), dtype=np.int32)
    for i in range(M):
        for j in range(i + 1, M):
            # find first differing bit
            diff = codes[i] ^ codes[j]
            nz = np.flatnonzero(diff)
            cp = K if nz.size == 0 else int(nz[0])
            CP[i, j] = cp
            CP[j, i] = cp
    # diagonal common prefix = K (full match) => distance treated as 0
    diag_mask = np.eye(M, dtype=bool)
    D = (1.0 / (1.0 - r)) * (r ** CP)
    D[diag_mask] = 0.0
    H = np.zeros_like(D)
    n_arr = np.arange(N + 1)
    weights = a ** (-n_arr)
    for nn, w in zip(n_arr, weights):
        H += w * np.cos(np.pi * (alpha ** nn) * D)
    H *= (1.0 / M)
    H = 0.5 * (H + H.T)
    return H

def build_H_phase_twist(pts, codes, alpha, a, N=20):
    """H^phi_{ij} = (1/M) * e^{i pi alpha (b_i - b_j)} * V_alpha(d(x_i,x_j))
    b_i = parity of number of 1's in i (Walsh-style natural invariant for 2-piece IFS).
    Result is Hermitian.
    """
    M = pts.shape[0]
    diff = pts[:, None, :] - pts[None, :, :]
    D = np.sqrt(np.sum(diff * diff, axis=-1))
    V = np.zeros_like(D)
    n_arr = np.arange(N + 1)
    weights = a ** (-n_arr)
    for nn, w in zip(n_arr, weights):
        V += w * np.cos(np.pi * (alpha ** nn) * D)
    V *= (1.0 / M)
    b = codes.sum(axis=1) % 2  # 0 or 1
    phase = np.exp(1j * np.pi * alpha * (b[:, None] - b[None, :]))
    H = phase * V
    H = 0.5 * (H + H.conj().T)
    return H

# --- main spectral sweep ------------------------------------------------------
def report_top(H, label, target=None, hermitian=True):
    if hermitian and np.iscomplexobj(H):
        eigs = np.linalg.eigvalsh(H)
    else:
        eigs = eigvalsh(H)
    eigs_sorted = np.sort(eigs)[::-1]
    print(f"\n{label}")
    print(f"  top 20 eigenvalues (descending):")
    for i, ev in enumerate(eigs_sorted[:20]):
        print(f"    [{i:2d}] {ev: .8f}")
    if target is not None:
        gap = np.min(np.abs(eigs - target))
        nearest = eigs[np.argmin(np.abs(eigs - target))]
        print(f"  target = {target:.8f}")
        print(f"  nearest eigenvalue = {nearest:.8f}")
        print(f"  |gap| = {gap:.6f}")
        return {"label": label, "target": float(target), "nearest": float(nearest),
                "gap": float(gap), "top20": [float(x) for x in eigs_sorted[:20]]}
    return {"label": label, "target": None, "nearest": None,
            "gap": None, "top20": [float(x) for x in eigs_sorted[:20]]}

results = {}

# Step 2-5: tests at k=8 (256 points) on d_H = sqrt(2) attractor
print("\n" + "=" * 72)
print("STEP 4-5: H_alpha at k=8 (256x256) on d_H=sqrt(2) substrate")
print("=" * 72)

pts8, codes8 = attractor_points(8)
print(f"Number of points: {pts8.shape[0]}")

# alpha = sqrt(2), various a
target_P = np.pi / (10.0 * SQ2)
print(f"\nTarget lambda_0 = pi/(10*sqrt(2)) = {target_P:.8f}")

for a_val, a_lbl in [(SQ2, "a = sqrt(2)"), (2.0, "a = 2"), (4.0, "a = 4"),
                     (1.0 / r, "a = 1/r = 2^(1/sqrt(2))")]:
    H = build_H_euclidean(pts8, alpha=SQ2, a=a_val, N=20)
    res = report_top(H, f"Euclidean, alpha=sqrt(2), {a_lbl}, k=8", target=target_P)
    results[f"euc_aP_sqrt2_{a_lbl}"] = res

# Step 6: depth convergence
print("\n" + "=" * 72)
print("STEP 6: depth convergence k=6,7,8 at alpha=sqrt(2), a=sqrt(2)")
print("=" * 72)
for k in [6, 7, 8]:
    pts_k, _ = attractor_points(k)
    H = build_H_euclidean(pts_k, alpha=SQ2, a=SQ2, N=20)
    res = report_top(H, f"k={k}, Euclidean, alpha=sqrt(2), a=sqrt(2)", target=target_P)
    results[f"depth_k{k}"] = res

# Also depth convergence at a = 1/r (IFS-natural)
print("\n--- depth convergence at a = 1/r (IFS-natural) ---")
for k in [6, 7, 8]:
    pts_k, _ = attractor_points(k)
    H = build_H_euclidean(pts_k, alpha=SQ2, a=1.0 / r, N=20)
    res = report_top(H, f"k={k}, Euclidean, alpha=sqrt(2), a=1/r", target=target_P)
    results[f"depth_natural_k{k}"] = res

# Step 7: alpha = 3/2 (target pi/15) and alpha = 2 (target pi/20)
print("\n" + "=" * 72)
print("STEP 7: other alpha values on d_H=sqrt(2) substrate, k=8")
print("=" * 72)
target_32 = np.pi / 15.0
target_2 = np.pi / 20.0

for a_val, a_lbl in [(1.5, "a = 3/2"), (2.0, "a = 2"), (1.0 / r, "a = 1/r")]:
    H = build_H_euclidean(pts8, alpha=1.5, a=a_val, N=20)
    res = report_top(H, f"Euclidean, alpha=3/2, {a_lbl}, k=8", target=target_32)
    results[f"alpha_32_{a_lbl}"] = res

for a_val, a_lbl in [(2.0, "a = 2"), (4.0, "a = 4"), (1.0 / r, "a = 1/r")]:
    H = build_H_euclidean(pts8, alpha=2.0, a=a_val, N=20)
    res = report_top(H, f"Euclidean, alpha=2, {a_lbl}, k=8", target=target_2)
    results[f"alpha_2_{a_lbl}"] = res

# Step 8: phase-twist variant
print("\n" + "=" * 72)
print("STEP 8: PHASE-TWIST variant on d_H=sqrt(2), k=8")
print("=" * 72)
for a_val, a_lbl in [(SQ2, "a=sqrt(2)"), (2.0, "a=2"), (1.0 / r, "a=1/r")]:
    H = build_H_phase_twist(pts8, codes8, alpha=SQ2, a=a_val, N=20)
    res = report_top(H, f"Phase-twist Hermitian, alpha=sqrt(2), {a_lbl}, k=8", target=target_P)
    results[f"twist_{a_lbl}"] = res

# Step 9: intrinsic ultrametric
print("\n" + "=" * 72)
print("STEP 9: INTRINSIC ULTRAMETRIC on d_H=sqrt(2), k=8")
print("=" * 72)
for a_val, a_lbl in [(SQ2, "a=sqrt(2)"), (2.0, "a=2"), (1.0 / r, "a=1/r")]:
    H = build_H_ultrametric(codes8, alpha=SQ2, a=a_val, N=20)
    res = report_top(H, f"Ultrametric, alpha=sqrt(2), {a_lbl}, k=8", target=target_P)
    results[f"ultra_{a_lbl}"] = res

# Save results
results["metadata"] = {
    "r": float(r), "d_H_target": float(d_H_target), "sqrt2": float(SQ2),
    "box_counting_dim_k14": float(dim_est),
    "targets": {
        "pi_over_10_sqrt2": float(target_P),
        "pi_over_15": float(target_32),
        "pi_over_20": float(target_2),
    }
}
with open(os.path.join(OUT, "results.json"), "w") as f:
    json.dump(results, f, indent=2)

# --- summary: closest gap to pi/(10*sqrt(2)) across ALL configurations -------
print("\n" + "=" * 72)
print("OVERALL SUMMARY: best gap to pi/(10*sqrt(2)) ~ 0.22214")
print("=" * 72)
best = None
for k, v in results.items():
    if k == "metadata":
        continue
    if v.get("target") is None:
        continue
    if v["target"] != float(target_P):
        continue
    if best is None or v["gap"] < best[1]:
        best = (v["label"], v["gap"], v["nearest"])
print(f"BEST MATCH to pi/(10*sqrt(2)) = {target_P:.6f}:")
if best:
    print(f"  config:  {best[0]}")
    print(f"  nearest: {best[2]:.8f}")
    print(f"  gap:     {best[1]:.6f}")
    print(f"  threshold for 'hit' at 0.001 level: {'HIT' if best[1] < 1e-3 else 'MISS'}")
    print(f"  threshold for 'hit' at 0.01 level:  {'HIT' if best[1] < 1e-2 else 'MISS'}")
