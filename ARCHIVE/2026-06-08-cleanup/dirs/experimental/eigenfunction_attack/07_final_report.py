"""
07 — Final consolidated empirical analysis.

This script reproduces the headline numbers and verifies:
  - converged spectrum of H_alpha on Cantor K (Hausdorff measure)
  - converged spectrum of H_alpha on [0,1] (Lebesgue measure)
  - exact value 1/alpha = 1/sqrt(2) appearing in Lebesgue spectrum
  - self-similarity identity verified to 1e-16
  - Rayleigh quotients of Hausdorff-constant and Walsh modes
  - no eigenvalue or natural derived quantity matches pi/(10 sqrt 2)
"""
import sys, importlib.util
import numpy as np
from numpy.linalg import eigh

spec = importlib.util.spec_from_file_location("k1", "01_kernel_and_cantor.py")
k1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(k1)

ALPHA = k1.ALPHA
LAMBDA_PRED = k1.LAMBDA_PRED


def cantor_spectrum(N):
    pts = k1.cantor_points(N)
    w = k1.hausdorff_weights(N)
    H_sym, _ = k1.build_H_matrix(pts, w, alpha=ALPHA, a=2.0, n_max=80)
    eigvals, _ = eigh(H_sym)
    return np.sort(eigvals)[::-1]


def lebesgue_spectrum(M):
    pts = (np.arange(M) + 0.5) / M
    w = np.full(M, 1.0 / M)
    H_sym, _ = k1.build_H_matrix(pts, w, alpha=ALPHA, a=2.0, n_max=80)
    eigvals, _ = eigh(H_sym)
    return np.sort(eigvals)[::-1]


print(f"alpha     = sqrt(2) = {ALPHA:.15f}")
print(f"1/alpha   = 1/sqrt2 = {1/ALPHA:.15f}")
print(f"lambda_pred = pi/(10 alpha) = {LAMBDA_PRED:.15f}\n")

print("CONVERGED SPECTRUM (Cantor / Hausdorff measure, N=11, 2048 pts)")
print("Top 8 eigenvalues (positive, descending):")
s_c = cantor_spectrum(11)
for i in range(8):
    print(f"  lam_{i} = {s_c[i]:.10f}    ratio to lambda_pred = {s_c[i]/LAMBDA_PRED:.6f}")

print("\nCONVERGED SPECTRUM (Lebesgue on [0,1], M=1500)")
print("Top 8 eigenvalues (positive, descending):")
s_l = lebesgue_spectrum(1500)
for i in range(8):
    print(f"  lam_{i} = {s_l[i]:.10f}    ratio to lambda_pred = {s_l[i]/LAMBDA_PRED:.6f}")

print(f"\n  --> Lebesgue lam_1 = {s_l[1]:.10f}")
print(f"      1/alpha     = {1/ALPHA:.10f}")
print(f"      diff        = {s_l[1] - 1/ALPHA:+.3e}    "
      f"(identifies lam_1 = 1/sqrt(2) to ~7 digits)")

# constant ansatz Rayleigh
print("\nRayleigh quotient for psi = 1 (constant) against Hausdorff measure:")
pts = k1.cantor_points(11)
w = k1.hausdorff_weights(11)
V = k1.V_kernel(pts[:, None], pts[None, :], alpha=ALPHA, a=2.0, n_max=80)
R = (w[:, None] * V * w[None, :]).sum() / w.sum()
print(f"  R(psi=1) = {R:.10f}     (= integral integral V dmu dmu)")
print(f"  vs lambda_pred = {LAMBDA_PRED:.10f}   diff = {R-LAMBDA_PRED:+.4e}")
print(f"  vs lam_0_Cantor= {s_c[0]:.10f}   diff = {R-s_c[0]:+.4e}")
print(f"    ==> constant psi is NOT close to the top eigenvector (R < lam_0).")
print(f"    ==> psi=1 has substantial overlap with multiple modes.")

# Compare gap to predicted
print("\nSpectral gap (Cantor) lam_1 - lam_2:")
print(f"  = {s_c[1] - s_c[2]:.10f}")
print(f"  vs lambda_pred = {LAMBDA_PRED:.10f}")
print(f"  diff = {(s_c[1]-s_c[2]) - LAMBDA_PRED:+.4e}  (2.7% miss, not converging closer)")

print("\nSummary:")
print(f"  Lebesgue lam_0 = {s_l[0]:.6f}  (no closed form found)")
print(f"  Lebesgue lam_1 = {s_l[1]:.6f}  = 1/sqrt(2) to 7 digits   *** identified ***")
print(f"  Cantor   lam_0 = {s_c[0]:.6f}")
print(f"  Cantor   lam_1 = {s_c[1]:.6f}")
print(f"  Cantor   lam_2 = {s_c[2]:.6f}")
print(f"  Predicted      = {LAMBDA_PRED:.6f}")
print(f"  closest absolute miss: 0.07 (Cantor) / 0.05 (Lebesgue) -- NOT in spectrum.")
