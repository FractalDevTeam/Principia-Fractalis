"""
05 — Forensic search for pi/(10*sqrt(2)) = 0.22214 in the spectrum.

Search across operator variants:
  V1:  V(x,y) = sum a^(-n) cos(pi alpha^n |x-y|)        (current)
  V2:  V(x,y) = sum a^(-n) cos(pi alpha^n (x-y))        (no abs val) -- same since cos even
  V3:  V(x,y) = sum a^(-n) sin(pi alpha^n |x-y|)        (sine kernel)
  V4:  V(x,y) = sum alpha^(-n) cos(pi alpha^n |x-y|)    (a = alpha)
  V5:  V(x,y) = sum a^(-n) cos(2 pi alpha^n |x-y|)      (2pi instead of pi)
  V6:  V(x,y) = sum a^(-n) cos(pi alpha^n |x-y|)        on K with COUNTING measure
                                                         (not Hausdorff)

For each, check if 0.22214 appears in top 20 eigenvalues on:
  (a) Cantor K at N=8
  (b) Lebesgue [0,1] at M=512
"""
import sys, importlib.util
import numpy as np
from numpy.linalg import eigh

spec = importlib.util.spec_from_file_location("k1", "01_kernel_and_cantor.py")
k1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(k1)

ALPHA = k1.ALPHA
LAMBDA_PRED = k1.LAMBDA_PRED


def kernel_variant(x, y, variant, alpha=ALPHA, a=2.0, n_max=80):
    d = np.abs(np.asarray(x) - np.asarray(y))
    n = np.arange(n_max + 1)
    if variant == "V1":  # standard
        decay = a ** (-n)
        arg = np.pi * np.multiply.outer(d, alpha ** n)
        return np.sum(decay * np.cos(arg), axis=-1)
    if variant == "V3":  # sin
        decay = a ** (-n)
        arg = np.pi * np.multiply.outer(d, alpha ** n)
        return np.sum(decay * np.sin(arg), axis=-1)
    if variant == "V4":  # a=alpha (decay=alpha^-n)
        decay = alpha ** (-n)
        arg = np.pi * np.multiply.outer(d, alpha ** n)
        return np.sum(decay * np.cos(arg), axis=-1)
    if variant == "V5":  # 2pi
        decay = a ** (-n)
        arg = 2 * np.pi * np.multiply.outer(d, alpha ** n)
        return np.sum(decay * np.cos(arg), axis=-1)
    if variant == "V6":  # cos with phase (1 - cos = 2 sin^2)
        decay = a ** (-n)
        arg = np.pi * np.multiply.outer(d, alpha ** n)
        return np.sum(decay * (1.0 - np.cos(arg)), axis=-1)
    raise ValueError(variant)


def closest_eig(eigvals, target):
    """Find eigenvalue closest to target."""
    diffs = np.abs(eigvals - target)
    i = diffs.argmin()
    return eigvals[i], diffs[i]


def spectrum(pts, weights, variant, alpha=ALPHA, a=2.0, n_max=80):
    V = kernel_variant(pts[:, None], pts[None, :], variant, alpha=alpha, a=a, n_max=n_max)
    sw = np.sqrt(weights)
    H_sym = sw[:, None] * V * sw[None, :]
    eigvals, _ = eigh(H_sym)
    return eigvals


def main():
    print(f"Target = pi/(10 sqrt 2) = {LAMBDA_PRED:.10f}")
    print(f"Also test = pi/(10 phi) = {np.pi / (10 * (1 + np.sqrt(5))/2):.10f}")
    print(f"Also test = pi/10       = {np.pi/10:.10f}")
    print(f"Also test = pi/(10*2)   = {np.pi/20:.10f}")

    N = 9
    pts_c = k1.cantor_points(N)
    w_c = k1.hausdorff_weights(N)

    M = 600
    pts_l = (np.arange(M) + 0.5) / M
    w_l = np.full(M, 1.0 / M)

    targets = {
        "pi/(10 sqrt 2)": np.pi / (10 * np.sqrt(2)),
        "pi/(10 phi)":    np.pi / (10 * (1 + np.sqrt(5))/2),
        "pi/10":          np.pi / 10,
        "pi/20":          np.pi / 20,
        "1/sqrt(2)":      1.0/np.sqrt(2),
        "1/(2 sqrt 2)":   1.0/(2*np.sqrt(2)),
    }

    for variant in ["V1", "V3", "V4", "V5", "V6"]:
        print(f"\n=== Variant {variant} ===")
        try:
            eigC = spectrum(pts_c, w_c, variant)
            eigL = spectrum(pts_l, w_l, variant)
        except Exception as e:
            print(f"  failed: {e}")
            continue
        for label, t in targets.items():
            c, d_c = closest_eig(eigC, t)
            l, d_l = closest_eig(eigL, t)
            mark_c = "<<<" if d_c < 1e-3 else ""
            mark_l = "<<<" if d_l < 1e-3 else ""
            print(f"  Cantor closest to {label:18s} ({t:.6f}): "
                  f"{c:+.6f}  diff {d_c:.3e} {mark_c}")
            print(f"  Lebesg closest to {label:18s} ({t:.6f}): "
                  f"{l:+.6f}  diff {d_l:.3e} {mark_l}")

    # And one more probe -- maybe the predicted lambda_0 is the SPECTRAL GAP
    print("\n=== Spectral gaps (Cantor, V1) ===")
    eigC = spectrum(pts_c, w_c, "V1")
    sorted_desc = np.sort(eigC)[::-1]
    print(f"  Top 6 eigenvalues: {sorted_desc[:6]}")
    print(f"  Gap lam_0 - lam_1 = {sorted_desc[0]-sorted_desc[1]:.6f}")
    print(f"  Gap lam_1 - lam_2 = {sorted_desc[1]-sorted_desc[2]:.6f}")
    print(f"  Gap lam_2 - lam_3 = {sorted_desc[2]-sorted_desc[3]:.6f}")
    print(f"  Target lambda_pred = {LAMBDA_PRED:.6f}")


if __name__ == "__main__":
    main()
