"""
Extended timing study: ch_2 vs Phi_Gaussian
for system sizes n = 4..15.
"""
import time
import numpy as np
from scipy.linalg import solve_discrete_lyapunov

from ch2_vs_phi import ch2_neural, phi_gaussian, erdos_renyi_W


def main():
    print(f"{'n':>3} {'ch_2 (s)':>14} {'Phi_G (s)':>14} {'ratio':>14}")
    print("-" * 50)
    for n in range(4, 16):
        W = erdos_renyi_W(n, 0.4, seed=42)

        t0 = time.perf_counter()
        for _ in range(50):
            _ = ch2_neural(W)
        t_c = (time.perf_counter() - t0) / 50.0

        t0 = time.perf_counter()
        _ = phi_gaussian(W)
        t_p = time.perf_counter() - t0
        print(f"{n:>3} {t_c:>14.6g} {t_p:>14.6g} {t_p/max(t_c,1e-12):>14.2f}x")


if __name__ == "__main__":
    main()
