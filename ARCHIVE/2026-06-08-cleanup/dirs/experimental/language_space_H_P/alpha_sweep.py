"""
Alpha sweep: scan alpha in [0.1, 4] and ask:
  (1) ||H_P - H_P*||_inf  (self-adjointness as function of alpha)
  (2) min |w_herm - pi/(10*alpha)| (closest Hermitian-part eigenvalue to target)

If the manuscript is right, BOTH should vanish at alpha = sqrt(2) ~ 1.4142.

Use N=2 (M=7, dim=128), E=trivial, since other E choices were never self-adjoint.
"""
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from hp_language_n2 import build_HP, E_trivial

alphas = np.linspace(0.1, 4.0, 400)
sa_errs = []
gaps   = []
gaps_real = []   # min |Re(eig) - target| over all (complex) eigvals
for a in alphas:
    H = build_HP(a, E_trivial)
    sa_errs.append(np.max(np.abs(H - H.conj().T)))
    H_herm = 0.5 * (H + H.conj().T)
    w_herm = np.linalg.eigvalsh(H_herm)
    w_full = np.linalg.eigvals(H)
    target = np.pi / (10 * a)
    gaps.append(np.min(np.abs(w_herm - target)))
    gaps_real.append(np.min(np.abs(np.real(w_full) - target)))

sa_errs = np.array(sa_errs)
gaps = np.array(gaps)
gaps_real = np.array(gaps_real)

fig, axes = plt.subplots(2, 1, figsize=(10, 8))
axes[0].plot(alphas, sa_errs, lw=1.2)
for a, lbl in [(np.sqrt(2), r'$\sqrt{2}$'), (1.5, '3/2'), (2.0, '2')]:
    axes[0].axvline(a, color='r' if abs(a-np.sqrt(2))<1e-9 else 'gray',
                    ls='--', alpha=0.6, label=lbl)
axes[0].set_xlabel(r'$\alpha$'); axes[0].set_ylabel(r'$\|H_P - H_P^*\|_\infty$')
axes[0].set_title(r'Self-adjointness of $H_P$ on language space (N=2, E=trivial)')
axes[0].grid(alpha=0.3); axes[0].legend()

axes[1].semilogy(alphas, gaps, lw=1.2, label='min |w_herm - pi/(10a)|')
axes[1].semilogy(alphas, gaps_real, lw=1.2, label='min |Re(w_full) - pi/(10a)|', alpha=0.7)
for a, lbl in [(np.sqrt(2), r'$\sqrt{2}$'), (1.5, '3/2'), (2.0, '2')]:
    axes[1].axvline(a, color='r' if abs(a-np.sqrt(2))<1e-9 else 'gray',
                    ls='--', alpha=0.6, label=lbl)
axes[1].set_xlabel(r'$\alpha$'); axes[1].set_ylabel('Gap to target')
axes[1].set_title(r'Closest spectrum to manuscript target $\pi/(10\alpha)$')
axes[1].grid(alpha=0.3); axes[1].legend()

plt.tight_layout()
plt.savefig('/home/xluxx/Principia-Fractalis/experimental/language_space_H_P/alpha_sweep.png', dpi=130)

# Print summary
i_min_sa = np.argmin(sa_errs)
i_min_gap = np.argmin(gaps)
print(f"min ||H-H*|| at alpha = {alphas[i_min_sa]:.4f} (value = {sa_errs[i_min_sa]:.4e})")
print(f"  sqrt(2) = 1.4142;  3/2 = 1.5;  2 = 2.0")
print(f"min gap_herm at alpha = {alphas[i_min_gap]:.4f} (value = {gaps[i_min_gap]:.4e})")
print(f"  target at this alpha = pi/(10*{alphas[i_min_gap]:.4f}) = {np.pi/(10*alphas[i_min_gap]):.6f}")

# Around sqrt(2)
mask = np.abs(alphas - np.sqrt(2)) < 0.05
print(f"\nNear alpha = sqrt(2):")
for a, sa, g in zip(alphas[mask], sa_errs[mask], gaps[mask]):
    print(f"  alpha = {a:.4f}  ||H-H*||={sa:.4f}  gap_herm={g:.6f}")
