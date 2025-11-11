#!/usr/bin/env python3
"""
Quick diagnostic plot showing eigenvalue pathology.
"""

import numpy as np
import matplotlib.pyplot as plt

# Eigenvalue data from computation
eigenvalues_N10 = [
    154402699.64, 24926665.91, -587926.11, 584680.27, 553631.56,
    -550374.01, -3915.46, 3909.22, -736.07, 735.08
]

eigenvalues_N20 = [
    181241252.85, 110899883.68, 64148122.62, 64148121.86, -44591612.13,
    -44591569.98, -34340996.70, 33234582.88, 33233671.73, -27499156.34,
    -27499060.63, -20987062.38, 17979039.81, 17978756.04, -15026825.47,
    14974074.12, -14973981.51, 11765453.38, -11765353.27, -4628302.65
]

# Expected: eigenvalues ~ O(1) for normalized operator with ||T||_HS = √3
expected_max = np.sqrt(3)

fig, axes = plt.subplots(2, 2, figsize=(14, 10))

# Plot 1: Eigenvalue magnitudes
ax = axes[0, 0]
ax.semilogy(range(1, len(eigenvalues_N10)+1), np.abs(eigenvalues_N10),
            'o-', label='N=10', markersize=8)
ax.semilogy(range(1, len(eigenvalues_N20)+1), np.abs(eigenvalues_N20),
            's-', label='N=20', markersize=6)
ax.axhline(expected_max, color='red', linestyle='--', linewidth=2,
           label=f'Expected max (√3 ≈ {expected_max:.2f})')
ax.set_xlabel('Eigenvalue Index', fontsize=12)
ax.set_ylabel('|λ|', fontsize=12)
ax.set_title('Eigenvalue Magnitudes: Observed vs. Expected', fontsize=14, fontweight='bold')
ax.legend()
ax.grid(True, alpha=0.3)
ax.text(0.5, 0.95, 'PATHOLOGY: Eigenvalues are 10⁸ times too large!',
        transform=ax.transAxes, ha='center', va='top',
        bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.8),
        fontsize=10, fontweight='bold')

# Plot 2: Sign pattern
ax = axes[0, 1]
signs_N10 = [np.sign(lam) for lam in eigenvalues_N10]
signs_N20 = [np.sign(lam) for lam in eigenvalues_N20]
ax.plot(range(1, len(signs_N10)+1), signs_N10, 'o-', label='N=10', markersize=8)
ax.plot(range(1, len(signs_N20)+1), signs_N20, 's-', label='N=20', markersize=6, alpha=0.6)
ax.set_xlabel('Eigenvalue Index', fontsize=12)
ax.set_ylabel('Sign(λ)', fontsize=12)
ax.set_title('Eigenvalue Signs (Self-Adjoint ⇒ All Real)', fontsize=14, fontweight='bold')
ax.set_ylim(-1.5, 1.5)
ax.legend()
ax.grid(True, alpha=0.3)
ax.text(0.5, 0.05, 'Real eigenvalues confirmed (but magnitudes wrong)',
        transform=ax.transAxes, ha='center', va='bottom',
        bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.8),
        fontsize=10)

# Plot 3: Trace class analysis
ax = axes[1, 0]
partial_sums_N20 = np.cumsum(np.abs(eigenvalues_N20))
indices = np.arange(1, len(partial_sums_N20) + 1)

# Fit: S_N ~ A * N^α
log_S = np.log(partial_sums_N20)
log_N = np.log(indices)
coeffs = np.polyfit(log_N, log_S, 1)
alpha = coeffs[0]
log_A = coeffs[1]
A = np.exp(log_A)

fit = A * indices**alpha

ax.loglog(indices, partial_sums_N20, 'o-', label='Actual S_N', markersize=6)
ax.loglog(indices, fit, '--', label=f'Fit: S_N ~ {A:.2e} × N^{alpha:.3f}', linewidth=2)
ax.set_xlabel('N (number of eigenvalues)', fontsize=12)
ax.set_ylabel('S_N = Σ|λₖ|', fontsize=12)
ax.set_title(f'Trace Class Test: α = {alpha:.3f} < 1 ⇒ Converges', fontsize=14, fontweight='bold')
ax.legend()
ax.grid(True, alpha=0.3)
if alpha < 1:
    verdict = "Trace class (if eigenvalues were valid)"
    color = 'lightblue'
else:
    verdict = "NOT trace class"
    color = 'lightcoral'
ax.text(0.5, 0.05, verdict,
        transform=ax.transAxes, ha='center', va='bottom',
        bbox=dict(boxstyle='round', facecolor=color, alpha=0.8),
        fontsize=10, fontweight='bold')

# Plot 4: Comparison with expected behavior
ax = axes[1, 1]
# For a properly normalized operator with ||T||_HS = √3:
# Eigenvalues should satisfy Σ λᵢ² ≤ ||T||²_HS = 3
cumulative_eigenvalue_norm_squared = np.cumsum([lam**2 for lam in eigenvalues_N20])
expected_bound = 3.0

ax.semilogy(indices, cumulative_eigenvalue_norm_squared, 'o-',
            label='Σλᵢ² (actual)', markersize=6, color='red')
ax.axhline(expected_bound, color='green', linestyle='--', linewidth=2,
           label=f'Hilbert-Schmidt bound = 3')
ax.set_xlabel('Number of eigenvalues summed', fontsize=12)
ax.set_ylabel('Σλᵢ²', fontsize=12)
ax.set_title('Hilbert-Schmidt Norm Test', fontsize=14, fontweight='bold')
ax.legend()
ax.grid(True, alpha=0.3)
ax.text(0.5, 0.95, f'FAILURE: Σλ² = {cumulative_eigenvalue_norm_squared[-1]:.2e} >> 3',
        transform=ax.transAxes, ha='center', va='top',
        bbox=dict(boxstyle='round', facecolor='red', alpha=0.8, edgecolor='darkred', linewidth=2),
        fontsize=11, fontweight='bold', color='white')

plt.tight_layout()
plt.savefig('/home/xluxx/pablo_context/Principia_Fractalis_v3.4_COMPLETE_PROOFS_2025-11-09/eigenvalue_diagnostic.png',
            dpi=300, bbox_inches='tight')
print("Diagnostic plot saved: eigenvalue_diagnostic.png")

# Summary statistics
print("\n" + "="*70)
print("EIGENVALUE DIAGNOSTIC SUMMARY")
print("="*70)
print(f"\nN=10:")
print(f"  Max |λ|: {max(np.abs(eigenvalues_N10)):.2e}")
print(f"  Expected max: {expected_max:.2f}")
print(f"  Ratio: {max(np.abs(eigenvalues_N10)) / expected_max:.2e}")
print(f"\nN=20:")
print(f"  Max |λ|: {max(np.abs(eigenvalues_N20)):.2e}")
print(f"  Expected max: {expected_max:.2f}")
print(f"  Ratio: {max(np.abs(eigenvalues_N20)) / expected_max:.2e}")
print(f"\nHilbert-Schmidt norm test:")
print(f"  Σλᵢ² = {cumulative_eigenvalue_norm_squared[-1]:.2e}")
print(f"  Should be ≤ 3")
print(f"  Violation factor: {cumulative_eigenvalue_norm_squared[-1] / 3:.2e}")
print(f"\nTrace class analysis:")
print(f"  Growth exponent α = {alpha:.4f}")
print(f"  Trace class: {'YES' if alpha < 1 else 'NO'}")
print(f"  (But eigenvalues are invalid anyway)")
print("\n" + "="*70)
print("CONCLUSION: Operator implementation is fundamentally broken")
print("="*70)
