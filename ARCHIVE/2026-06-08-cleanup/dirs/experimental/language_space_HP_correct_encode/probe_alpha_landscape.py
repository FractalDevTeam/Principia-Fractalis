"""
Follow-up probe: fine α-scan around √2 and special points, looking for
any α at which (a) H_P becomes Hermitian, or (b) a real eigenvalue
crosses π/(10α).
"""
import numpy as np
from test_HP_prime_encoding import (
    enumerate_strings, build_HP_matrix, hadamard_eigenvalues,
    coeff, D3_encode, encode_string
)

N = 2
strings = enumerate_strings(N)
M = len(strings)
print(f"Probe with N={N}, M={M} strings, dim=2^M={2**M}")
print(f"D_3 values: {[D3_encode(x) for x in strings]}")
print(f"Lengths    : {[len(x) for x in strings]}")
print()

# ---- (a) Hermiticity scan over α ----
print("=" * 78)
print("Fine α-scan for HERMITICITY of H_P (||H - H†||_F / ||H||_F)")
print("=" * 78)
alphas = np.linspace(0.0, 4.0, 161)  # step 0.025
results = []
for a in alphas:
    H = build_HP_matrix(strings, a)
    n = np.linalg.norm(H - H.conj().T, 'fro')
    d = np.linalg.norm(H, 'fro')
    results.append((a, n / d if d > 0 else 0.0))
# Print only α where ratio is < 1e-6 (Hermitian)
print("\nα values where ||H - H†|| / ||H|| < 1e-6 :")
hermitian_alphas = [(a, r) for (a, r) in results if r < 1e-6]
for a, r in hermitian_alphas:
    print(f"  α = {a:.6f}   ratio = {r:.3e}")

# Theoretical observation: H is Hermitian iff for each x, c_x = c_x*
# (since F_x is self-inverse, hence Hermitian, so the operator c_x F_x is
# Hermitian iff c_x is real). c_x = (1/2^|x|) e^{iπα D_3(encode(x))} is real
# iff πα · D_3 ≡ 0 mod π, i.e. α · D_3 ∈ ℤ for every x. With our D_3 values
# {1,3,5,3,5,5,5}, this requires α to be such that α·d ∈ ℤ for all d in that
# set. gcd: α must be a rational p/q with q | gcd_set. Since D_3 values
# include 1 directly, α must be a positive integer.
# So Hermitian exactly at α ∈ ℤ. Predicted: 1, 2, 3 ⇒ Hermitian. √2, e, π ⇒ not.
print("\nTheoretical: c_x real ⇔ α · D_3(x) ∈ ℤ for ALL x. With D_3 set containing 1,")
print("α must be a positive integer. Predicted Hermitian α: {1, 2, 3, 4, ...}.")
print("All observed Hermitian α in scan:")
for a, r in results:
    if r < 1e-6:
        print(f"  α = {a:.6f}  (predicted integer? {abs(a - round(a)) < 1e-9})")

# ---- (b) Real-eigenvalue tracking ----
# Even though H_P is non-Hermitian off integer α, it may still have some real
# eigenvalues. Search those eigenvalues that have |Im(λ)| < 1e-8 and see if
# Re(λ) ever crosses π/(10α).
print()
print("=" * 78)
print("Real eigenvalues (|Im| < 1e-8) and their Re vs π/(10α)")
print("=" * 78)
alphas_fine = [np.sqrt(2.0), 1.0, 1.5, (1 + np.sqrt(5))/2 + 0.25, 2.0, 3.0, np.e, np.pi]
labels      = ['√2', '1', '3/2', 'φ+1/4', '2', '3', 'e', 'π']
for label, a in zip(labels, alphas_fine):
    eigs = hadamard_eigenvalues(strings, a)
    real_mask = np.abs(eigs.imag) < 1e-8
    real_eigs = np.unique(np.round(eigs[real_mask].real, 10))
    tgt = np.pi / (10.0 * a)
    print(f"\nα = {label} ({a:.6f}), target π/(10α)={tgt:.6f}")
    print(f"  # real eigenvalues: {real_mask.sum()} out of {len(eigs)}")
    print(f"  unique real eigenvalues: {real_eigs}")
    if len(real_eigs) > 0:
        d = np.abs(real_eigs - tgt)
        i = np.argmin(d)
        print(f"  closest real eigenvalue to target: {real_eigs[i]:.8f}  (dist {d[i]:.4e})")
