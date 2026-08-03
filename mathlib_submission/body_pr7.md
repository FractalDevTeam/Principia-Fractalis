A matrix `A : ℕ → ℕ → ℂ` with square-summable entries induces a bounded operator on `lp (fun _ : ℕ => ℂ) 2` with operator norm at most the Hilbert–Schmidt norm — and that operator is compact.

Contents:
- `HSSummable A`, `hsOperator hA : lp _ 2 →L[ℂ] lp _ 2`, `hsOperator_norm_le`;
- `isCompactOperator_of_mem_finiteDimensional`: a continuous linear map whose range lies in a finite-dimensional submodule is a compact operator (the finite-rank ⟹ compact bridge; `IsCompactOperator` currently has no finite-rank API and no nontrivial examples);
- `isCompactOperator_hsOperator` via finite-rank row truncations converging in operator norm;
- the double-geometric decay criterion `‖A m n‖ ≤ C·r^m·ρ^n` with the explicit bound `‖·‖_HS ≤ C/√((1−r²)(1−ρ²))`.

The index type is fixed to ℕ (truncations via `Finset.range`); generalising the index is routine and can follow in a later PR. All declarations report axioms `[propext, Classical.choice, Quot.sound]`.

Parts of this contribution were developed with AI assistance (Claude). All statements are machine-checked by the Lean kernel.
