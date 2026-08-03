For a symmetric bi-additive form `B : G → G → ℝ` on an abelian group and points `P : Fin n → G`, a nonzero Gram determinant `(gram B P).det ≠ 0` forces the `P i` to be `ℤ`-linearly independent, hence `(n : Cardinal) ≤ Module.rank ℤ G`.

Motivation: this is the working criterion behind Néron–Tate regulator arguments (rank lower bounds for Mordell–Weil groups from certified numerics). mathlib's nearest result is the 2×2 pair case `LinearIndependent.linear_combination_pair_of_det_ne_zero`; nothing exists at this generality, and `Gram` currently appears only in inner-product-space files.

All declarations report axioms `[propext, Classical.choice, Quot.sound]`.

Parts of this contribution were developed with AI assistance (Claude). All statements are machine-checked by the Lean kernel.
