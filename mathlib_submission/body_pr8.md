The Cauchy coefficient matrix of a weighted composition system — finitely many branches `φ k` mapping the circle `|z−c| = R₁` into a closed ball `|z−c| ≤ τ` with `τ < R < R₁`, weights `w k` bounded on that circle — satisfies the double-geometric bound `‖A m n‖ ≤ (K·W)·(R/R₁)^m·(τ/R)^n`, hence induces a compact operator on ℓ² by the Hilbert–Schmidt criterion (#PR7).

No analyticity is assumed anywhere: `norm_cauchyPowerSeries_le` is a pure integral estimate, so continuity on the circle suffices. This is the geometry of Ruelle/Mayer transfer operators for continued-fraction systems (Mayer 1991, Lewis–Zagier 2001), and — to our knowledge — the first formalized compactness result for that operator class in any proof assistant.

Depends on the Hilbert–Schmidt base PR; if that is unmerged this branch carries both files. All declarations report axioms `[propext, Classical.choice, Quot.sound]`.

Parts of this contribution were developed with AI assistance (Claude). All statements are machine-checked by the Lean kernel.
