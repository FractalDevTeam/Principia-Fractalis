# C2 STATEMENT CARDS — Noether–Skolem for `M_n(ℂ) →⋆ₐ[ℂ] M_{kn}(ℂ)`

**Purpose.** Per `FLT_LESSONS_FOR_PF_2026-09-08.md` §1, decompose C2 (`SubstrateRigidity.lean` §5, `unital_star_hom_inner_unique`) into immutable statement-cards. Each card: Lean signature, English intent, proof sketch, mathlib primitives, dependencies, read-back prompt.

**Discipline** (same as C1): the Lean signature is what a prover-agent MUST type-check against; multiple proofs / disproofs first-class; a card lands only when `#print axioms` returns exactly `[propext, Classical.choice, Quot.sound]`.

**Scope.** C2 = any two unital *-homs `φ, ψ : M_n(ℂ) →⋆ₐ[ℂ] M_{kn}(ℂ)` are conjugate by a unitary `U ∈ M_{kn}(ℂ)`. Consumed by C4 (Elliott back-and-forth) to reduce arbitrary inclusions to the canonical C1 shape.

---

## Strategy: matrix-unit / orthonormal-basis (Path A)

Candidates considered: **(A) matrix-units** — `φ(e_{ij})` form a system of matrix units in `M_{kn}(ℂ)`; align ONBs of `range(E^φ_{00})` and `range(E^ψ_{00})` via a unitary. **(B) bimodule** — `M_n(ℂ)`-module structures on `ℂ^{kn}` via `φ`, `ψ` are both isotypic of the same multiplicity. **(C) Wedderburn** — extract from `IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end`.

**Path A wins.** Mathlib carries full `Matrix.single` calculus in `Data/Matrix/Basis.lean` and change-of-ONB unitarity via `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` (`Analysis/InnerProductSpace/PiL2.lean` L963). Path B needs a star-preserving lift `LinearIsometryEquiv → unitary` mathlib doesn't bundle. Path C returns `AlgEquiv`, not `StarAlgEquiv`. Path A is explicit and mirrors C1's style.

**Mathlib primitives (verified 2026-09-09 vs `mathlib4-pr` HEAD):** `Matrix.single`, `single_mul_single_same`, `single_mul_single_of_ne`, `diagonal_single`, `diagonal_one`, `Matrix.unitaryGroup`, `mem_unitaryGroup_iff`/`_iff'`, `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`, `stdOrthonormalBasis`, `NonUnitalStarAlgHom.isometry`, `finProdFinEquiv`.

**Presence to verify in v3 read-back:** `Matrix.star_single`/`conjTranspose_single`; `OrthonormalBasis` constructor for `range` of a self-adjoint idempotent given a `finrank` witness.

---

## CARD C2.1 — `phiMatrixUnit`

```lean
noncomputable def phiMatrixUnit
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k*n)) (Fin (k*n)) ℂ) (i j : Fin n) :
    Matrix (Fin (k*n)) (Fin (k*n)) ℂ := φ (Matrix.single i j 1)
```

`E^φ_{ij} := φ(e_{ij})`. **Sketch:** definition. **Prim:** `Matrix.single`. **Deps:** none.

---

## CARD C2.2 — `phiMatrixUnit_mul_same`

```lean
lemma phiMatrixUnit_mul_same (φ …) (i j l : Fin n) :
    phiMatrixUnit φ i j * phiMatrixUnit φ j l = phiMatrixUnit φ i l
```

`E^φ_{ij} · E^φ_{jl} = E^φ_{il}`. **Sketch:** `rw [← map_mul, single_mul_single_same, one_mul]`. **Prim:** `single_mul_single_same`, `map_mul`. **Deps:** C2.1.

---

## CARD C2.3 — `phiMatrixUnit_mul_of_ne`

```lean
lemma phiMatrixUnit_mul_of_ne (φ …) (i j k' l : Fin n) (h : j ≠ k') :
    phiMatrixUnit φ i j * phiMatrixUnit φ k' l = 0
```

Orthogonality. **Sketch:** `rw [← map_mul, single_mul_single_of_ne h, map_zero]`. **Prim:** `single_mul_single_of_ne`, `map_mul`, `map_zero`. **Deps:** C2.1.

---

## CARD C2.4 — `phiMatrixUnit_star`

```lean
lemma phiMatrixUnit_star (φ …) (i j : Fin n) :
    star (phiMatrixUnit φ i j) = phiMatrixUnit φ j i
```

`(E^φ_{ij})* = E^φ_{ji}`. **Sketch:** `map_star` + `star (single i j 1) = single j i 1` (entry-wise `ext`, or `Matrix.star_single` if present). **Prim:** `map_star`, `Matrix.star_apply`. **Deps:** C2.1. **Verify:** `Matrix.star_single` presence in mathlib HEAD; if absent, 4-line `ext` fallback.

---

## CARD C2.5 — `phiMatrixUnit_sum_diag`

```lean
lemma phiMatrixUnit_sum_diag (φ …) : (∑ i : Fin n, phiMatrixUnit φ i i) = 1
```

`Σᵢ E^φ_{ii} = 1_{kn}` (completeness). **Sketch:** `map_sum`; `∑ single i i 1 = 1` via `diagonal_single` + `diagonal_one`; `map_one`. **Prim:** `diagonal_single`, `diagonal_one`, `map_sum`, `map_one`. **Deps:** C2.1.

---

## CARD C2.6 — `phi_e00_isProjection`

```lean
lemma phi_e00_isProjection (φ …) [NeZero n] :
    letI p := phiMatrixUnit φ ⟨0, Nat.pos_of_neZero n⟩ ⟨0, Nat.pos_of_neZero n⟩
    p * p = p ∧ star p = p
```

Self-adjoint idempotent. **Sketch:** idempotence from C2.2 (`i=j=l=0`); self-adjoint from C2.4 (`i=j=0`). **Deps:** C2.2, C2.4.

---

## CARD C2.7 — `phi_e00_range_finrank`

```lean
lemma phi_e00_range_finrank (φ …) [NeZero n] [NeZero k] :
    Module.finrank ℂ
      (LinearMap.range (Matrix.toEuclideanLin
        (phiMatrixUnit φ ⟨0,_⟩ ⟨0,_⟩))) = k
```

`range(E^φ_{00})` has dim `k`. **Sketch:** the `n` projections `E^φ_{ii}` are pairwise orthogonal (C2.3 with `l=i`) and sum to `1` (C2.5); pairwise unitarily conjugate via partial isometries `E^φ_{i0}` (`E^φ_{i0} · E^φ_{00} · E^φ_{0i} = E^φ_{ii}` from C2.2 + C2.4). Equal rank `d` with `n·d = kn`, so `d = k`. **Prim:** `Submodule.finrank_iSup_of_isInternal`, `OrthogonalFamily.isInternal_iff`. **Deps:** C2.2, C2.3, C2.4, C2.5, C2.6. **Split-fallback:** if mathlib lacks packaged lemmas, split into C2.7a (orthogonality), C2.7b (partial-isometry conjugation), C2.7c (dim arithmetic).

---

## CARD C2.8 — `phiONB`

```lean
noncomputable def phiONB (φ …) [NeZero n] [NeZero k] :
    OrthonormalBasis (Fin n × Fin k) ℂ (EuclideanSpace ℂ (Fin (k*n)))
```

ONB of `ℂ^{kn}` indexed by `Fin n × Fin k`: pick ONB `{v_a}` of `range(E^φ_{00})` (dim `k` by C2.7); `(i,a)`-th vector is `E^φ_{i0} v_a`. **Sketch:** `stdOrthonormalBasis` on the `k`-dim subspace; family orthonormality via `⟨E^φ_{i0} v_a, E^φ_{j0} v_b⟩ = ⟨E^φ_{0j} E^φ_{i0} v_a, v_b⟩` (C2.4), reducing by C2.3 (i≠j → 0) and C2.2 (i=j → `δ_{ab}`); completeness by dim count `n·k = kn`. **Prim:** `stdOrthonormalBasis`, `OrthonormalBasis.mk`, `Submodule.finrank_eq`. **Deps:** C2.2, C2.3, C2.4, C2.7.

---

## CARD C2.9 — `unitaryOfONBpair`

```lean
noncomputable def unitaryOfONBpair (n k : ℕ) [NeZero n] [NeZero k]
    (bφ bψ : OrthonormalBasis (Fin n × Fin k) ℂ
                (EuclideanSpace ℂ (Fin (k*n)))) :
    Matrix (Fin (k*n)) (Fin (k*n)) ℂ :=
  bψ.toBasis.toMatrix bφ.toBasis
```

Change-of-ONB matrix `bφ → bψ`. **Sketch:** `OrthonormalBasis.toBasis` + `Basis.toMatrix`. **Deps:** none. **Read-back:** *"Chirality — is `toMatrix` in the right direction for `U·ψ(x)·U* = φ(x)`?"*

---

## CARD C2.10 — `unitaryOfONBpair_mem_unitaryGroup`

```lean
lemma unitaryOfONBpair_mem_unitaryGroup (n k …) (bφ bψ …) :
    letI U := unitaryOfONBpair n k bφ bψ
    U * star U = 1 ∧ star U * U = 1
```

**Sketch:** direct via `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` (PiL2.lean L963), unfolded through `mem_unitaryGroup_iff`/`_iff'`; reindex `Fin (k*n) ↔ Fin n × Fin k` via `finProdFinEquiv`. **Prim:** `toMatrix_orthonormalBasis_mem_unitary`, `mem_unitaryGroup_iff`, `finProdFinEquiv`. **Deps:** C2.9.

---

## CARD C2.11 — `unitary_conjugates_phi_psi`

```lean
lemma unitary_conjugates_phi_psi (φ ψ …) [NeZero n] [NeZero k] :
    letI U := unitaryOfONBpair n k (phiONB φ) (phiONB ψ)
    ∀ x, φ x = U * ψ x * (star U)
```

**Sketch:** both sides `ℂ`-linear; check on `single i j 1`. On that basis: `E^φ_{ij}` sends `phiONB φ (j,a) ↦ phiONB φ (i,a)`, kills others (C2.2/C2.3 through C2.8). Same for `ψ`. `U` sends `phiONB ψ (i,a) ↦ phiONB φ (i,a)` (C2.9). Hence `U·E^ψ_{ij}·U*` and `E^φ_{ij}` agree on `phiONB φ`. **Prim:** `Matrix.matrix_eq_sum_single`, `OrthonormalBasis.ext`, `Matrix.toLin'`. **Deps:** C2.2, C2.3, C2.4, C2.8, C2.9.

---

## CARD C2.12 — `unital_star_hom_inner_unique` (MAIN)

```lean
lemma unital_star_hom_inner_unique (φ ψ …) [NeZero n] [NeZero k] :
    ∃ U : Matrix (Fin (k*n)) (Fin (k*n)) ℂ,
      U * star U = 1 ∧ star U * U = 1 ∧ ∀ x, φ x = U * ψ x * (star U) :=
  ⟨unitaryOfONBpair n k (phiONB φ) (phiONB ψ),
   (unitaryOfONBpair_mem_unitaryGroup n k _ _).1,
   (unitaryOfONBpair_mem_unitaryGroup n k _ _).2,
   unitary_conjugates_phi_psi φ ψ⟩
```

Target theorem — term-mode assembly. **Deps:** C2.9, C2.10, C2.11. **Discipline:** SubstrateRigidity signature has `[NeZero k]` only. If `[NeZero n]` is not added there, C2.12 must dispatch `n = 0` trivially (`U = 1`; `M_0(ℂ) = 0`, so `φ x = 0 = ψ x`).

---

## Aggregate C2 status when all 12 cards land

- `unital_star_hom_inner_unique` proved (C2.12); explicit witness `U = unitaryOfONBpair n k (phiONB φ) (phiONB ψ)`.
- `#print axioms unital_star_hom_inner_unique` = `[propext, Classical.choice, Quot.sound]`.
- C2.1–C2.6: 3–8 lines each. C2.7 deepest (dimension count; may split). C2.8–C2.11: assembly. C2.12: term-mode wrapper.
- Aggregate cost ~1.5–2.5 h at Vinogradov cadence; C2.7 tallest single card (~30–40 min).

## Mathlib gap identified

Not in mathlib (verified 2026-09-09); build as `PF/SubstrateRigidity/C2Helpers.lean` or upstream PRs:

1. **`Matrix.star_single`** — `star (single i j c) = single j i (star c)`. 4-line `ext`. PR to `Data/Matrix/Basis.lean`.
2. **`IsSelfAdjoint.range_orthonormalBasis`** — `OrthonormalBasis (Fin n) ℂ (range p.toLin)` from self-adjoint idempotent `p` + `finrank = n` witness. ~15 lines over `stdOrthonormalBasis`.
3. **Rank-additivity for pairwise-orthogonal projections summing to `1`** — `Σᵢ finrank (range pᵢ) = finrank V`. Via `Submodule.finrank_iSup_of_isInternal` + `OrthogonalFamily.isInternal_iff`. ~10 lines.
4. **Partial-isometry conjugation preserves range dim** — `V*V = p`, `VV* = q` ⇒ `finrank (range p) = finrank (range q)`. ~8 lines via `LinearMap.equivOfRange`.

Each is a self-contained PR candidate; file to `MATHLIB_UPSTREAM_QUEUE_2026-09-10.md` once C2 lands.

## Sequencing

C2.1 → {C2.2, C2.3, C2.4, C2.5} (fan 4-wide) → C2.6 → C2.7 (longest) → C2.8 → C2.9 → C2.10 → C2.11 → C2.12. Priorities: C2.1 solo; fan C2.2/3/4/5; C2.7 gets deepest agent; serialize the tail.

---

*Statement-cards drafted 2026-09-10. Awaiting v3 read-back on enclosing `SubstrateRigidity.lean` scratch and on the four mathlib-gap items above before landing as prover-farmable jobs. Public HEAD `96c71da7`. NO PUSH TO MASTER. Branch `r331b-provenance`.*
