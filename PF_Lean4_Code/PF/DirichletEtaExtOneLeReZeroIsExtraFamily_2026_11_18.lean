import PF.DirichletEtaExtZerosCharacterization_2026_11_18
import PF.DirichletEtaExtraFamilyExhaustive_2026_11_18
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# On `Re s ≥ 1`, the only zeros of `dirichletEtaExt` are the extra family

Sharpens the previous `dirichletEtaExt_ne_zero_of_one_lt_re` to the
*closed* half-plane `Re s ≥ 1`, and simultaneously pins the location of
zeros there: they are precisely the extra-zero family
`extraFamily(ℤ) = { 1 + 2π i k / log 2 : k ∈ ℤ }`.

```
dirichletEtaExt_eq_zero_iff_mem_extraFamily_of_one_le_re :
    1 ≤ s.re →
      (dirichletEtaExt s = 0 ↔ ∃ k : ℤ, s = extraFamily k)
```

Proof: the full iff characterization of today gives
`dirichletEtaExt s = 0 ↔ 2^(1-s) = 1 ∨ ζ s = 0`. Mathlib's
`riemannZeta_ne_zero_of_one_le_re` kills the second disjunct on the
closed right half-plane. Then
`two_cpow_eq_one_iff_mem_extraFamily` converts the first disjunct.

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.

This is the strongest localisation of η-zeros currently in the corpus:
in `Re s ≥ 1`, every zero of `dirichletEtaExt` is "trivial" — a member
of the explicit countably infinite family contributed by the factor
`(1 - 2^(1-s))`. Nontrivial zeros therefore live in `Re s < 1`.
-/

namespace PrincipiaTractalis.DirichletEtaExtOneLeReZeroIsExtraFamily_2026_11_18

open PrincipiaTractalis.DirichletEtaExtension (dirichletEtaExt)
open PrincipiaTractalis.DirichletEtaExtZerosCharacterization_2026_11_18
  (dirichletEtaExt_eq_zero_iff)
open PrincipiaTractalis.DirichletEtaExtraFamilyStructure_2026_11_18
  (extraFamily)
open PrincipiaTractalis.DirichletEtaExtraFamilyExhaustive_2026_11_18
  (two_cpow_eq_one_iff_mem_extraFamily)

/-- **Localisation of η-zeros on the closed right half-plane.**
    On `Re s ≥ 1`, a zero of `dirichletEtaExt` must be a member of the
    extra-zero family `1 + 2π i k / Complex.log 2`, and vice versa. -/
theorem dirichletEtaExt_eq_zero_iff_mem_extraFamily_of_one_le_re
    {s : ℂ} (hs : 1 ≤ s.re) :
    dirichletEtaExt s = 0 ↔ ∃ k : ℤ, s = extraFamily k := by
  rw [dirichletEtaExt_eq_zero_iff, two_cpow_eq_one_iff_mem_extraFamily]
  constructor
  · rintro (hex | hzeta)
    · exact hex
    · exact absurd hzeta (riemannZeta_ne_zero_of_one_le_re hs)
  · intro hex
    exact Or.inl hex

/-- **Nontrivial η-zeros live in `Re s < 1`.** Contrapositive form of
    the main theorem: if `s` is a zero of `dirichletEtaExt` and not in
    the extra family, then `Re s < 1`. -/
theorem lt_one_of_dirichletEtaExt_zero_of_not_extra
    {s : ℂ} (hzero : dirichletEtaExt s = 0)
    (hnot : ∀ k : ℤ, s ≠ extraFamily k) : s.re < 1 := by
  by_contra h_ge
  push_neg at h_ge
  rcases (dirichletEtaExt_eq_zero_iff_mem_extraFamily_of_one_le_re h_ge).mp hzero
    with ⟨k, hk⟩
  exact hnot k hk

#print axioms dirichletEtaExt_eq_zero_iff_mem_extraFamily_of_one_le_re
#print axioms lt_one_of_dirichletEtaExt_zero_of_not_extra

end PrincipiaTractalis.DirichletEtaExtOneLeReZeroIsExtraFamily_2026_11_18
