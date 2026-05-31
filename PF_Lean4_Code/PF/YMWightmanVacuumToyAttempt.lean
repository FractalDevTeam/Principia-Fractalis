/-
# YM Wightman Vacuum + 1-Particle Mass-Gap TOY Attempt — Wave 53D

★ DISPATCHED 2026-05-31 — direct extension of Wave 52D's rank-K PSD
  Gram-matrix toy (`YMReflectionPositivity3plus1DRankKAttempt.lean`)
  to a finite-dimensional vacuum-plus-one-particle Wightman-style
  toy carrying the simplest possible mass-gap signature:

      `⟨0|H|0⟩ = 0  <  m  ≤  ⟨n|H|n⟩`   for every one-particle state n.

## Strategic context

Wave 48B–52D realised the algebraic CORE of OS reflection positivity
(rank-1 Gram-matrix PSD, 1+1D / 2+1D / 3+1D / rank-2 / rank-3 / rank-K)
inside mathlib. Wave 47B's honest scope analysis isolated the four
genuine Clay-grade mathlib barriers (Bochner–Minlos on nuclear spaces,
`S(ℝ⁴)` reflection, Wightman reconstruction, mass-gap propagation).

This file (Wave 53D) takes the FIRST step from "OS positivity ladder"
toward "Wightman reconstruction + mass-gap propagation": we build the
smallest possible finite-dimensional Hilbert space carrying a
vacuum-vs-one-particle separation in the spectrum of a `H`-style
Hamiltonian, together with a ladder creation operator `aStar` that
moves between sectors.

The model is honestly a TOY: the carrier is finite-dimensional, the
Hamiltonian is diagonal, and the "one-particle states" are
canonical-basis vectors orthogonal to the vacuum. No `S(ℝ⁴)`, no
Wightman 2-point function in spacetime, no continuum lift. What it
DOES is encode the *structural shape* of the Clay mass-gap statement
   `Spec(H) ⊂ {0} ∪ [Δ, ∞)`   for Δ > 0
at the toy level: `H` is non-negative, its zero-eigenspace contains
the vacuum, and every one-particle basis state has eigenvalue ≥ m.

## Construction

Fix `N : ℕ` (number of one-particle modes) and `m : ℝ` with `0 < m`.

* **Hilbert space**: `Hilb N := EuclideanSpace ℝ (Fin (N + 1))`.

* **Vacuum**: `vac N : Hilb N := PiLp.basisFun ... 0` — the 0-th
  canonical basis vector.

* **One-particle states**: for `i : Fin N`, `oneParticle N i : Hilb N`
  is the basis vector at index `i.succ : Fin (N+1)`.

* **Hamiltonian** (diagonal): `hamFun N m : Fin (N+1) → ℝ` is
  `0` at index `0` and `m` at every other index.

* **Creation operator** `aStar N m : Hilb N → Hilb N` (linear): sends
  the vacuum to the first one-particle state and shifts each
  one-particle state to the next, with the top capped at zero.

* **Mass-gap signature**: `⟨0|H|0⟩ = 0` and `⟨i|H|i⟩ = m` for every
  one-particle index `i`.

## Honest scope

  * Finite-dim toy: `Hilb N = ℝ^{N+1}`, NOT a Fock space on `S(ℝ⁴)`.
  * `H` is by construction diagonal in the chosen basis; we are not
    *deriving* a mass gap from interactions — we are *registering*
    the structural shape `Spec(H) ⊂ {0} ∪ [m, ∞)` at the toy level.
  * The creation operator does NOT satisfy canonical commutation
    relations — it is a clean shift on the basis, sufficient for the
    "vacuum to one-particle" mass-gap signature.
  * The four Clay-grade mathlib barriers from Wave 47B remain open;
    in particular Wightman reconstruction and mass-gap propagation
    are NOT addressed. YM mass gap unchanged.

## Output

Axiom-free; `#print axioms` on
`ym_wightman_vacuum_toy_attempt_capstone` returns only
`[propext, Classical.choice, Quot.sound]`.

Author: Wave 53D extension dispatch, 2026-05-31.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace YMWightmanVacuumToyAttempt

open scoped BigOperators

/-! ## §1 — Finite-dimensional vacuum + N-particle Hilbert space -/

/-- **Toy Wightman Hilbert space**: vacuum ⊕ `N` one-particle states.

    Concretely: `EuclideanSpace ℝ (Fin (N + 1))`, with index `0`
    interpreted as the vacuum and indices `1, …, N` as one-particle
    states. -/
abbrev Hilb (N : ℕ) : Type := EuclideanSpace ℝ (Fin (N + 1))

/-- **Vacuum state** `|0⟩ ∈ Hilb N`: the 0-th canonical basis vector,
    i.e. the function `Fin (N+1) → ℝ` sending `0 ↦ 1` and `k ↦ 0` for
    `k ≠ 0`. We use `Pi.single` to define it explicitly. -/
noncomputable def vac (N : ℕ) : Hilb N :=
  (EuclideanSpace.single (0 : Fin (N + 1)) (1 : ℝ))

/-- **One-particle state** `|i⟩ ∈ Hilb N`: the canonical basis vector
    at index `i.succ : Fin (N+1)`. The `.succ` shifts past the vacuum
    index. -/
noncomputable def oneParticle (N : ℕ) (i : Fin N) : Hilb N :=
  (EuclideanSpace.single (i.succ : Fin (N + 1)) (1 : ℝ))

/-! ## §2 — Diagonal Hamiltonian with mass gap `m` -/

/-- **Hamiltonian diagonal coefficients** `Fin (N+1) → ℝ`:
    `0` at the vacuum index, `m` at every one-particle index. -/
def hamFun (N : ℕ) (m : ℝ) : Fin (N + 1) → ℝ :=
  fun k => if k = 0 then 0 else m

/-- **Hamiltonian** `H : Hilb N → Hilb N`: diagonal in the canonical
    basis, with diagonal entries given by `hamFun N m`. Concretely,
    `(H ψ) k = (hamFun N m k) * ψ k`. -/
noncomputable def ham (N : ℕ) (m : ℝ) (ψ : Hilb N) : Hilb N :=
  fun k => hamFun N m k * ψ k

/-! ## §3 — Creation (ladder) operator -/

/-- **Creation operator** `a* : Hilb N → Hilb N` acting on canonical
    basis index components. For `(ψ : Hilb N)` and index `k`,
    `(a* ψ) k := ψ (k - 1)` if `k ≥ 1`, otherwise `0`. That is, the
    creation operator shifts a basis vector at index `j` to the
    basis vector at index `j + 1`, capped at the top. -/
noncomputable def aStar (N : ℕ) (ψ : Hilb N) : Hilb N :=
  fun k =>
    match (k : Fin (N + 1)) with
    | ⟨0, _⟩ => 0
    | ⟨j + 1, h⟩ => ψ ⟨j, by omega⟩

/-! ## §4 — Vacuum and one-particle inner products

    Inner products on `Hilb N = EuclideanSpace ℝ (Fin (N+1))` of
    canonical basis vectors are handled directly via mathlib's
    `EuclideanSpace.inner_single_left`. -/

/-- `⟨vac|vac⟩ = 1`. -/
theorem inner_vac_vac (N : ℕ) : @inner ℝ _ _ (vac N) (vac N) = 1 := by
  unfold vac
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  simp

/-- `⟨vac|oneParticle i⟩ = 0`. -/
theorem inner_vac_oneParticle (N : ℕ) (i : Fin N) :
    @inner ℝ _ _ (vac N) (oneParticle N i) = 0 := by
  unfold vac oneParticle
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  simp [Fin.succ_ne_zero, eq_comm (a := (0 : Fin (N + 1))) (b := i.succ)]

/-- `⟨oneParticle i|oneParticle i⟩ = 1` for every `i : Fin N`. -/
theorem inner_oneParticle_self (N : ℕ) (i : Fin N) :
    @inner ℝ _ _ (oneParticle N i) (oneParticle N i) = 1 := by
  unfold oneParticle
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  simp

/-! ## §6 — Hamiltonian acting on basis states -/

/-- **`H` annihilates the vacuum**: `H |0⟩ = 0`. -/
theorem ham_vac (N : ℕ) (m : ℝ) : ham N m (vac N) = 0 := by
  funext k
  unfold ham hamFun vac
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; simp [EuclideanSpace.single_apply]
  · simp [hk, EuclideanSpace.single_apply]

/-- **`H` acts as scalar `m` on each one-particle basis state**. -/
theorem ham_oneParticle (N : ℕ) (m : ℝ) (i : Fin N) :
    ham N m (oneParticle N i) = m • (oneParticle N i) := by
  funext k
  unfold ham hamFun oneParticle
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    simp [EuclideanSpace.single_apply, Fin.succ_ne_zero, eq_comm]
  · rcases eq_or_ne k i.succ with hki | hki
    · subst hki
      have : (i.succ : Fin (N + 1)) ≠ 0 := Fin.succ_ne_zero i
      simp [this, EuclideanSpace.single_apply, PiLp.smul_apply,
            smul_eq_mul]
    · simp [hk, hki, EuclideanSpace.single_apply, PiLp.smul_apply,
            smul_eq_mul]

/-! ## §7 — Diagonal matrix elements ⟨ψ|H|ψ⟩ -/

/-- **Vacuum expectation of `H` vanishes**: `⟨vac|H|vac⟩ = 0`. -/
theorem inner_vac_ham_vac (N : ℕ) (m : ℝ) :
    @inner ℝ _ _ (vac N) (ham N m (vac N)) = 0 := by
  rw [ham_vac]
  exact inner_zero_right _

/-- **One-particle expectation of `H` equals `m`**:
    `⟨i|H|i⟩ = m` for every one-particle index `i`. -/
theorem inner_oneParticle_ham_oneParticle (N : ℕ) (m : ℝ) (i : Fin N) :
    @inner ℝ _ _ (oneParticle N i) (ham N m (oneParticle N i)) = m := by
  rw [ham_oneParticle, inner_smul_right, inner_oneParticle_self]
  ring

/-- **Off-diagonal vacuum–one-particle matrix element of `H` vanishes**:
    `⟨vac|H|oneParticle i⟩ = 0`. -/
theorem inner_vac_ham_oneParticle (N : ℕ) (m : ℝ) (i : Fin N) :
    @inner ℝ _ _ (vac N) (ham N m (oneParticle N i)) = 0 := by
  rw [ham_oneParticle, inner_smul_right, inner_vac_oneParticle]
  ring

/-! ## §8 — Creation operator on the vacuum and one-particle states -/

/-- **Creation lifts vacuum into the first one-particle state**:
    when `N ≥ 1`, `a* |vac⟩ = |oneParticle 0⟩`. -/
theorem aStar_vac (N : ℕ) (hN : 0 < N) :
    aStar N (vac N) = oneParticle N ⟨0, hN⟩ := by
  funext k
  unfold aStar vac oneParticle
  rcases k with ⟨k, hk⟩
  match k, hk with
  | 0, _ =>
    simp [EuclideanSpace.single_apply]
  | j + 1, hk =>
    simp only [EuclideanSpace.single_apply]
    by_cases hj : j = 0
    · subst hj
      simp
    · have h1 : (⟨j + 1, hk⟩ : Fin (N + 1)) ≠ (⟨0, hN⟩ : Fin N).succ := by
        intro hcontra
        have : j + 1 = 0 + 1 := by
          have := congrArg (·.val) hcontra
          simpa using this
        omega
      have h2 : (⟨j, by omega⟩ : Fin (N + 1)) ≠ (0 : Fin (N + 1)) := by
        intro hcontra
        have : j = 0 := by
          have := congrArg (·.val) hcontra
          simpa using this
        exact hj this
      simp [h2, hj]

/-! ## §9 — Mass-gap signature theorems -/

/-- **★ MASS-GAP SIGNATURE (vacuum side) ★**: the vacuum sits at the
    bottom of the spectrum, `⟨vac|H|vac⟩ = 0`. -/
theorem mass_gap_vacuum_side (N : ℕ) (m : ℝ) :
    @inner ℝ _ _ (vac N) (ham N m (vac N)) = 0 :=
  inner_vac_ham_vac N m

/-- **★ MASS-GAP SIGNATURE (one-particle side) ★**: every one-particle
    state has expectation value `m` for `H`. -/
theorem mass_gap_one_particle_side (N : ℕ) (m : ℝ) (i : Fin N) :
    @inner ℝ _ _ (oneParticle N i) (ham N m (oneParticle N i)) = m :=
  inner_oneParticle_ham_oneParticle N m i

/-- **★ STRICT MASS-GAP SIGNATURE ★**: when `m > 0`, the vacuum
    expectation is STRICTLY less than every one-particle expectation,
    with separation EXACTLY `m`. This is the toy analogue of the
    Clay statement `Spec(H) ⊂ {0} ∪ [m, ∞)`. -/
theorem mass_gap_strict (N : ℕ) (m : ℝ) (hm : 0 < m) (i : Fin N) :
    @inner ℝ _ _ (vac N) (ham N m (vac N))
      < @inner ℝ _ _ (oneParticle N i) (ham N m (oneParticle N i)) := by
  rw [mass_gap_vacuum_side, mass_gap_one_particle_side]
  exact hm

/-- **★ MASS-GAP SIGNATURE ⟨0|H|n⟩ ≥ m·n ★**: a sharpened toy form
    of the Clay shape "n-particle expectation ≥ m·n". Here, on a
    one-particle state, the expectation equals exactly `m = m · 1`,
    so the toy realises the n = 1 case of the inequality. -/
theorem mass_gap_inequality_one_particle (N : ℕ) (m : ℝ) (_hm : 0 ≤ m)
    (i : Fin N) :
    m * (1 : ℝ) ≤
      @inner ℝ _ _ (oneParticle N i) (ham N m (oneParticle N i)) := by
  rw [mass_gap_one_particle_side]
  linarith

/-! ## §10 — Hamiltonian is non-negative on every basis state -/

/-- **Hamiltonian non-negative on the vacuum**. -/
theorem ham_nonneg_on_vac (N : ℕ) (m : ℝ) :
    0 ≤ @inner ℝ _ _ (vac N) (ham N m (vac N)) := by
  rw [mass_gap_vacuum_side]

/-- **Hamiltonian non-negative on every one-particle state**, provided
    `m ≥ 0`. -/
theorem ham_nonneg_on_oneParticle (N : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (i : Fin N) :
    0 ≤ @inner ℝ _ _ (oneParticle N i) (ham N m (oneParticle N i)) := by
  rw [mass_gap_one_particle_side]
  exact hm

/-! ## §11 — Capstone -/

/-- ★★★ **CAPSTONE: WIGHTMAN VACUUM + 1-PARTICLE MASS-GAP TOY** ★★★
    (Wave 53D extension, 2026-05-31)

    Direct extension of Wave 52D's rank-K PSD Gram-matrix OS-RP toy
    to a finite-dimensional vacuum-plus-one-particle Wightman-style
    Hilbert space `Hilb N := EuclideanSpace ℝ (Fin (N + 1))`, a
    diagonal Hamiltonian `H : Hilb N → Hilb N` with vacuum at 0 and
    all one-particle states at energy `m > 0`, and a ladder creation
    operator `a* : Hilb N → Hilb N`. Axiom-free, build-clean.

    Six structural clauses:

    (1) **Vacuum normalisation**: `⟨vac|vac⟩ = 1`.

    (2) **Vacuum / one-particle orthogonality**:
        `⟨vac|oneParticle i⟩ = 0` for every `i : Fin N`.

    (3) **Vacuum mass-gap side**: `⟨vac|H|vac⟩ = 0`.

    (4) **One-particle mass-gap side**:
        `⟨oneParticle i|H|oneParticle i⟩ = m` for every `i`.

    (5) **Strict mass-gap signature**: for `m > 0`,
        `⟨vac|H|vac⟩ < ⟨oneParticle i|H|oneParticle i⟩`.

    (6) **Mass-gap inequality (n = 1 case of the Clay shape
        `⟨n|H|n⟩ ≥ m · n`)**: for `m ≥ 0` and any one-particle
        index, `m * 1 ≤ ⟨oneParticle i|H|oneParticle i⟩`.

    **Honest scope** (mandatory non-overclaim): this is a finite-dim
    toy. `Hilb N = ℝ^{N+1}` is NOT a Fock space on `S(ℝ⁴)`; `H` is
    diagonal in the chosen basis (no interactions, no kinetic term);
    `a*` is a basis shift, not a true creation operator satisfying
    canonical commutation relations. The construction REGISTERS the
    structural shape `Spec(H) ⊂ {0} ∪ [m, ∞)` at the toy level but
    does NOT derive a mass gap from dynamics. The four Clay-grade
    mathlib barriers from Wave 47B (Bochner–Minlos on nuclear spaces,
    `S(ℝ⁴)` reflection structure, Wightman reconstruction, mass-gap
    propagation) remain open. YM mass gap unchanged.

    **What this extension demonstrably ADDS to Wave 52D**: Waves
    48B–52D realised the OS-RP positivity ladder (rank-1, …, rank-K
    Gram-matrix PSD); this file is the FIRST step from that ladder
    toward the Wightman/mass-gap side of the Clay statement. It
    introduces (at the toy level) the carrier `Hilb N`, the
    Hamiltonian `H`, the creation operator `a*`, and the structural
    shape `⟨0|H|0⟩ = 0 < m ≤ ⟨n|H|n⟩` for one-particle states.

    Axiom-free; `#print axioms` returns only
    `[propext, Classical.choice, Quot.sound]`. -/
theorem ym_wightman_vacuum_toy_attempt_capstone :
    -- (1) Vacuum normalisation.
    (∀ N : ℕ, @inner ℝ _ _ (vac N) (vac N) = 1) ∧
    -- (2) Vacuum / one-particle orthogonality.
    (∀ N : ℕ, ∀ i : Fin N, @inner ℝ _ _ (vac N) (oneParticle N i) = 0) ∧
    -- (3) Vacuum mass-gap side: ⟨vac|H|vac⟩ = 0.
    (∀ N : ℕ, ∀ m : ℝ,
        @inner ℝ _ _ (vac N) (ham N m (vac N)) = 0) ∧
    -- (4) One-particle mass-gap side: ⟨i|H|i⟩ = m.
    (∀ N : ℕ, ∀ m : ℝ, ∀ i : Fin N,
        @inner ℝ _ _ (oneParticle N i) (ham N m (oneParticle N i)) = m) ∧
    -- (5) ★ Strict mass-gap signature ★.
    (∀ N : ℕ, ∀ m : ℝ, ∀ _ : 0 < m, ∀ i : Fin N,
        @inner ℝ _ _ (vac N) (ham N m (vac N))
          < @inner ℝ _ _ (oneParticle N i) (ham N m (oneParticle N i))) ∧
    -- (6) ★ Mass-gap inequality (n=1 case of ⟨n|H|n⟩ ≥ m·n) ★.
    (∀ N : ℕ, ∀ m : ℝ, ∀ _ : 0 ≤ m, ∀ i : Fin N,
        m * (1 : ℝ) ≤
          @inner ℝ _ _ (oneParticle N i) (ham N m (oneParticle N i))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N; exact inner_vac_vac N
  · intro N i; exact inner_vac_oneParticle N i
  · intro N m; exact mass_gap_vacuum_side N m
  · intro N m i; exact mass_gap_one_particle_side N m i
  · intro N m hm i; exact mass_gap_strict N m hm i
  · intro N m hm i; exact mass_gap_inequality_one_particle N m hm i

/-- **Structural-reading remark on the Wightman-vacuum toy capstone**.

    The Wightman vacuum + one-particle toy formalises the SIMPLEST
    finite-dim shape consistent with the Clay mass-gap statement
    `Spec(H) ⊂ {0} ∪ [Δ, ∞)`. Three structural observations:

      (i) The toy is the first PF-stack member to carry a NAMED
          `vac` state, a NAMED `oneParticle i` state family, a
          diagonal Hamiltonian with the right spectral shape, and a
          ladder operator `aStar`. Waves 48B–52D supplied OS-RP
          positivity; this file supplies vacuum / one-particle
          spectral separation.

      (ii) The mass-gap inequality `m * 1 ≤ ⟨1|H|1⟩` is the n = 1
           specialisation of the genuine Clay shape `⟨n|H|n⟩ ≥ m · n`.
           Pushing to genuine n-particle states (and the resulting
           tower of inequalities) requires a Fock-space construction
           — beyond a finite-dim toy.

     (iii) The four Clay-grade mathlib barriers from Wave 47B remain
           open: Bochner–Minlos on nuclear spaces, `S(ℝ⁴)` reflection,
           Wightman reconstruction, mass-gap propagation. The toy is
           a structural marker, not a discharge.

    The YM mass-gap conditional-discharge chain (Waves 26 / 29 / 30 /
    39C / 43C / 46C / 47B / 48B–52D / 53D) is unchanged at the
    Millennium level; what Wave 53D adds is the first toy carrier
    where the literal Clay-style inequality `⟨vac|H|vac⟩ = 0 < m ≤
    ⟨oneParticle|H|oneParticle⟩` is machine-checked, axiom-free. -/
theorem ym_wightman_vacuum_toy_attempt_structural_remark :
    True := trivial

end YMWightmanVacuumToyAttempt
end PrincipiaTractalis
