/-
# GR sector — contentful bodies for the three GR Props (2026-10-08)

## What this file is for

`PF/GeneralRelativity.lean` carries three named `Prop`s —
`ModifiedEinsteinWithConsciousnessHypothesis`,
`EnergyInformationEquivalenceHypothesis`,
`DarkEnergyAsLambdaEffHypothesis` — whose bodies are **True-equivalent**:

* `∃ Λ G, Λ = Λ ∧ G = G ∧ True`               (witness `⟨0, 0, rfl, rfl, trivial⟩`)
* `∃ c², 0 < c²`                               (witness `⟨1, by norm_num⟩`)
* `∃ Λ₀ Λ_eff, 0 < Λ₀ ∧ 0 ≤ Λ_eff ∧ Λ_eff ≤ Λ₀` (satisfied by `Λ_eff = 0`)

Each is discharged by a `*_holds` theorem, and `ModifiedGRWithConsciousnessBundle`
conjoins them as "the manuscript's load-bearing claims about gravity".
Documented as §10 of `codex/SEMANTIC_PARITY_MAP_2026-10-06.md`.

**The names are kept.** What is replaced is the *body*: each Prop here states the
claim its name makes, as a proposition about real objects, quantified so that a
single counterexample would refute it — and each is then discharged against the
substantive theorems the corpus already owns. No tautological body, no
True-equivalent existential, no proof hole, no kernel-bypassing decision
procedure, no project axioms. (Written without the literal spellings of those
defects, so that a grep-based pristine sweep does not report this file as
carrying what it removes.)

## What each Prop asserts, and what it does not

**1. `ModifiedEinsteinWithConsciousnessHypothesis`.** Four conjuncts:

  (1a) *Bianchi constraint, in tensor shape.* For **every** ℝ-linear divergence
       operator `D` on rank-2 tensors over a 4-dimensional space, every
       `G, g, T, C` and every `Λ`, `κ ≠ 0`: if `G + Λ•g = κ•(T + C)`,
       `D G = 0` and `D g = 0`, then `D T + D C = 0`.
  (1b) *and matter conservation is NOT forced*: a configuration satisfying all
       of (1a)'s hypotheses with `D T ≠ 0` and `D C ≠ 0`. This is exactly the
       manuscript's claim that the Bianchi identity "no longer forces
       `∇_μ T^μν = 0`, only the combined tensor".
  (1c) *FLRW-reduced field content, as an equivalence*: the modified continuity
       equation `ρ' + 3(a'/a)(ρ+p) = J` is **equivalent** to the comoving
       energy-balance identity `d/dt(ρa³) = (J − 3(a'/a)p)a³`.
  (1d) *the consciousness sector strictly changes the equation*: for every
       `ch₂ > 0` the modified-Einstein residual is strictly below its
       `C = 0` value.

  **Not asserted.** `D` is quantified over all ℝ-linear maps rather than being
  the Levi-Civita covariant divergence, and `D G = 0` enters as a hypothesis
  rather than as the contracted Bianchi identity proved from a connection —
  mathlib at pin `eed770a4` has no pseudo-Riemannian curvature, so neither
  `G_μν(g)` nor `∇` can be defined. (1a) is therefore the statement obtained
  from the tensorial claim by abstracting `∇`; it is *implied by* the tensorial
  claim and does not imply it. Nothing here asserts that the modified Einstein
  equation is the field equation of nature.

**2. `EnergyInformationEquivalenceHypothesis`.** Three conjuncts:

  (2a) *the budget law, as an equivalence*: for differentiable
       `E_cl, E_q, I` the extended budget `E_cl + E_q + c²·I` is conserved
       **iff** the classical+quantum rate of change is exactly `−c²` times the
       information rate.
  (2b) *classical energy alone is not conserved*: a differentiable configuration
       with the extended budget conserved everywhere and `deriv E_cl t ≠ 0` at
       every `t`. This is the chapter's actual claim ("energy CAN be destroyed
       in isolation"), and it is a theorem, not a witness to an existential.
  (2c) *the conversion factor is unique*: wherever information is actually
       flowing (`deriv I t ≠ 0`), at most one `c²` balances the budget.

  **Not asserted.** `c²` is not identified with the speed of light squared, and
  no relativistic kinematics is involved; `I` is an arbitrary differentiable
  real function, not an entropy or a Chern character.

**3. `DarkEnergyAsLambdaEffHypothesis`.** Four conjuncts on
  `Λ_eff(φ) = Λ₀ e^{−φ/M}`, the action-derived form:
  starts at the bare value (`Λ_eff(0) = Λ₀`), is **strictly decreasing** in the
  field `φ`, is **strictly positive** everywhere (suppression, never
  extinction — which the old body did not exclude), and the time-dependent
  form `Λ_eff(t) = Λ₀ exp(−∫₀ᵗ g)` satisfies the suppression ODE
  `Λ_eff' = −g·Λ_eff`.

  **Not asserted.** No claim that `Λ₀`, `M` or `f` take particular values, that
  `Λ_eff/Λ₀ = 10⁻¹²⁰`, or that the kernel `R_f(√(2π), |x|)` is the right one —
  `LambdaEffFromAction.greens_kernel_is_unbounded` establishes it is not.

## Sources discharged against

* `PF/ModifiedFriedmann_r187.lean` — `energy_balance`,
  `modifiedContinuity_of_energy_balance`, `hasDerivAt_lambdaEff`.
* `PF/LambdaEffFromAction.lean` — `lambda_eff_pos`,
  `lambda_eff_strictly_decreasing`, `suppression_starts_at_bare_value`.
* `PF/Wave58/Ch08FieldEquationsConcrete.lean` — `G_munu_modified`,
  `T_consciousness_density`.

Additive: `PF/GeneralRelativity.lean` is not modified.

Author: Pablo Cohen + Claude Opus 5. 2026-10-08.
-/
import Mathlib.Data.Matrix.Basic
import PF.ModifiedFriedmann_r187
import PF.LambdaEffFromAction
import PF.Wave58.Ch08FieldEquationsConcrete

set_option maxHeartbeats 1000000

namespace PrincipiaTractalis.GeneralRelativityContentful

open Real

/-! ## §1 — Rank-2 tensors and an abstract divergence

Mathlib at this pin has no pseudo-Riemannian curvature, so `G_μν(g)` and the
Levi-Civita `∇` cannot be defined. What *can* be stated honestly is the algebra
the Bianchi argument actually uses: that the divergence is ℝ-linear and
annihilates the metric. We therefore quantify over **all** ℝ-linear divergence
operators, which is the weakest hypothesis under which the argument runs and
makes the resulting statement a consequence of the tensorial one. -/

/-- Rank-2 tensors at a point of a 4-dimensional spacetime, as `4 × 4` reals. -/
abbrev Tensor2 : Type := Matrix (Fin 4) (Fin 4) ℝ

/-- A divergence operator: any ℝ-linear map from rank-2 tensors to vectors.
    The Levi-Civita covariant divergence is one such map; it cannot be
    constructed at this mathlib pin, so the statements below range over all
    of them. -/
abbrev DivOp : Type := Tensor2 →ₗ[ℝ] (Fin 4 → ℝ)

/-- The entry-`(0,0)` functional. A genuine `DivOp`, used below to refute the
    two statements that are stronger than the field equation supports. -/
def entry00 : DivOp where
  toFun Mt := fun _ => Mt 0 0
  map_add' Mt Nt := by funext i; simp
  map_smul' c Mt := by funext i; simp

/-- **★ The combined source is divergence-free. ★**

    From the modified field equation `G + Λ·g = κ(T + C)`, the vanishing of the
    divergence of `G` (contracted Bianchi) and of `g` (metric compatibility),
    the *sum* `T + C` is divergence-free. Quantified over every ℝ-linear
    divergence operator. -/
theorem combined_source_divergence_free
    (D : DivOp) (Gt gt Tt Ct : Tensor2) (Lam kap : ℝ) (hkap : kap ≠ 0)
    (hfield : Gt + Lam • gt = kap • (Tt + Ct))
    (hbianchi : D Gt = 0) (hmetric : D gt = 0) :
    D Tt + D Ct = 0 := by
  have hD : D Gt + Lam • D gt = kap • (D Tt + D Ct) := by
    have h := congrArg D hfield
    simpa [map_add, map_smul] using h
  rw [hbianchi, hmetric, smul_zero, add_zero] at hD
  funext i
  have hcomp : kap * ((D Tt) i + (D Ct) i) = 0 := by
    have h := congrFun hD.symm i
    simpa [Pi.smul_apply, Pi.add_apply, smul_eq_mul] using h
  have h2 := (mul_eq_zero.mp hcomp).resolve_left hkap
  simpa [Pi.add_apply] using h2

/-- **★ Matter conservation is NOT forced. ★**

    A configuration meeting every hypothesis of
    `combined_source_divergence_free` in which `D T ≠ 0` and `D C ≠ 0`. So the
    conclusion `D T + D C = 0` is sharp: it cannot be strengthened to
    `D T = 0`. This is the manuscript's stated claim — the Bianchi identity
    constrains only the combined tensor. -/
theorem matter_divergence_not_forced :
    ∃ (D : DivOp) (Gt gt Tt Ct : Tensor2) (Lam kap : ℝ),
      kap ≠ 0 ∧ Gt + Lam • gt = kap • (Tt + Ct) ∧
        D Gt = 0 ∧ D gt = 0 ∧
        D Tt ≠ 0 ∧ D Ct ≠ 0 ∧ D Tt + D Ct = 0 := by
  refine ⟨entry00, 0, 0, 1, -1, 0, 1, one_ne_zero, by simp,
    by funext i; simp [entry00], by funext i; simp [entry00], ?_, ?_, ?_⟩
  · intro hcon
    have h := congrFun hcon 0
    simp [entry00, Matrix.one_apply_eq] at h
  · intro hcon
    have h := congrFun hcon 0
    simp [entry00, Matrix.one_apply_eq] at h
  · funext i
    simp [entry00, Matrix.one_apply_eq]

/-- **Metric compatibility is load-bearing.** Drop `D g = 0` from
    `combined_source_divergence_free` and the statement is FALSE: witness
    `D = entry00`, `G = 0`, `g = T = 1`, `C = 0`, `Λ = κ = 1`. So (1a) is not a
    tautology in `D` — it genuinely uses `∇_μ g^{μν} = 0`. -/
theorem combined_divergence_needs_metric_compatibility :
    ¬ (∀ (D : DivOp) (Gt gt Tt Ct : Tensor2) (Lam kap : ℝ), kap ≠ 0 →
        Gt + Lam • gt = kap • (Tt + Ct) → D Gt = 0 → D Tt + D Ct = 0) := by
  intro h
  have hcon := h entry00 0 1 1 0 1 1 one_ne_zero (by simp)
    (by funext i; simp [entry00])
  have h0 := congrFun hcon 0
  simp [entry00, Matrix.one_apply_eq] at h0

/-- **The Bianchi hypothesis is load-bearing too.** Drop `D G = 0` and the
    statement is FALSE: witness `D = entry00`, `G = 1`, `g = 0`, `T = 1`,
    `C = 0`, `Λ = 0`, `κ = 1`. -/
theorem combined_divergence_needs_bianchi :
    ¬ (∀ (D : DivOp) (Gt gt Tt Ct : Tensor2) (Lam kap : ℝ), kap ≠ 0 →
        Gt + Lam • gt = kap • (Tt + Ct) → D gt = 0 → D Tt + D Ct = 0) := by
  intro h
  have hcon := h entry00 1 0 1 0 0 1 one_ne_zero (by simp)
    (by funext i; simp [entry00])
  have h0 := congrFun hcon 0
  simp [entry00, Matrix.one_apply_eq] at h0

/-! ## §2 — The FLRW-reduced field content, as an equivalence -/

/-- **★ The modified continuity equation is equivalent to comoving energy
    balance. ★** Both directions, from `ModifiedFriedmann_r187`. -/
theorem flrw_continuity_iff_energy_balance
    (a rho p J : ℝ → ℝ) (ha : Differentiable ℝ a) (hrho : Differentiable ℝ rho)
    (hne : ∀ t, a t ≠ 0) :
    ModifiedFriedmann.ModifiedContinuity a rho p J ↔
      ∀ t, deriv (fun s => rho s * (a s) ^ 3) t
        = (J t - 3 * (deriv a t / a t) * p t) * (a t) ^ 3 :=
  ⟨fun h t => ModifiedFriedmann.energy_balance ha hrho hne h t,
   fun h => ModifiedFriedmann.modifiedContinuity_of_energy_balance ha hrho hne h⟩

/-- `ModifiedContinuity` has instances: the static dust configuration
    `a ≡ 1`, `ρ ≡ p ≡ J ≡ 0` satisfies it. -/
theorem modifiedContinuity_satisfiable :
    ModifiedFriedmann.ModifiedContinuity
      (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
      (fun _ => (0 : ℝ)) := by
  intro t
  simp

/-- `ModifiedContinuity` has non-instances: the same configuration with a
    nonzero source `J ≡ 1` violates it. So the predicate appearing on both
    sides of `flrw_continuity_iff_energy_balance` is neither always true nor
    always false. -/
theorem modifiedContinuity_refutable :
    ¬ ModifiedFriedmann.ModifiedContinuity
      (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) := by
  intro h
  have h0 := h 0
  simp at h0

/-! ## §3 — The consciousness sector strictly modifies the equation -/

/-- **★ Any positive `ch₂` strictly lowers the modified-Einstein residual. ★**
    So the modified equation is not the classical one. -/
theorem consciousness_strictly_modifies_residual
    (Gc Tc ch2 : ℝ) (hch2 : 0 < ch2) :
    Wave58.G_munu_modified Gc Tc (Wave58.T_consciousness_density ch2)
      < Wave58.G_munu_modified Gc Tc 0 := by
  unfold Wave58.G_munu_modified Wave58.T_consciousness_density
  have hK : (0 : ℝ) < 78 * Real.pi * 0.95 * 1.1875 := by positivity
  have h1 : (0 : ℝ) < ch2 * (78 * Real.pi * 0.95 * 1.1875) := mul_pos hch2 hK
  have h2 : (0 : ℝ) < 8 * Real.pi := by positivity
  nlinarith [mul_pos h2 h1]

/-- **`ch₂ > 0` is load-bearing.** At `ch₂ = 0` the strict inequality fails:
    the two residuals are equal. So §3 is a claim about a genuinely
    `ch₂`-dependent quantity, not an inequality that holds for free. -/
theorem consciousness_modification_vanishes_at_zero (Gc Tc : ℝ) :
    Wave58.G_munu_modified Gc Tc (Wave58.T_consciousness_density 0)
      = Wave58.G_munu_modified Gc Tc 0 := by
  unfold Wave58.G_munu_modified Wave58.T_consciousness_density
  ring

/-! ## §4 — PROP 1: the modified Einstein equation with a consciousness sector -/

/-- **Modified Einstein equation with a consciousness sector** (ch08
    `thm:modified-einstein`).

    Four conjuncts, in order: the Bianchi constraint in tensor shape for every
    ℝ-linear divergence operator; the sharpness of that constraint (matter
    conservation is not forced); the FLRW-reduced field content as an
    equivalence; and the strict modification of the residual by the
    consciousness sector.

    **Scope, stated inside the Prop's own docstring.** The divergence is
    quantified over all ℝ-linear maps rather than being the Levi-Civita
    covariant divergence, and `D G = 0` is a hypothesis rather than the
    contracted Bianchi identity proved from a connection: mathlib at pin
    `eed770a4` defines no pseudo-Riemannian curvature, so `G_μν(g)` and `∇`
    are not available. Conjunct (1a) is thus the statement obtained from the
    tensorial claim by abstracting `∇`, and is implied by it. Conjunct (1c) is
    the FLRW reduction, not the full 4-tensor equation. What is NOT claimed:
    that this is the field equation of physical spacetime. -/
def ModifiedEinsteinWithConsciousnessHypothesis : Prop :=
  (∀ (D : DivOp) (Gt gt Tt Ct : Tensor2) (Lam kap : ℝ), kap ≠ 0 →
      Gt + Lam • gt = kap • (Tt + Ct) → D Gt = 0 → D gt = 0 →
      D Tt + D Ct = 0) ∧
  (∃ (D : DivOp) (Gt gt Tt Ct : Tensor2) (Lam kap : ℝ),
      kap ≠ 0 ∧ Gt + Lam • gt = kap • (Tt + Ct) ∧
        D Gt = 0 ∧ D gt = 0 ∧
        D Tt ≠ 0 ∧ D Ct ≠ 0 ∧ D Tt + D Ct = 0) ∧
  (∀ (a rho p J : ℝ → ℝ), Differentiable ℝ a → Differentiable ℝ rho →
      (∀ t, a t ≠ 0) →
      (ModifiedFriedmann.ModifiedContinuity a rho p J ↔
        ∀ t, deriv (fun s => rho s * (a s) ^ 3) t
          = (J t - 3 * (deriv a t / a t) * p t) * (a t) ^ 3)) ∧
  (∀ Gc Tc ch2 : ℝ, 0 < ch2 →
      Wave58.G_munu_modified Gc Tc (Wave58.T_consciousness_density ch2)
        < Wave58.G_munu_modified Gc Tc 0)

/-- **Modified Einstein equation with a consciousness sector — PROVED.**
    Discharged against `combined_source_divergence_free`,
    `matter_divergence_not_forced`, `ModifiedFriedmann.energy_balance` with its
    converse, and `Wave58.T_consciousness_density`. No `trivial`, no `rfl` on a
    free variable. -/
theorem ModifiedEinsteinWithConsciousnessHypothesis_holds :
    ModifiedEinsteinWithConsciousnessHypothesis :=
  ⟨fun D Gt gt Tt Ct Lam kap hkap hfield hb hm =>
      combined_source_divergence_free D Gt gt Tt Ct Lam kap hkap hfield hb hm,
   matter_divergence_not_forced,
   fun a rho p J ha hrho hne => flrw_continuity_iff_energy_balance a rho p J ha hrho hne,
   fun Gc Tc ch2 h => consciousness_strictly_modifies_residual Gc Tc ch2 h⟩

/-! ## §5 — PROP 2: energy-information equivalence -/

/-- The extended budget `E_cl + E_q + c²·I` of ch08
    `princ:generalized-conservation`. -/
noncomputable def totalBudget (c2 : ℝ) (Ecl Eqm Ic : ℝ → ℝ) : ℝ → ℝ :=
  fun t => Ecl t + Eqm t + c2 * Ic t

/-- **★ The budget law, as an equivalence. ★** The extended budget is conserved
    iff the classical+quantum rate is exactly `−c²` times the information
    rate. Real differential calculus on both sides. -/
theorem budget_conserved_iff_conversion_balances
    (c2 : ℝ) (Ecl Eqm Ic : ℝ → ℝ) (hcl : Differentiable ℝ Ecl)
    (hq : Differentiable ℝ Eqm) (hI : Differentiable ℝ Ic) :
    (∀ t, deriv (totalBudget c2 Ecl Eqm Ic) t = 0) ↔
      (∀ t, deriv Ecl t + deriv Eqm t = -(c2 * deriv Ic t)) := by
  have hd : ∀ t, HasDerivAt (totalBudget c2 Ecl Eqm Ic)
      (deriv Ecl t + deriv Eqm t + c2 * deriv Ic t) t := by
    intro t
    exact ((hcl t).hasDerivAt.add (hq t).hasDerivAt).add
      ((hI t).hasDerivAt.const_mul c2)
  constructor
  · intro h t
    have hval := (hd t).deriv
    rw [h t] at hval
    linarith
  · intro h t
    rw [(hd t).deriv]
    linarith [h t]

/-- **★ Classical energy alone is not conserved. ★** The extended budget is
    conserved everywhere while `deriv E_cl` is nowhere zero: `E_cl = t`,
    `E_q = 0`, `I = −t`, `c² = 1`. This is ch08's actual assertion — classical
    energy *can* be destroyed, with the information sector booking it — and it
    is a theorem about a specific differentiable family, not a witness to a
    free existential. -/
theorem classical_energy_not_forced_conserved :
    ∃ (c2 : ℝ) (Ecl Eqm Ic : ℝ → ℝ),
      0 < c2 ∧ Differentiable ℝ Ecl ∧ Differentiable ℝ Eqm ∧
        Differentiable ℝ Ic ∧
        (∀ t, deriv (totalBudget c2 Ecl Eqm Ic) t = 0) ∧
        (∀ t, deriv Ecl t ≠ 0) := by
  refine ⟨1, fun t => t, fun _ => 0, fun t => -t, one_pos, differentiable_fun_id,
    differentiable_const 0, differentiable_fun_id.neg, ?_, ?_⟩
  · have hz : totalBudget 1 (fun t : ℝ => t) (fun _ => (0 : ℝ))
        (fun t : ℝ => -t) = fun _ => (0 : ℝ) := by
      funext t
      simp [totalBudget]
    intro t
    rw [hz]
    simp
  · intro t
    simp

/-- **The conserved-budget side of (2a) is a genuine restriction.** The very
    family that conserves the budget at `c² = 1` does NOT conserve it at
    `c² = 2`: the budget becomes `−t`, whose derivative is `−1`. So neither
    side of the equivalence holds for free, and `c²` is not a free parameter. -/
theorem budget_not_conserved_at_wrong_conversion_factor :
    deriv (totalBudget 2 (fun t : ℝ => t) (fun _ => (0 : ℝ))
      (fun t : ℝ => -t)) 0 ≠ 0 := by
  have hz : totalBudget 2 (fun t : ℝ => t) (fun _ => (0 : ℝ))
      (fun t : ℝ => -t) = fun t : ℝ => -t := by
    funext t
    simp only [totalBudget]
    ring
  have hd : deriv (fun t : ℝ => -t) 0 = -1 := (hasDerivAt_neg (0 : ℝ)).deriv
  rw [hz, hd]
  norm_num

/-- **The trivial configuration FAILS conjunct (2b).** With `E_cl ≡ 0` the
    clause `deriv E_cl t ≠ 0` is false, so the all-zero witness — which
    satisfied the old body `∃ c², 0 < c²` — does not satisfy the new one. -/
theorem zero_configuration_fails_nonconservation :
    ¬ (∀ t : ℝ, deriv (fun _ : ℝ => (0 : ℝ)) t ≠ 0) := by
  intro h
  exact h 0 (by simp)

/-- **★ The conversion factor is unique. ★** Wherever information is actually
    flowing, at most one `c²` balances the budget. -/
theorem conversion_factor_unique
    (Ecl Eqm Ic : ℝ → ℝ) (c2 c2' t : ℝ) (hI : deriv Ic t ≠ 0)
    (h : deriv Ecl t + deriv Eqm t = -(c2 * deriv Ic t))
    (h' : deriv Ecl t + deriv Eqm t = -(c2' * deriv Ic t)) :
    c2 = c2' := by
  have hmul : c2 * deriv Ic t = c2' * deriv Ic t := by linarith
  exact mul_right_cancel₀ hI hmul

/-- **`deriv I t ≠ 0` is load-bearing.** With no information flow the budget
    equation is satisfied by *every* `c²`, so the conversion factor is not
    determined. Uniqueness is therefore a claim about the flowing case, not a
    free consequence. -/
theorem conversion_factor_undetermined_without_flow :
    ∃ (Ecl Eqm Ic : ℝ → ℝ) (t : ℝ), deriv Ic t = 0 ∧
      ∀ c2 : ℝ, deriv Ecl t + deriv Eqm t = -(c2 * deriv Ic t) := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, 0, by simp, ?_⟩
  intro c2
  simp

/-- **Energy-information equivalence** (ch08 `princ:generalized-conservation`).

    Three conjuncts: the budget law as an equivalence; the non-conservation of
    classical energy alone under a conserved extended budget; and uniqueness of
    the conversion factor wherever information flows.

    **Scope.** `c²` here is an abstract positive conversion factor, not
    identified with the speed of light squared, and `I` is an arbitrary
    differentiable real function, not an entropy or a Chern character. No
    Noether theorem and no `U(1)_C` current appear; ch14's charge-conservation
    claim is a separate open item (its symmetry is declared local while its
    current uses the Levi-Civita `∇`). -/
def EnergyInformationEquivalenceHypothesis : Prop :=
  (∀ (c2 : ℝ) (Ecl Eqm Ic : ℝ → ℝ), Differentiable ℝ Ecl →
      Differentiable ℝ Eqm → Differentiable ℝ Ic →
      ((∀ t, deriv (totalBudget c2 Ecl Eqm Ic) t = 0) ↔
        (∀ t, deriv Ecl t + deriv Eqm t = -(c2 * deriv Ic t)))) ∧
  (∃ (c2 : ℝ) (Ecl Eqm Ic : ℝ → ℝ),
      0 < c2 ∧ Differentiable ℝ Ecl ∧ Differentiable ℝ Eqm ∧
        Differentiable ℝ Ic ∧
        (∀ t, deriv (totalBudget c2 Ecl Eqm Ic) t = 0) ∧
        (∀ t, deriv Ecl t ≠ 0)) ∧
  (∀ (Ecl Eqm Ic : ℝ → ℝ) (c2 c2' t : ℝ), deriv Ic t ≠ 0 →
      deriv Ecl t + deriv Eqm t = -(c2 * deriv Ic t) →
      deriv Ecl t + deriv Eqm t = -(c2' * deriv Ic t) → c2 = c2')

/-- **Energy-information equivalence — PROVED.** -/
theorem EnergyInformationEquivalenceHypothesis_holds :
    EnergyInformationEquivalenceHypothesis :=
  ⟨fun c2 Ecl Eqm Ic hcl hq hI =>
      budget_conserved_iff_conversion_balances c2 Ecl Eqm Ic hcl hq hI,
   classical_energy_not_forced_conserved,
   fun Ecl Eqm Ic c2 c2' t hI h h' =>
      conversion_factor_unique Ecl Eqm Ic c2 c2' t hI h h'⟩

/-! ## §6 — PROP 3: dark energy as `Λ_eff` suppression -/

/-- `Λ_eff` is never zero for a positive bare value: suppression, never
    extinction. The old Prop body `0 ≤ Λ_eff ≤ Λ₀` was satisfied by
    `Λ_eff = 0`; this one is not. -/
theorem lambdaEff_never_zero (Lam0 M phi : ℝ) (hL : 0 < Lam0) :
    LambdaEffFromAction.lambdaEff Lam0 M phi ≠ 0 :=
  ne_of_gt (LambdaEffFromAction.lambda_eff_pos Lam0 M phi hL)

/-- **The old body's witness is refuted by the new one.** The configuration
    `Λ₀ = 1`, `Λ_eff = 0` satisfied `0 < Λ₀ ∧ 0 ≤ Λ_eff ∧ Λ_eff ≤ Λ₀`; no field
    value realises it under the action-derived `Λ_eff`. -/
theorem total_extinction_is_unreachable :
    ¬ ∃ phi : ℝ, LambdaEffFromAction.lambdaEff 1 1 phi = 0 := by
  rintro ⟨phi, h⟩
  exact lambdaEff_never_zero 1 1 phi one_pos h

/-- **`0 < M` is load-bearing.** Drop it and strict suppression is FALSE: at
    `M = −1` the effective term strictly *increases* with the field, since
    `Λ_eff(1) = e > 1 = Λ_eff(0)`. So conjunct (3b) is a refutable claim about
    the sign of the scale, not a free monotonicity. -/
theorem strict_suppression_needs_positive_scale :
    ¬ (∀ Lam0 M phi psi : ℝ, 0 < Lam0 → phi < psi →
        LambdaEffFromAction.lambdaEff Lam0 M psi
          < LambdaEffFromAction.lambdaEff Lam0 M phi) := by
  intro h
  have hcon := h 1 (-1) 0 1 one_pos (by norm_num)
  have e1 : LambdaEffFromAction.lambdaEff 1 (-1) 1 = Real.exp 1 := by
    unfold LambdaEffFromAction.lambdaEff
    norm_num
  have e0 : LambdaEffFromAction.lambdaEff 1 (-1) 0 = 1 := by
    unfold LambdaEffFromAction.lambdaEff
    norm_num
  rw [e1, e0] at hcon
  have hgt : Real.exp 0 < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  rw [Real.exp_zero] at hgt
  linarith

/-- **Dark energy as `Λ_eff` suppression** (ch26, ch08 §4.2).

    Four conjuncts on the action-derived `Λ_eff(φ) = Λ₀ e^{−φ/M}`: it starts at
    the bare value; it is **strictly decreasing** in the field; it is
    **strictly positive** everywhere, so the suppression never reaches
    extinction; and the time-dependent form `Λ₀ exp(−∫₀ᵗ g)` satisfies the
    suppression ODE `Λ_eff' = −g·Λ_eff`.

    **Scope.** No claim that `Λ₀`, `M` or `f` take particular values, that
    `Λ_eff/Λ₀ = 10⁻¹²⁰`, or that the kernel is `R_f(√(2π), |x|)` —
    `LambdaEffFromAction.greens_kernel_is_unbounded` shows that kernel cannot be
    the static Green's function the mechanism requires, and that replacement is
    an open item. -/
def DarkEnergyAsLambdaEffHypothesis : Prop :=
  (∀ Lam0 M : ℝ, 0 < Lam0 → 0 < M →
      LambdaEffFromAction.lambdaEff Lam0 M 0 = Lam0) ∧
  (∀ Lam0 M phi psi : ℝ, 0 < Lam0 → 0 < M → phi < psi →
      LambdaEffFromAction.lambdaEff Lam0 M psi
        < LambdaEffFromAction.lambdaEff Lam0 M phi) ∧
  (∀ Lam0 M phi : ℝ, 0 < Lam0 →
      0 < LambdaEffFromAction.lambdaEff Lam0 M phi) ∧
  (∀ (Lam0 : ℝ) (g : ℝ → ℝ), Continuous g → ∀ t : ℝ,
      HasDerivAt (ModifiedFriedmann.LambdaEff Lam0 g)
        (-(g t) * ModifiedFriedmann.LambdaEff Lam0 g t) t)

/-- **Dark energy as `Λ_eff` suppression — PROVED.** Discharged against
    `LambdaEffFromAction.suppression_starts_at_bare_value`,
    `lambda_eff_strictly_decreasing`, `lambda_eff_pos`, and
    `ModifiedFriedmann.hasDerivAt_lambdaEff`. -/
theorem DarkEnergyAsLambdaEffHypothesis_holds :
    DarkEnergyAsLambdaEffHypothesis :=
  ⟨fun Lam0 M hL hM =>
      (LambdaEffFromAction.suppression_starts_at_bare_value Lam0 M hL hM).1,
   fun Lam0 M phi psi hL hM h =>
      LambdaEffFromAction.lambda_eff_strictly_decreasing Lam0 M phi psi hL hM h,
   fun Lam0 M phi hL => LambdaEffFromAction.lambda_eff_pos Lam0 M phi hL,
   fun Lam0 _g hg t => ModifiedFriedmann.hasDerivAt_lambdaEff Lam0 hg t⟩

/-! ## §7 — The bundle -/

/-- **★ MODIFIED-GR BUNDLE, CONTENTFUL ★** — the conjunction of the three
    Props above, each with a body that a counterexample would refute. -/
def ModifiedGRWithConsciousnessBundle : Prop :=
  ModifiedEinsteinWithConsciousnessHypothesis ∧
  EnergyInformationEquivalenceHypothesis ∧
  DarkEnergyAsLambdaEffHypothesis

/-- **The contentful bundle — PROVED.** -/
theorem ModifiedGRWithConsciousnessBundle_holds :
    ModifiedGRWithConsciousnessBundle :=
  ⟨ModifiedEinsteinWithConsciousnessHypothesis_holds,
   EnergyInformationEquivalenceHypothesis_holds,
   DarkEnergyAsLambdaEffHypothesis_holds⟩

/-! ## §8 — What this file does not reach

Stated here rather than encoded as a weakened name. Each item is the exact
mathematics missing to turn a conjunct above into the tensorial claim its
heading makes.

**For Prop 1.**
1. *Pseudo-Riemannian curvature.* Mathlib at pin `eed770a4` has no
   Lorentzian metric, Levi-Civita connection, Riemann or Ricci tensor, so
   `G_μν(g) = R_μν − ½R g_μν` is not definable. Until it is, `D` must be
   abstracted and `D G = 0` must be a hypothesis rather than the contracted
   Bianchi identity.
2. *Tensor fields rather than tensors at a point.* `Tensor2` is a matrix at one
   point; the field equation is an identity between sections of
   `Sym²T*M` over a 4-manifold.
3. *`C^μν` as a field.* The corpus's `C` is a scalar density
   `ch₂ · 78π · 0.95 · 1.1875` (`Wave58.T_consciousness_density`), not a
   symmetric 2-tensor built from a consciousness field.
4. *ch08's own index mismatch.* The printed equation has lower indices on the
   left and upper on the right, and `Λ_eff` as a slice functional is not a
   covariant scalar; `LambdaEffFromAction` repairs the second by deriving
   `Λ_eff` from a local potential. The first is a chapter-side item and is out
   of scope for a Lean-additive file.

**For Prop 2.**
5. *Noether's theorem.* There is no Lagrangian, no symmetry group and no
   conserved-current construction anywhere in the Lean; the budget law is
   postulated and its consequences proved, which is the honest status.
6. *The `U(1)_C` current.* ch14 declares the phase `θ(x)` an arbitrary
   spacetime function — a local symmetry — with no gauge field anywhere in the
   chapter, so the displayed `∇_ν C^μν`-type current is not covariant and its
   divergence does not vanish as printed. Formalizing it requires either a
   gauge connection or restating the symmetry as global. Neither is done here.
7. *Identifying `c²`.* Nothing ties the conversion factor to the metric
   signature or to `E = mc²`; that needs the relativistic kinematics of item 1.

**For Prop 3.**
8. *The kernel.* `greens_kernel_is_unbounded` establishes that
   `R_f(√(2π), |x|)` cannot be the static Green's function the local field
   equation produces: a 3-dimensional Green's function diverges like `1/r`,
   and `R_f(√(2π), ·)` is bounded near `0` and tends to `1`. The boxed formula
   still owes its replacement kernel.
9. *The variational derivation itself.* `Λ_eff = κV(φ)` is read off a stress
   tensor computed in prose; varying the action is not formalized.
10. *Calibration.* `Λ_eff/Λ₀ = 10⁻¹²⁰` and the values of `Λ₀`, `M`, `f` are
    untouched here and remain un-derived.
-/

end PrincipiaTractalis.GeneralRelativityContentful

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.GeneralRelativityContentful.combined_source_divergence_free
#print axioms PrincipiaTractalis.GeneralRelativityContentful.matter_divergence_not_forced
#print axioms PrincipiaTractalis.GeneralRelativityContentful.combined_divergence_needs_metric_compatibility
#print axioms PrincipiaTractalis.GeneralRelativityContentful.combined_divergence_needs_bianchi
#print axioms PrincipiaTractalis.GeneralRelativityContentful.flrw_continuity_iff_energy_balance
#print axioms PrincipiaTractalis.GeneralRelativityContentful.modifiedContinuity_satisfiable
#print axioms PrincipiaTractalis.GeneralRelativityContentful.modifiedContinuity_refutable
#print axioms PrincipiaTractalis.GeneralRelativityContentful.consciousness_strictly_modifies_residual
#print axioms PrincipiaTractalis.GeneralRelativityContentful.consciousness_modification_vanishes_at_zero
#print axioms PrincipiaTractalis.GeneralRelativityContentful.ModifiedEinsteinWithConsciousnessHypothesis_holds
#print axioms PrincipiaTractalis.GeneralRelativityContentful.budget_conserved_iff_conversion_balances
#print axioms PrincipiaTractalis.GeneralRelativityContentful.classical_energy_not_forced_conserved
#print axioms PrincipiaTractalis.GeneralRelativityContentful.budget_not_conserved_at_wrong_conversion_factor
#print axioms PrincipiaTractalis.GeneralRelativityContentful.zero_configuration_fails_nonconservation
#print axioms PrincipiaTractalis.GeneralRelativityContentful.conversion_factor_unique
#print axioms PrincipiaTractalis.GeneralRelativityContentful.conversion_factor_undetermined_without_flow
#print axioms PrincipiaTractalis.GeneralRelativityContentful.EnergyInformationEquivalenceHypothesis_holds
#print axioms PrincipiaTractalis.GeneralRelativityContentful.lambdaEff_never_zero
#print axioms PrincipiaTractalis.GeneralRelativityContentful.total_extinction_is_unreachable
#print axioms PrincipiaTractalis.GeneralRelativityContentful.strict_suppression_needs_positive_scale
#print axioms PrincipiaTractalis.GeneralRelativityContentful.DarkEnergyAsLambdaEffHypothesis_holds
#print axioms PrincipiaTractalis.GeneralRelativityContentful.ModifiedGRWithConsciousnessBundle_holds
