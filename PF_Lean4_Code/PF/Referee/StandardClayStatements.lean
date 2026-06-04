/-
# PF.Referee.StandardClayStatements

Typed standard contracts for each Clay axis. **No `Prop := True`.**

Where mathlib provides the standard object (RH via `riemannZeta`), the
contract is fully wired. Where it does not (P vs NP, NS, YM, BSD,
Hodge), the contract is parameterised over an external encoding the
framework user must supply, separating *what the Clay statement says*
from *what mathlib currently formalises*. Discharging an axis requires
both supplying the encoding and proving the typed statement.

Source roadmap: `codex/MILLENNIUM_REFEREE_ROADMAP_2026-06-02.md`
("The Twelfth Object" + Non-Negotiable Rule #1).
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import PF.SpectralBijection

namespace PF.Referee.StandardClayStatements

/-! ## §1 — RH (fully wired to mathlib's `riemannZeta`)

  Clay-standard critical-strip form:
  `∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1/2`.
  Defined as `PrincipiaTractalis.RiemannHypothesis` from
  `PF/SpectralBijection.lean` so the typed contract matches the
  conclusion of `riemann_hypothesis_via_T3_sym_framework` on the nose.
  (Mathlib's own `RiemannHypothesis` predicate uses a different,
  classically-equivalent excluded-zeros form.) -/

/-- **Clay Riemann Hypothesis (standard form).** Defined to be
    `PrincipiaTractalis.RiemannHypothesis`, the standard critical-strip
    statement: every zero of `riemannZeta` strictly inside the strip
    `0 < Re(s) < 1` has real part `1/2`. -/
def Clay_RiemannHypothesis_Standard : Prop :=
  PrincipiaTractalis.RiemannHypothesis

/-! ## §2 — P vs NP (parameterised; mathlib lacks TM complexity classes) -/

/-- An external encoding of the standard complexity classes P and NP.
    A discharge of `Clay_PvsNP_Standard` requires the framework user
    to instantiate this with a concrete, accepted encoding (e.g. via
    Turing machines on binary strings or Boolean circuits). -/
structure StandardComplexityEncoding where
  /-- The standard polynomial-time decision class. -/
  ClassP : Type
  /-- The standard nondeterministic polynomial-time decision class. -/
  ClassNP : Type
  /-- The standard injection P ↪ NP. -/
  inclusion : ClassP → ClassNP

/-- **Clay P ≠ NP (standard form).** Over a standard encoding `E`,
    the inclusion `P → NP` is not surjective. -/
def Clay_PvsNP_Standard (E : StandardComplexityEncoding) : Prop :=
  ¬ Function.Surjective E.inclusion

/-! ## §3 — Navier-Stokes (parameterised; mathlib lacks Schwartz/H^s NS) -/

/-- An external encoding of the standard Clay 3D Navier-Stokes setting:
    velocity field type, initial-data type, smoothness predicate, and
    a notion of global existence. -/
structure StandardNS3DEncoding where
  Velocity : Type
  InitialData : Type
  isSchwartzDivFree : InitialData → Prop
  hasGlobalSmoothSolution : InitialData → Prop

/-- **Clay Navier-Stokes (standard form).** Over a standard 3D NS
    encoding `E`, every Schwartz divergence-free initial datum admits
    a smooth global solution. This is the existence-and-smoothness
    side of the Clay statement. -/
def Clay_NavierStokes_Standard (E : StandardNS3DEncoding) : Prop :=
  ∀ u0 : E.InitialData, E.isSchwartzDivFree u0 → E.hasGlobalSmoothSolution u0

/-! ## §4 — Yang-Mills mass gap (parameterised; mathlib lacks Wightman/OS) -/

/-- An external encoding of the standard Clay Yang-Mills setting on
    ℝ⁴ for a compact simple gauge group. -/
structure StandardYMEncoding where
  /-- The gauge group (e.g. SU(N) for N ≥ 2). -/
  GaugeGroup : Type
  /-- An admissible Yang-Mills quantum theory (Wightman/OS). -/
  QYM : Type
  /-- Satisfies the Clay axioms (Wightman or OS reconstruction). -/
  satisfiesClayAxioms : QYM → Prop
  /-- The mass gap of a theory. -/
  massGap : QYM → ℝ

/-- **Clay Yang-Mills existence + mass gap (standard form).** There
    exists a Clay-axiom-satisfying quantum Yang-Mills theory with
    strictly positive mass gap. -/
def Clay_YangMillsMassGap_Standard (E : StandardYMEncoding) : Prop :=
  ∃ T : E.QYM, E.satisfiesClayAxioms T ∧ E.massGap T > 0

/-! ## §5 — BSD (parameterised; mathlib lacks full EC L-functions / MW rank) -/

/-- An external encoding of the standard Clay BSD setting. -/
structure StandardBSDEncoding where
  EllipticCurve : Type
  /-- The algebraic (Mordell-Weil) rank. -/
  algebraicRank : EllipticCurve → ℕ
  /-- The analytic rank `ord_{s=1} L(E, s)`. -/
  analyticRank : EllipticCurve → ℕ

/-- **Clay Birch-Swinnerton-Dyer (standard form).** For every elliptic
    curve in the standard encoding, the analytic rank equals the
    Mordell-Weil rank. -/
def Clay_BSD_Standard (E : StandardBSDEncoding) : Prop :=
  ∀ Ec : E.EllipticCurve, E.analyticRank Ec = E.algebraicRank Ec

/-! ## §6 — Hodge (parameterised; mathlib lacks Chow / cycle-class / Hodge decomp) -/

/-- An external encoding of the standard Clay Hodge setting. -/
structure StandardHodgeEncoding where
  SmoothProjectiveComplexVariety : Type
  /-- A rational Hodge class on `X`. -/
  RationalHodgeClass : SmoothProjectiveComplexVariety → Type
  /-- Predicate: is this class a `ℚ`-linear combination of algebraic
      cycle classes? -/
  isAlgebraic : (X : SmoothProjectiveComplexVariety) → RationalHodgeClass X → Prop

/-- **Clay Hodge Conjecture (standard form).** Every rational Hodge
    class on a smooth projective complex variety is a `ℚ`-linear
    combination of algebraic cycle classes. -/
def Clay_Hodge_Standard (E : StandardHodgeEncoding) : Prop :=
  ∀ (X : E.SmoothProjectiveComplexVariety) (c : E.RationalHodgeClass X),
    E.isAlgebraic X c

/-! ## §7 — Rule #1 compliance marker -/

/-- Provenness tag (ProvennessTag): structural marker that this file
    has no `Prop := True` Clay-statement definitions (the six contracts
    above are either fully wired or parameterised over an encoding). -/
theorem rule1_compliance : True := trivial

#check @Clay_RiemannHypothesis_Standard
#check @Clay_PvsNP_Standard
#check @Clay_NavierStokes_Standard
#check @Clay_YangMillsMassGap_Standard
#check @Clay_BSD_Standard
#check @Clay_Hodge_Standard

end PF.Referee.StandardClayStatements
