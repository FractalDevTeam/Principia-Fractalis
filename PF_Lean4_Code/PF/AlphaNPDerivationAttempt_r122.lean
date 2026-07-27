/-
# α_NP Derivation Attempt — r122 (2026-07-26)

★ A serious, honest attempt to DERIVE `α_NP = φ + 1/4` from something more
primitive, and — where that fails — to prove precisely WHY it cannot be
derived from the framework's stated postulates. ★

Companion note: `codex/ALPHA_NP_DERIVATION_ATTEMPT_2026-07-26.md`.
Prior audit:    `codex/ALPHA_NP_DERIVABILITY_2026-07-25.md`.

## What this file establishes (all axiom-free, no `sorry`, no `Prop := True`)

**§1 — The universal coupling carries ZERO information about α.**
`λ₀(α)·α = π/10` is satisfiable for EVERY nonzero α by choosing
`λ₀ := π/(10α)`. It is a change of variables, not a constraint. Any argument
of the form "the coupling pins α" is therefore void.

**§2 — The π/10 ↔ H₃ thread yields `φ` EXACTLY, and EXCLUDES `φ + 1/4`.**
Combine the coupling with the classical icosahedral identity
`sin(π/10) = 1/(2φ)` (`PF/H3CoxeterOrigin.lean`) in the only natural
self-consistent way — `α = 1/(2·sin(λ₀(α)·α))` — and the unique solution is
`α = φ`, with `α = φ + 1/4` provably failing. The residual is computed
exactly: `2·(φ+1/4)·sin(π/10) = 1 + 1/(4φ)`.
**The framework can motivate φ. It cannot motivate the +1/4 this way.**

**§3 — POSITIVE RESULT: the `+1/4` is a Galois trace, not a free rational.**
Inside the golden sector (`α ∈ φ + ℚ`, i.e. unit φ-modulation), the ℚ(√5)
trace is `Tr(φ + q) = 1 + 2q`. Hence the single postulate

    (T)   Tr_{ℚ(√5)/ℚ}(α_NP) = α_RH

pins `q = (α_RH − 1)/2 = (α_RH − α_Poincaré)/[ℚ(√5):ℚ]`, giving
`α_NP = φ + 1/4` from `α_RH = 3/2` and `α_Poincaré = 1` — **two constants
the framework already fixes in OTHER sectors, with no reference to α_NP.**
This is non-circular (unlike `α_NP − α_Hodge = 1/4`, which IS the value).

**§4 — The quadratic `16x² − 24x − 11` has no content beyond (Tr, disc).**
It is *identically* `(2x − α_RH)² = 5`. The coefficients are
`24 = 16·α_RH` and `11 = 4·5 − 4·α_RH²`, and its discriminant
`1280 = 16²·5` carries the golden discriminant `5` times the squared
normalisation. So "the quadratic forces φ + 1/4" is a restatement of (T).

**§5 — `φ + 1/4` is NOT an algebraic integer of ℚ(√5).**
`φ + 1/4 ∉ ℤ[φ]`. Since every H₃ Coxeter invariant — Cartan entries,
Coxeter-element eigenvalues (in the maximal real subfield of ℚ(ζ₁₀)),
character values of `H₃ ≅ ℤ/2 × A₅`, root coordinates — is an algebraic
integer of ℚ(√5), **no ℤ-polynomial combination of H₃ data can equal α_NP.**
A derivation must divide by 4 at some point; H₃ supplies no such division.

**§6 — IMPOSSIBILITY: α_NP is INDEPENDENT of every non-definitional postulate.**
Take the framework's α-skeleton (`CrossMillenniumSharedInvariants`) with
clause (10) `α_NP − α_Hodge = 1/4` removed — that clause is the *only* one
mentioning α_NP — and keep every non-definitional constraint that does
mention it (positivity, `α_NP ≠ α_P` from `AlphaRealizationNoGo`, and the
universal coupling). Then **for EVERY `r > 0` with `r ≠ √2` there is a model
with `α_NP = r`.** Hence the stated postulates do not determine α_NP: the pin
is an axiom or an empirical input, not a consequence.

**§7 — The corpus's own bare-GF reality route: sin-branch eliminated.**
`bare_route_structural_finding` leaves two branches. We kill branch (i)
outright: `sin(π(φ+1/4)) ≠ 0`. So if the bare reality condition held at
α_NP it could only be via `cos(π·α_NP) = −1/2`, which forces α_NP ∈ ℚ.

## Honest scope

§3 is a REDUCTION, not an elimination. It replaces one free rational (`1/4`)
by one cross-sector postulate (T). The information content is the same real
number; what changes is that (T) is (a) non-circular, (b) stated across
sectors so that an independent determination of α_RH would test it, and
(c) mechanism-shaped rather than inert. Two conditions (golden-sector
membership + trace) determine two degrees of freedom, so there is NO
over-determination and NO independent confirmation. Said plainly:
**nothing here derives φ + 1/4 from operator theory; §6 proves that nothing
in the stated postulate set can.**

Axiom budget: zero project axioms, zero `sorry`, zero `admit`.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic
import PF.H3CoxeterOrigin
import PF.TuringEncoding.WeightedDigitalSumGeneratingFunction

namespace PrincipiaFractalis.AlphaNPDerivationAttempt_r122

open Real
open scoped goldenRatio

/-! ## §1 — The universal coupling `λ₀·α = π/10` carries no information -/

/-- The framework's universal coupling relation. -/
def Coupling (lam α : ℝ) : Prop := lam * α = Real.pi / 10

/-- **The coupling is satisfiable at every nonzero α.** Choose
    `λ₀ := π/(10α)`. -/
theorem coupling_holds_of_ne_zero (α : ℝ) (hα : α ≠ 0) :
    Coupling (Real.pi / (10 * α)) α := by
  unfold Coupling
  field_simp

/-- **★ The coupling determines NO α.** For every positive `α` there is a
    `λ₀` satisfying the universal coupling. Therefore no argument of the
    form "the universal coupling pins α_NP" can have content. -/
theorem coupling_determines_no_alpha :
    ∀ α : ℝ, 0 < α → ∃ lam : ℝ, Coupling lam α :=
  fun α hα => ⟨_, coupling_holds_of_ne_zero α (ne_of_gt hα)⟩

/-! ## §2 — The π/10 ↔ H₃ thread produces `φ`, and excludes `φ + 1/4` -/

/-- **Icosahedral self-consistency.** The only natural way to combine the
    framework's coupling `λ₀·α = π/10` with the classical H₃ identity
    `sin(π/10) = 1/(2φ)` into a condition on α: require α to be the
    reciprocal-double-sine of its own coupling angle,
    `α = 1 / (2·sin(λ₀·α))`. -/
def IcosahedralSelfConsistency (lam α : ℝ) : Prop :=
  Coupling lam α ∧ 2 * α * Real.sin (lam * α) = 1

/-- **★★ The π/10 route forces `α = φ` — EXACTLY, and uniquely.**
    This is the strongest thing the H₃/coupling thread can do. -/
theorem icosahedral_self_consistency_forces_goldenRatio
    (lam α : ℝ) (h : IcosahedralSelfConsistency lam α) :
    α = Real.goldenRatio := by
  obtain ⟨hc, hs⟩ := h
  unfold Coupling at hc
  rw [hc, PrincipiaFractalis.H3CoxeterOrigin.sin_pi_div_ten_eq_inv_two_phi] at hs
  have hφ : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hne : Real.goldenRatio ≠ 0 := ne_of_gt hφ
  field_simp at hs
  have hdef : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  linarith

/-- **★★ `α_NP = φ + 1/4` FAILS the icosahedral self-consistency.**
    The H₃/π-10 thread cannot produce the `+1/4`. -/
theorem alphaNP_fails_icosahedral_self_consistency (lam : ℝ) :
    ¬ IcosahedralSelfConsistency lam (Real.goldenRatio + 1/4) := by
  intro h
  have := icosahedral_self_consistency_forces_goldenRatio lam _ h
  linarith

/-- **The exact residual.** At `α = φ + 1/4` the icosahedral condition
    overshoots by exactly `1/(4φ)`:
    `2·(φ + 1/4)·sin(π/10) = 1 + 1/(4φ)`.
    (Equivalently `= 1 + (φ−1)/4`, since `1/φ = φ − 1`.) -/
theorem icosahedral_residual_at_alphaNP :
    2 * (Real.goldenRatio + 1/4) * Real.sin (Real.pi / 10)
      = 1 + 1 / (4 * Real.goldenRatio) := by
  rw [PrincipiaFractalis.H3CoxeterOrigin.sin_pi_div_ten_eq_inv_two_phi]
  have hne : Real.goldenRatio ≠ 0 := ne_of_gt Real.goldenRatio_pos
  field_simp

/-! ## §3 — POSITIVE RESULT: the golden-sector trace law -/

/-- Golden-sector element with offset `q`: `φ + q`. "Unit φ-modulation". -/
noncomputable def sectorElt (q : ℝ) : ℝ := Real.goldenRatio + q

/-- Its ℚ(√5)-Galois conjugate: `ψ + q`, where `ψ = (1 − √5)/2`. -/
noncomputable def sectorConj (q : ℝ) : ℝ := Real.goldenConj + q

/-- The ℚ(√5)-trace of a golden-sector element. -/
noncomputable def sectorTrace (q : ℝ) : ℝ := sectorElt q + sectorConj q

/-- **Trace formula**: `Tr(φ + q) = 1 + 2q`. -/
theorem sectorTrace_eq (q : ℝ) : sectorTrace q = 1 + 2 * q := by
  unfold sectorTrace sectorElt sectorConj
  have := Real.goldenRatio_add_goldenConj
  linarith

/-- **Spread formula**: `(φ + q) − (ψ + q) = √5`, independent of `q`.
    This is what "unit φ-modulation" means: the golden discriminant is
    inherited unchanged from `α_Hodge = φ`. -/
theorem sectorSpread_eq (q : ℝ) : sectorElt q - sectorConj q = Real.sqrt 5 := by
  unfold sectorElt sectorConj
  have := Real.goldenRatio_sub_goldenConj
  linarith

/-- **The trace law pins the offset.** Given the trace `T`, the offset is
    forced: `q = (T − 1)/2`. The `2` is `[ℚ(√5):ℚ]`; the `1` is `Tr(φ)`,
    which the framework already calls `α_Poincaré`. -/
theorem trace_pins_offset (q T : ℝ) (h : sectorTrace q = T) : q = (T - 1) / 2 := by
  rw [sectorTrace_eq] at h; linarith

/-- **★★★ MAIN POSITIVE RESULT — `α_NP` from the trace law.**

    Hypotheses (NONE of which mentions `1/4`, `φ + 1/4`, or the NP quadratic):

    * `hHodge` : `α_Hodge = φ`                      — golden sector generator
    * `hSector`: `α_NP = α_Hodge + q`               — unit φ-modulation (S1)
    * `hTrace` : `Tr_{ℚ(√5)/ℚ}(α_NP) = α_RH`        — cross-sector trace law (S2)
    * `hP`     : `α_Poincaré = 1`                   — fixed elsewhere
    * `hRH`    : `α_RH = 3/2`                       — fixed elsewhere (H₃: 15/10)

    Conclusion: `α_NP = φ + (α_RH − α_Poincaré)/2 = φ + 1/4`. -/
theorem alphaNP_from_golden_sector_trace_law
    (αNP αHodge αRH αPoincare q : ℝ)
    (hHodge : αHodge = Real.goldenRatio)
    (hSector : αNP = αHodge + q)
    (hTrace : sectorTrace q = αRH)
    (hP : αPoincare = 1)
    (hRH : αRH = 3 / 2) :
    αNP = Real.goldenRatio + (αRH - αPoincare) / 2 ∧
    αNP = Real.goldenRatio + 1 / 4 := by
  have hq : q = (αRH - 1) / 2 := trace_pins_offset q αRH hTrace
  constructor
  · rw [hSector, hHodge, hq, hP]
  · rw [hSector, hHodge, hq, hRH]; norm_num

/-- **The `+1/4` restated with zero NP-specific input.**
    `1/4 = (α_RH − α_Poincaré) / [ℚ(√5):ℚ]`, i.e. half the framework's own
    "critical-line offset" `α_RH − α_Poincaré = 1/2`. -/
theorem quarter_is_half_the_critical_line_offset :
    ((3 : ℝ) / 2 - 1) / 2 = 1 / 4 := by norm_num

/-! ## §4 — The quadratic `16x² − 24x − 11` IS `(2x − α_RH)² = 5` -/

/-- **★ The NP quadratic is exactly the (trace, discriminant) statement.**
    `16x² − 24x − 11 = 0 ↔ (2x − 3/2)² = 5`, i.e.
    `(2x − α_RH)² = disc ℚ(√5)`. -/
theorem NP_quadratic_iff_trace_disc (x : ℝ) :
    16 * x ^ 2 - 24 * x - 11 = 0 ↔ (2 * x - 3 / 2) ^ 2 = 5 := by
  constructor <;> intro h <;> nlinarith [h]

/-- **The coefficients are functions of `(T, D) = (α_RH, 5)`.**
    From `4x² − 4Tx + (T² − D) = 0`, scaling by 4:
    `16x² − 16T·x + (4T² − 4D) = 0`. With `T = 3/2`, `D = 5`:
    `16·T = 24` and `4D − 4T² = 11`. Nothing else enters. -/
theorem NP_quadratic_coefficients_from_trace_disc (T D x : ℝ) :
    (2 * x - T) ^ 2 = D ↔ 16 * x ^ 2 - 16 * T * x + (4 * T ^ 2 - 4 * D) = 0 := by
  constructor <;> intro h <;> nlinarith [h]

/-- `16·α_RH = 24` and `4·5 − 4·α_RH² = 11`: the two "mystery" integers. -/
theorem NP_quadratic_integers_explained :
    (16 : ℝ) * (3 / 2) = 24 ∧ 4 * (5 : ℝ) - 4 * (3 / 2) ^ 2 = 11 := by
  norm_num

/-- The discriminant `1280 = 16² · 5` — the golden discriminant `5` times the
    squared normalisation `16`. The `2⁸` is bookkeeping; the `5` is the field. -/
theorem NP_quadratic_discriminant : (24 : ℝ) ^ 2 + 4 * 16 * 11 = 16 ^ 2 * 5 := by
  norm_num

/-- **The trace law forces the quadratic** (not the other way round). -/
theorem trace_law_forces_NP_quadratic (q : ℝ) (hTrace : sectorTrace q = 3 / 2) :
    16 * (sectorElt q) ^ 2 - 24 * (sectorElt q) - 11 = 0 := by
  have hq : q = 1 / 4 := by
    have := trace_pins_offset q (3 / 2) hTrace; linarith
  unfold sectorElt
  rw [hq]
  linear_combination (16 : ℝ) * Real.goldenRatio_sq

/-! ## §5 — `φ + 1/4` is not an algebraic integer of ℚ(√5) -/

/-- **★★ `α_NP ∉ ℤ[φ]`.** There are no integers `a, b` with
    `a + b·φ = φ + 1/4`.

    `ℤ[φ]` is the ring of integers of `ℚ(√5)`, and it contains *every*
    quantity the H₃ Coxeter data produces: the Cartan-matrix entries
    (`2cos(π/5) = φ`, `1`, `2`), the eigenvalues of the Coxeter element in
    the maximal real subfield of `ℚ(ζ₁₀)`, the character values of
    `H₃ ≅ ℤ/2 × A₅`, and the root coordinates. Consequently **no
    ℤ-polynomial combination of H₃ invariants equals `α_NP`.** Any
    derivation must introduce a division by 4, and H₃ supplies no
    canonical such division — which is exactly why the
    "`1/4 = 1/(H₃ exponent gap)`" match is a fit and not a derivation. -/
theorem alphaNP_not_algebraic_integer :
    ¬ ∃ a b : ℤ, (a : ℝ) + (b : ℝ) * Real.goldenRatio
        = Real.goldenRatio + 1 / 4 := by
  rintro ⟨a, b, h⟩
  rcases eq_or_ne b 1 with hb | hb
  · subst hb
    push_cast at h
    have h4 : ((4 * a : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by push_cast; linarith
    have : (4 * a : ℤ) = 1 := by exact_mod_cast h4
    omega
  · have hb' : ((b : ℝ) - 1) ≠ 0 := by
      intro hc
      apply hb
      have : ((b : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hden : (((4 * (b - 1) : ℤ)) : ℝ) ≠ 0 := by
      push_cast
      intro hc
      exact hb' (by linarith)
    have key : Real.goldenRatio
        = (((1 - 4 * a : ℤ)) : ℝ) / (((4 * (b - 1) : ℤ)) : ℝ) := by
      rw [eq_div_iff hden]
      push_cast
      linear_combination (4 : ℝ) * h
    exact Real.goldenRatio_irrational.ne_rational (1 - 4 * a) (4 * (b - 1)) key

/-! ## §6 — IMPOSSIBILITY: α_NP is independent of the stated postulates -/

/-- The framework's cross-Millennium α-skeleton
    (`CrossMillenniumSharedInvariants.cross_millennium_shared_invariants_capstone`)
    with clause (10) `α_NP − α_Hodge = 1/4` **removed** — that clause is the
    only one of the eleven that mentions `α_NP`, and it is definitionally the
    value being tested. Every *other* stated constraint that mentions `α_NP`
    is retained:

    * `np_pos`      — positivity (from `PolylogEigenvalueConjecture`);
    * `np_ne_alphaP`— distinctness, the entire content of
                      `AlphaRealizationNoGo`;
    * `np_coupling` — the universal coupling `λ₀·α_NP = π/10`. -/
structure AlphaSkeletonWithoutNPClause where
  αPoincare : ℝ
  αP : ℝ
  αNP : ℝ
  αRH : ℝ
  αNS : ℝ
  αYM : ℝ
  αBSD : ℝ
  αHodge : ℝ
  αQG : ℝ
  lam : ℝ
  inv_P_sq : αP ^ 2 = αYM
  inv_RH_sq : αRH ^ 2 = 9 / 4
  inv_QG_sq : αQG ^ 2 = 2 * Real.pi
  inv_Hodge_sq : αHodge ^ 2 = αHodge + 1
  inv_NS_two_BSD : αNS = 2 * αBSD
  inv_NS_YM_BSD : αNS = αYM * αBSD
  inv_YM_succ : αYM = αPoincare + 1
  inv_RH_NS : αRH * αNS = αNS + αBSD
  inv_RH_YM : αRH * αYM = 3
  inv_QG_YM_pi : αQG ^ 2 = αYM * Real.pi
  np_pos : 0 < αNP
  np_ne_alphaP : αNP ≠ αP
  np_coupling : lam * αNP = Real.pi / 10

/-- **★★★ IMPOSSIBILITY THEOREM.**

    For **every** real `r > 0` with `r ≠ √2` there is a model of the entire
    stated α-skeleton (minus the definitional NP clause) in which
    `α_NP = r`, with all other nine α-values at their canonical framework
    values.

    Therefore: the framework's stated postulates **do not determine α_NP**.
    The pin `α_NP = φ + 1/4` is an axiom or an empirical input; it is not a
    consequence of anything else the framework asserts. -/
theorem alphaNP_unconstrained (r : ℝ) (hr : 0 < r) (hne : r ≠ Real.sqrt 2) :
    ∃ S : AlphaSkeletonWithoutNPClause, S.αNP = r := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hQG : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  refine ⟨{ αPoincare := 1
            αP := Real.sqrt 2
            αNP := r
            αRH := 3 / 2
            αNS := 3 * Real.pi / 2
            αYM := 2
            αBSD := 3 * Real.pi / 4
            αHodge := Real.goldenRatio
            αQG := Real.sqrt (2 * Real.pi)
            lam := Real.pi / (10 * r)
            inv_P_sq := h2
            inv_RH_sq := by norm_num
            inv_QG_sq := hQG
            inv_Hodge_sq := Real.goldenRatio_sq
            inv_NS_two_BSD := by ring
            inv_NS_YM_BSD := by ring
            inv_YM_succ := by norm_num
            inv_RH_NS := by ring
            inv_RH_YM := by norm_num
            inv_QG_YM_pi := hQG
            np_pos := hr
            np_ne_alphaP := hne
            np_coupling := by field_simp }, rfl⟩

/-- **Two models with different `α_NP`** — the independence made concrete. -/
theorem alphaNP_not_determined :
    ∃ S T : AlphaSkeletonWithoutNPClause, S.αNP ≠ T.αNP := by
  have hs2lt : Real.sqrt 2 < 3 / 2 := by
    have h : Real.sqrt 2 < Real.sqrt (9 / 4) :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num,
         Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3 / 2)] at h
  have hs2gt : (1 : ℝ) < Real.sqrt 2 := by
    have h : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_one] at h
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    have h : Real.sqrt 4 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num,
         Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h
  have hφgt : (3 / 2 : ℝ) < Real.goldenRatio := by
    have hdef : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
    linarith
  obtain ⟨S, hS⟩ := alphaNP_unconstrained 1 (by norm_num) (by intro hc; linarith)
  obtain ⟨T, hT⟩ := alphaNP_unconstrained (Real.goldenRatio + 1 / 4)
    (by linarith) (by intro hc; linarith)
  exact ⟨S, T, by rw [hS, hT]; intro hc; linarith⟩

/-! ## §7 — The corpus's bare-GF reality route: the sin-branch is dead -/

/-- `π·(φ + 1/4)` is not an integer multiple of `π`, hence
    `sin(π·(φ + 1/4)) ≠ 0`: **branch (i) of
    `bare_route_structural_finding` is eliminated at `α_NP`.** -/
theorem sin_pi_alphaNP_ne_zero :
    Real.sin (Real.pi * (Real.goldenRatio + 1/4)) ≠ 0 := by
  intro h
  rw [Real.sin_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hval : Real.goldenRatio + 1/4 = (n : ℝ) := by
    field_simp at hn ⊢
    nlinarith [hn, Real.pi_pos]
  have key : Real.goldenRatio = (((4 * n - 1 : ℤ)) : ℝ) / (((4 : ℤ)) : ℝ) := by
    rw [eq_div_iff (by norm_num : (((4 : ℤ)) : ℝ) ≠ 0)]
    push_cast
    linarith
  exact Real.goldenRatio_irrational.ne_rational (4 * n - 1) 4 key

/-- **★ At `α_NP` the bare reality condition can only survive via the cosine
    branch.** Combined with the corpus's
    `bare_route_structural_finding`, if `Im β = 0` held at `α_NP` then
    necessarily `cos(π·α_NP) = −1/2` — which forces `α_NP ∈ 2/3 + 2ℤ` or
    `α_NP ∈ 4/3 + 2ℤ`, i.e. rational. So the bare weighted-`G_n` route
    remains machine-checked incompatible with `α_NP = φ + 1/4`. -/
theorem bare_route_at_alphaNP_forces_cos_branch
    (h : PrincipiaTractalis.TuringEncoding.betaIm (Real.goldenRatio + 1/4) = 0) :
    Real.cos (Real.pi * (Real.goldenRatio + 1/4)) = -1/2 := by
  rcases PrincipiaTractalis.TuringEncoding.bare_route_structural_finding _ h with hs | hc
  · exact absurd hs sin_pi_alphaNP_ne_zero
  · exact hc

/-! ## §8 — Honest-scope capstone -/

/-- **What this file does and does not establish.**

    DOES (all axiom-free):
    1. the universal coupling constrains nothing (§1);
    2. the π/10 ↔ H₃ thread yields `φ` uniquely and excludes `φ + 1/4` (§2);
    3. `α_NP` follows from `α_Hodge`, `α_RH`, `α_Poincaré` plus the two
       structural postulates (unit φ-modulation, Galois trace) with **no
       NP-specific free parameter** (§3);
    4. `16x² − 24x − 11` is exactly `(2x − α_RH)² = 5` (§4);
    5. `φ + 1/4 ∉ ℤ[φ]`, so no ℤ-combination of H₃ data reaches it (§5);
    6. **the stated postulates do not determine `α_NP`: every `r > 0`,
       `r ≠ √2`, extends to a full model** (§6);
    7. the bare-GF reality route's sin-branch is dead at `α_NP` (§7).

    DOES NOT:
    * derive `α_NP` from self-adjointness, trace-class, or any spectral
      property of a Hamiltonian;
    * supply an independent motivation for the trace law (S2);
    * over-determine `α_NP` (S1 + S2 are exactly 2 conditions on 2 degrees
      of freedom). -/
theorem alpha_NP_derivation_attempt_r122_honest_scope : True := trivial

end PrincipiaFractalis.AlphaNPDerivationAttempt_r122

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaFractalis.AlphaNPDerivationAttempt_r122.coupling_determines_no_alpha
#print axioms
  PrincipiaFractalis.AlphaNPDerivationAttempt_r122.icosahedral_self_consistency_forces_goldenRatio
#print axioms
  PrincipiaFractalis.AlphaNPDerivationAttempt_r122.alphaNP_from_golden_sector_trace_law
#print axioms PrincipiaFractalis.AlphaNPDerivationAttempt_r122.trace_law_forces_NP_quadratic
#print axioms PrincipiaFractalis.AlphaNPDerivationAttempt_r122.alphaNP_not_algebraic_integer
#print axioms PrincipiaFractalis.AlphaNPDerivationAttempt_r122.alphaNP_unconstrained
#print axioms PrincipiaFractalis.AlphaNPDerivationAttempt_r122.alphaNP_not_determined
#print axioms PrincipiaFractalis.AlphaNPDerivationAttempt_r122.bare_route_at_alphaNP_forces_cos_branch
