/-
# r124 — Degrees of freedom of the cross-Millennium α-web

★ NEGATIVE / STRUCTURAL RESULT 2026-07-26 ★

The corpus states eleven simultaneous algebraic invariants relating the nine
framework α-values (`PF/Referee/PrincipiaFractalisSubstrateTheorem.lean`,
conjunct `C8`; `PF/CrossMillenniumSharedInvariants.lean`, capstone), and
describes them as *rigid*: "the 9 α-values are **not free parameters**".

This file settles, machine-checked, what the eleven invariants actually
determine when they are read as a **system of simultaneous equations in nine
unknowns** rather than as a catalogue of facts about pre-chosen values.

## Results

* `alpha_web_admits_every_positive_BSD` — for **every** `t > 0` there is an
  assignment of the nine α's satisfying **all eleven invariants** with
  `αBSD = t`.  The solution set is a one-parameter family, not a point.
* `alpha_web_underdetermined` — consequently two assignments satisfying the
  identical eleven invariants disagree.  The web does **not** pin the nine
  values.
* `alpha_web_pins` — what the web *does* pin: seven of the nine α's are
  uniquely forced (`αYM = 2`, `αPoincaré = 1`, `αRH = 3/2`, `αP = √2`,
  `αHodge = φ`, `αNP = φ + 1/4`, `αQG = √(2π)`), and `αNS = 2·αBSD`.  The
  pair `(αNS, αBSD)` is forced only *up to a common positive scale*.
* `alpha_offset_is_free` — for **every** real `c` the ten invariants that do
  not mention `αNP` are satisfiable together with `αNP − αHodge = c`.  The
  constant `1/4` in invariant 10 is therefore a **free parameter of the
  system**: nothing else in the web constrains it.  (This is the formal form
  of the 2026-07-25 audit's finding, `codex/ALPHA_NP_DERIVABILITY_2026-07-25.md`.)
* `invariant_two_is_redundant` — invariant 2 (`αRH² = 9/4`) is a consequence
  of invariants 3, 9 and 11.  It carries no information.
* `invariant_eight_is_redundant` — invariant 8 (`αRH·αNS = αNS + αBSD`) is a
  consequence of invariants 3, 5, 9 and 11.

## Companion symbolic computation

`codex/alpha_web_system.py` (sympy, exact, over ℚ(π)) computes: the Gröbner
basis has 8 elements, `dim V(I) = 1` with `{αBSD}` the unique maximal
independent variable set, exactly 3 of the eleven are ideal-redundant, and the
elimination ideal `I ∩ ℚ(π)[αBSD]` is `{0}`.

## Honest scope

Nothing here refutes any invariant: all eleven are true of the framework's
values.  What is established is that they are **not jointly rigid**, and that
`αBSD = 3π/4` and the offset `1/4` are inputs the web does not supply.

## Status

Axiom-free.  No `sorry`.  `#print axioms` at the end.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import PF.IntervalArithmetic

namespace PrincipiaTractalis
namespace AlphaWebDegreesOfFreedom

open Real

/-! ## §0 — Two elementary facts reused throughout -/

/-- `φ² = φ + 1`, proved directly from `φ = (1 + √5)/2`. -/
theorem phi_sq : phi ^ 2 = phi + 1 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  unfold phi
  nlinarith [h5]

/-- `0 < φ`. -/
theorem phi_pos : 0 < phi := by
  have : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  unfold phi; linarith

/-- The positive root of `x² = x + 1` is `φ`. -/
theorem eq_phi_of_sq_eq_self_add_one {x : ℝ} (hx : 0 < x)
    (h : x ^ 2 = x + 1) : x = phi := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have h5ge : (2:ℝ) ≤ Real.sqrt 5 := by
    nlinarith [h5, Real.sqrt_nonneg 5]
  have hfac : (x - (1 + Real.sqrt 5) / 2) * (x - (1 - Real.sqrt 5) / 2) = 0 := by
    nlinarith [h5, h]
  rcases mul_eq_zero.mp hfac with h1 | h2
  · unfold phi; linarith
  · exfalso; nlinarith [h5ge]

/-! ## §1 — The α-web as an abstract system

`AlphaWebSansI10` carries the nine unknowns, the positivity hypotheses the
corpus itself uses, and the **ten** invariants of conjunct `C8` that do not
mention `αNP`.  `AlphaWeb` adds invariant 10.

Splitting the structure this way is what makes the freedom of the `1/4`
expressible: `αNP` occurs in exactly one of the eleven invariants. -/

/-- The ten invariants of `C8` that do not mention `αNP`, plus the positivity
    hypotheses used by the corpus's own rigidity theorems. -/
structure AlphaWebSansI10 where
  αPoincare : ℝ
  αP        : ℝ
  αRH       : ℝ
  αYM       : ℝ
  αHodge    : ℝ
  αNP       : ℝ
  αNS       : ℝ
  αBSD      : ℝ
  αQG       : ℝ
  αP_pos     : 0 < αP
  αHodge_pos : 0 < αHodge
  αQG_pos    : 0 < αQG
  αBSD_pos   : 0 < αBSD
  /-- I1 : `α_P² = α_YM` -/
  I1  : αP ^ 2 = αYM
  /-- I2 : `α_RH² = 9/4` -/
  I2  : αRH ^ 2 = 9 / 4
  /-- I3 : `α_QG² = 2π` -/
  I3  : αQG ^ 2 = 2 * Real.pi
  /-- I4 : `α_Hodge² = α_Hodge + 1` -/
  I4  : αHodge ^ 2 = αHodge + 1
  /-- I5 : `α_NS = 2·α_BSD` -/
  I5  : αNS = 2 * αBSD
  /-- I6 : `α_NS = α_YM·α_BSD` -/
  I6  : αNS = αYM * αBSD
  /-- I7 : `α_YM = α_Poincaré + 1` -/
  I7  : αYM = αPoincare + 1
  /-- I8 : `α_RH·α_NS = α_NS + α_BSD` -/
  I8  : αRH * αNS = αNS + αBSD
  /-- I9 : `α_RH·α_YM = 3` -/
  I9  : αRH * αYM = 3
  /-- I11 : `α_QG² = α_YM·π` -/
  I11 : αQG ^ 2 = αYM * Real.pi

/-- All eleven invariants of conjunct `C8`. -/
structure AlphaWeb extends AlphaWebSansI10 where
  /-- I10 : `α_NP − α_Hodge = 1/4` -/
  I10 : αNP - αHodge = 1 / 4

/-! ## §2 — The one-parameter family of solutions

For every positive `t` there is a full solution of the eleven invariants with
`αBSD = t`.  Only the framework's own choice `t = 3π/4` is singled out — and it
is singled out by fiat, not by the web. -/

/-- **The α-web has a solution with `α_BSD = t`, for every `t > 0`.**

    Every one of the eleven invariants holds; every positivity hypothesis
    holds.  Nothing in the system sees `t`. -/
noncomputable def webOf (t : ℝ) (ht : 0 < t) : AlphaWeb where
  αPoincare := 1
  αP        := Real.sqrt 2
  αRH       := 3 / 2
  αYM       := 2
  αHodge    := phi
  αNP       := phi + 1 / 4
  αNS       := 2 * t
  αBSD      := t
  αQG       := Real.sqrt (2 * Real.pi)
  αP_pos     := Real.sqrt_pos.mpr (by norm_num)
  αHodge_pos := phi_pos
  αQG_pos    := Real.sqrt_pos.mpr (by positivity)
  αBSD_pos   := ht
  I1  := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  I2  := by norm_num
  I3  := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.pi)
  I4  := phi_sq
  I5  := by ring
  I6  := by ring
  I7  := by norm_num
  I8  := by ring
  I9  := by norm_num
  I11 := by
    have := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.pi); linarith
  I10 := by ring

/-- **★ The eleven invariants admit EVERY positive value of `α_BSD`.** -/
theorem alpha_web_admits_every_positive_BSD :
    ∀ t : ℝ, 0 < t → ∃ W : AlphaWeb, W.αBSD = t :=
  fun t ht => ⟨webOf t ht, rfl⟩

/-- **★★★ UNDER-DETERMINATION — the eleven invariants do NOT pin the nine
    α-values.**

    Two assignments satisfying the identical eleven invariants (and identical
    positivity hypotheses) differ in `α_BSD` and in `α_NS`.  "Rigidity" is
    therefore the wrong word for the α-web: its real solution set is a
    one-parameter family, not an isolated point. -/
theorem alpha_web_underdetermined :
    ∃ W₁ W₂ : AlphaWeb, W₁.αBSD ≠ W₂.αBSD ∧ W₁.αNS ≠ W₂.αNS := by
  refine ⟨webOf 1 (by norm_num), webOf 2 (by norm_num), ?_, ?_⟩
  · show (1 : ℝ) ≠ 2
    norm_num
  · show (2 * 1 : ℝ) ≠ 2 * 2
    norm_num

/-- The framework's own assignment is one member of that family, at
    `t = 3π/4`. -/
noncomputable def frameworkWeb : AlphaWeb :=
  webOf (3 * Real.pi / 4) (by positivity)

theorem frameworkWeb_values :
    frameworkWeb.αPoincare = 1 ∧
    frameworkWeb.αP = Real.sqrt 2 ∧
    frameworkWeb.αRH = 3 / 2 ∧
    frameworkWeb.αYM = 2 ∧
    frameworkWeb.αHodge = phi ∧
    frameworkWeb.αNP = phi + 1 / 4 ∧
    frameworkWeb.αNS = 3 * Real.pi / 2 ∧
    frameworkWeb.αBSD = 3 * Real.pi / 4 ∧
    frameworkWeb.αQG = Real.sqrt (2 * Real.pi) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, by unfold frameworkWeb webOf; ring, rfl, rfl⟩

/-! ## §3 — What the web *does* pin

Seven of the nine are genuinely forced.  `α_NS` and `α_BSD` are forced only
relative to one another. -/

/-- **★ The genuine pins.**  Every solution of the eleven invariants has the
    framework's values for seven of the nine α's, and satisfies
    `α_NS = 2·α_BSD`.  The remaining freedom is exactly the common scale of
    the `(α_NS, α_BSD)` sector. -/
theorem alpha_web_pins (W : AlphaWeb) :
    W.αYM = 2 ∧
    W.αPoincare = 1 ∧
    W.αRH = 3 / 2 ∧
    W.αP = Real.sqrt 2 ∧
    W.αHodge = phi ∧
    W.αNP = phi + 1 / 4 ∧
    W.αQG = Real.sqrt (2 * Real.pi) ∧
    W.αNS = 2 * W.αBSD := by
  -- α_YM = 2 from I3 and I11, since π ≠ 0.
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hYM : W.αYM = 2 := by
    have h : W.αYM * Real.pi = 2 * Real.pi := by
      rw [← W.I11, W.I3]
    exact (mul_left_inj' hpi).mp h
  -- α_Poincaré = 1 from I7.
  have hPoi : W.αPoincare = 1 := by have := W.I7; rw [hYM] at this; linarith
  -- α_RH = 3/2 from I9.
  have hRH : W.αRH = 3 / 2 := by have := W.I9; rw [hYM] at this; linarith
  -- α_P = √2 from I1 and positivity.
  have hP : W.αP = Real.sqrt 2 := by
    have hsq : W.αP ^ 2 = 2 := by rw [W.I1, hYM]
    have : Real.sqrt (W.αP ^ 2) = Real.sqrt 2 := by rw [hsq]
    rwa [Real.sqrt_sq W.αP_pos.le] at this
  -- α_Hodge = φ from I4 and positivity.
  have hHo : W.αHodge = phi := eq_phi_of_sq_eq_self_add_one W.αHodge_pos W.I4
  -- α_NP from I10.
  have hNP : W.αNP = phi + 1 / 4 := by have := W.I10; rw [hHo] at this; linarith
  -- α_QG = √(2π) from I3 and positivity.
  have hQG : W.αQG = Real.sqrt (2 * Real.pi) := by
    have : Real.sqrt (W.αQG ^ 2) = Real.sqrt (2 * Real.pi) := by rw [W.I3]
    rwa [Real.sqrt_sq W.αQG_pos.le] at this
  exact ⟨hYM, hPoi, hRH, hP, hHo, hNP, hQG, W.I5⟩

/-- **`α_BSD` is not pinned.**  The value `3π/4` appears nowhere in the
    conclusion of `alpha_web_pins`, and by `alpha_web_admits_every_positive_BSD`
    it cannot: the eleven invariants are satisfied for every positive value.

    (The corpus's own "9 of 9" theorem
    `CrossMillenniumDerivedConsequences.alpha_system_rigidity_extended` pins
    `α_BSD` only by adding a **twelfth** hypothesis, `α_QG² = (8/3)·α_BSD`,
    which is not one of the eleven invariants of conjunct `C8`.) -/
theorem alpha_BSD_not_pinned :
    ¬ ∃ v : ℝ, ∀ W : AlphaWeb, W.αBSD = v := by
  rintro ⟨v, hv⟩
  have h1 : (1 : ℝ) = v := hv (webOf 1 (by norm_num))
  have h2 : (2 : ℝ) = v := hv (webOf 2 (by norm_num))
  norm_num [← h1] at h2

/-! ## §4 — The `1/4` is a free parameter

`α_NP` occurs in exactly one of the eleven invariants.  A variable occurring in
exactly one equation of a system is *defined* by that equation, never
constrained by it.  Formally: the other ten invariants are satisfiable
alongside `α_NP − α_Hodge = c` for **every** real `c`. -/

/-- Witness family for the freedom of the offset. -/
noncomputable def webSansI10Of (c : ℝ) : AlphaWebSansI10 where
  αPoincare := 1
  αP        := Real.sqrt 2
  αRH       := 3 / 2
  αYM       := 2
  αHodge    := phi
  αNP       := phi + c
  αNS       := 3 * Real.pi / 2
  αBSD      := 3 * Real.pi / 4
  αQG       := Real.sqrt (2 * Real.pi)
  αP_pos     := Real.sqrt_pos.mpr (by norm_num)
  αHodge_pos := phi_pos
  αQG_pos    := Real.sqrt_pos.mpr (by positivity)
  αBSD_pos   := by positivity
  I1  := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  I2  := by norm_num
  I3  := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.pi)
  I4  := phi_sq
  I5  := by ring
  I6  := by ring
  I7  := by norm_num
  I8  := by ring
  I9  := by norm_num
  I11 := by
    have := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.pi); linarith

/-- **★★★ THE `1/4` IS A FREE PARAMETER OF THE α-WEB.**

    For every real `c`, the ten invariants of conjunct `C8` other than
    invariant 10 are satisfiable — at the framework's own values of the other
    eight α's, no less — together with `α_NP − α_Hodge = c`.

    Therefore no combination of the other ten invariants constrains the offset.
    Invariant 10 does not *derive* `1/4`; it *inserts* it.  This is the clean
    impossibility statement behind the 2026-07-25 audit
    (`codex/ALPHA_NP_DERIVABILITY_2026-07-25.md`). -/
theorem alpha_offset_is_free :
    ∀ c : ℝ, ∃ W : AlphaWebSansI10, W.αNP - W.αHodge = c := by
  intro c
  refine ⟨webSansI10Of c, ?_⟩
  show phi + c - phi = c
  ring

/-- The same statement in contrapositive form: there is no real `q` such that
    the ten `αNP`-free invariants force the offset to be `q`.  In particular
    they do not force `q = 1/4`. -/
theorem alpha_offset_not_forced :
    ¬ ∃ q : ℝ, ∀ W : AlphaWebSansI10, W.αNP - W.αHodge = q := by
  rintro ⟨q, hq⟩
  have h0 : (0 : ℝ) = q := by
    have := hq (webSansI10Of 0); simpa [webSansI10Of] using this
  have h1 : (1 : ℝ) = q := by
    have := hq (webSansI10Of 1); simpa [webSansI10Of] using this
  norm_num [← h0] at h1

/-! ## §5 — Redundancy: three of the eleven carry no information

The sympy computation finds exactly three ideal-redundant invariants: I2 is
always redundant, and of `{I5, I6, I8}` any one follows from the other two
together with the rest.  Two representative cases are formalised here. -/

/-- **Invariant 2 is redundant.**  `α_RH² = 9/4` follows from I3, I11 and I9
    alone — no positivity needed. -/
theorem invariant_two_is_redundant
    {αRH αYM αQG : ℝ}
    (I3 : αQG ^ 2 = 2 * Real.pi)
    (I11 : αQG ^ 2 = αYM * Real.pi)
    (I9 : αRH * αYM = 3) :
    αRH ^ 2 = 9 / 4 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hYM : αYM = 2 := by
    have h : αYM * Real.pi = 2 * Real.pi := by rw [← I11, I3]
    exact (mul_left_inj' hpi).mp h
  rw [hYM] at I9
  nlinarith [I9]

/-- **Invariant 8 is redundant.**  `α_RH·α_NS = α_NS + α_BSD` follows from
    I3, I11, I9 and I5. -/
theorem invariant_eight_is_redundant
    {αRH αYM αNS αBSD αQG : ℝ}
    (I3 : αQG ^ 2 = 2 * Real.pi)
    (I11 : αQG ^ 2 = αYM * Real.pi)
    (I9 : αRH * αYM = 3)
    (I5 : αNS = 2 * αBSD) :
    αRH * αNS = αNS + αBSD := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hYM : αYM = 2 := by
    have h : αYM * Real.pi = 2 * Real.pi := by rw [← I11, I3]
    exact (mul_left_inj' hpi).mp h
  rw [hYM] at I9
  have hRH : αRH = 3 / 2 := by linarith
  rw [hRH, I5]; ring

/-- **Invariant 6 is redundant.**  `α_NS = α_YM·α_BSD` follows from I3, I11
    and I5. -/
theorem invariant_six_is_redundant
    {αYM αNS αBSD αQG : ℝ}
    (I3 : αQG ^ 2 = 2 * Real.pi)
    (I11 : αQG ^ 2 = αYM * Real.pi)
    (I5 : αNS = 2 * αBSD) :
    αNS = αYM * αBSD := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hYM : αYM = 2 := by
    have h : αYM * Real.pi = 2 * Real.pi := by rw [← I11, I3]
    exact (mul_left_inj' hpi).mp h
  rw [hYM, I5]

/-! ## §6 — The π-sector is a pure scale

Every invariant is homogeneous under the substitution
`(α_NS, α_BSD) ↦ (μ·α_NS, μ·α_BSD)`.  Consequently the NS/BSD sector's scale —
and in particular whether it contains `π` at all — is invisible to the web.
The statement below is the exact content of that observation. -/

/-- **★ The `(α_NS, α_BSD)` sector is only determined up to a common positive
    scale.**  Rescaling `α_NS` and `α_BSD` by any `μ > 0` maps solutions to
    solutions and changes nothing else.  In particular the `π` in
    `α_NS = 3π/2`, `α_BSD = 3π/4` is carried by the *definitions*, not by the
    invariants: the web says only `α_NS = 2·α_BSD`. -/
noncomputable def rescaleNSBSD (W : AlphaWeb) {μ : ℝ} (hμ : 0 < μ) : AlphaWeb :=
  webOf (μ * W.αBSD) (mul_pos hμ W.αBSD_pos)

theorem rescaleNSBSD_scales (W : AlphaWeb) {μ : ℝ} (hμ : 0 < μ) :
    (rescaleNSBSD W hμ).αBSD = μ * W.αBSD ∧
    (rescaleNSBSD W hμ).αNS = μ * W.αNS := by
  refine ⟨rfl, ?_⟩
  have h := (alpha_web_pins W).2.2.2.2.2.2.2   -- W.αNS = 2 * W.αBSD
  show 2 * (μ * W.αBSD) = μ * W.αNS
  rw [h]; ring

/-! ## §7 — Summary capstone -/

/-- **★★★ CAPSTONE — degrees of freedom of the α-web ★★★**

    Bundles the four load-bearing facts:

    1. the eleven invariants are **consistent** (the framework's tuple is a
       solution);
    2. they leave `α_BSD` — hence `α_NS` — **completely free** over the
       positive reals;
    3. they **do** pin the other seven α's uniquely;
    4. the offset in invariant 10 is a **free parameter**: the other ten
       invariants are compatible with `α_NP − α_Hodge = c` for every real `c`.

    Read together: the α-web is a rank-8 system in nine unknowns.  Its
    solution set is one-dimensional.  Calling it "rigid" is not accurate;
    "consistent, and pinning seven of nine up to one scale" is. -/
theorem alpha_web_degrees_of_freedom_capstone :
    -- (1) consistent
    (∃ W : AlphaWeb, W.αBSD = 3 * Real.pi / 4) ∧
    -- (2) α_BSD free
    (∀ t : ℝ, 0 < t → ∃ W : AlphaWeb, W.αBSD = t) ∧
    (¬ ∃ v : ℝ, ∀ W : AlphaWeb, W.αBSD = v) ∧
    -- (3) the other seven pinned
    (∀ W : AlphaWeb,
      W.αYM = 2 ∧ W.αPoincare = 1 ∧ W.αRH = 3 / 2 ∧ W.αP = Real.sqrt 2 ∧
      W.αHodge = phi ∧ W.αNP = phi + 1 / 4 ∧
      W.αQG = Real.sqrt (2 * Real.pi) ∧ W.αNS = 2 * W.αBSD) ∧
    -- (4) the 1/4 is free
    (∀ c : ℝ, ∃ W : AlphaWebSansI10, W.αNP - W.αHodge = c) ∧
    (¬ ∃ q : ℝ, ∀ W : AlphaWebSansI10, W.αNP - W.αHodge = q) :=
  ⟨⟨frameworkWeb, rfl⟩,
   alpha_web_admits_every_positive_BSD,
   alpha_BSD_not_pinned,
   alpha_web_pins,
   alpha_offset_is_free,
   alpha_offset_not_forced⟩

#check @alpha_web_admits_every_positive_BSD
#check @alpha_web_underdetermined
#check @alpha_web_pins
#check @alpha_BSD_not_pinned
#check @alpha_offset_is_free
#check @alpha_offset_not_forced
#check @invariant_two_is_redundant
#check @invariant_six_is_redundant
#check @invariant_eight_is_redundant
#check @alpha_web_degrees_of_freedom_capstone

#print axioms alpha_web_admits_every_positive_BSD
#print axioms alpha_web_underdetermined
#print axioms alpha_web_pins
#print axioms alpha_BSD_not_pinned
#print axioms alpha_offset_is_free
#print axioms alpha_offset_not_forced
#print axioms invariant_two_is_redundant
#print axioms invariant_six_is_redundant
#print axioms invariant_eight_is_redundant
#print axioms alpha_web_degrees_of_freedom_capstone

end AlphaWebDegreesOfFreedom
end PrincipiaTractalis
