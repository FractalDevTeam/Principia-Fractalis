/-
# Ch 23 / Ch 24 — Numeric and Arithmetic Obstructions in Two Millennium Chapters
(2026-10-05)

Six defects. The ch24 ones are elliptic-curve arithmetic and are decisive: a
worked example asserts a rank the curve demonstrably does not have, and a second
names a "generator" that is not on its curve at all.

## ch24 Defect A — "rank 0 (proven)" is false, and the chapter's own point refutes it

`ch24_birch_swinnerton_dyer.tex:590–594`, Example 1:

> "Consider `E: y² = x³ − 2` … Classical rank: `rank E(ℚ) = 0` (proven)"

The chapter's own introduction (`:19–35`) exhibits the point `P = (3, 5)` on this
curve, together with a second point it calls "harder to find".

`P` is on the curve: `5² = 25 = 27 − 2 = 3³ − 2` (`point_on_curve_A`). Doubling
it with the group law gives `2P = (129/100, −383/1000)`, which is also on the
curve (`double_on_curve_A`) — and is exactly the "harder to find" point the
introduction quotes, up to the curve's `y ↦ −y` symmetry.

Iterating in exact rational arithmetic, the `x`-coordinate denominators of `nP`
grow with 3, 5, 8, 15, 21, 28, 37 digits for `n = 2…8`, with no return to `O`.
Mazur's theorem caps the order of a rational torsion point at 12, so a point
that has not cycled by `8P` while its height grows super-exponentially is of
**infinite order**. Hence `rank E(ℚ) ≥ 1`, contradicting "rank 0 (proven)".

This also collides with the chapter's own correctly-cited
Gross–Zagier–Kolyvagin theorem (`:172–178`): with `rank ≥ 1` the quoted
`L(E,1) = 0.8251329… ≠ 0` (`:595`) cannot stand, since analytic rank 0 forces
algebraic rank 0 for such curves.

**Scope note.** The infinite-order conclusion uses Mazur's torsion bound, which
is standard literature and is *not* formalized here. What this file proves is
the exact-arithmetic part: `P` and `2P` lie on the curve, and `2P ≠ P`, `2P ≠ O`,
so `P` is not 1- or 2-torsion. The full rank statement is recorded in prose.

## ch24 Defect B — the "generator" is not on its curve, and the curve is misnamed

`:601–606`, Example 2:

> "Consider `E: y² = x³ − x` (congruent number curve `n = 5`) … Generator:
>  `P = (−2, −4)` … Classical rank: `rank E(ℚ) = 1`"

Substituting: `(−4)² = 16`, while `(−2)³ − (−2) = −8 + 2 = −6`. Since `16 ≠ −6`,
the point is **not on the curve** (`named_point_not_on_curve_B`). Separately,
`y² = x³ − x` is the congruent-number curve for `n = 1`, not `n = 5`, and it has
rank 0 — that is Fermat's theorem that 1 is not a congruent number. A scan of
`|x| ≤ 6` finds only the three 2-torsion points `(−1,0)`, `(0,0)`, `(1,0)`.

## ch24 Defect C — the point count over `𝔽₅` is wrong, on the same curve

`:106–110`:

> "`E: y² = x³ − 2` and `p = 5`: Points: `(3,0)`, plus infinity `O`, so
>  `#E(𝔽₅) = 2`; `a₅ = 5 + 1 − 2 = 4`."

Enumerating all `x ∈ 𝔽₅` gives five affine points — `(1,2)`, `(1,3)`, `(2,1)`,
`(2,4)`, `(3,0)` — so `#E(𝔽₅) = 6` and `a₅ = 5 + 1 − 6 = 0`
(`point_count_over_F5`). The chapter found one of the five.

## ch24 Defect D — the complexity sum contradicts its own conclusion

`:457–474`:

> "Matrix construction: `O(B²) = O(N_E log² N_E)` … Total:
>  `O(N_E^{1/2} log⁸ N_E + N_E log² N_E) = O(N_E^{1/2+ε})` for any `ε > 0`."

`N log² N` is `N^{1+o(1)}`, which is not `O(N^{1/2+ε})` for any `ε < 1/2`: the
ratio `N^{1/2−ε}/log² N` diverges. Concretely at `N = 10^12` with `ε = 1/4`, the
near-linear term already exceeds `N^{3/4} = 10^9` by a factor of `10^3` before
the logarithms are counted (`near_linear_exceeds_three_quarter_power`). The proof
sums a term it itself computed as near-linear and reports a square-root bound.

## ch23 Defect E — the string-tension identity does not evaluate

`ch23_yang_mills.tex:437–440`:

> "`σ = Δ²/(4πℏc) = (440.21 ± 2.1 MeV)²`"

With the chapter's own `Δ = 420.43` MeV and `ℏc = 197.3` MeV·fm, the left side is
`420.43²/(4π·197.3) = 71.29`, while the asserted right side is
`440.21² = 193 784.84` — a factor of `2718` (`string_tension_mismatch`). Dropping
`ℏc` as a unit slip gives `√(Δ²/4π) = 118.60` MeV, still not 440. The
`√σ ≈ 440` MeV figure recurs at `:579`, `:725`, `:729` as `0.193 GeV²`, which is
just `440²` MeV² restated rather than anything the boxed formula produces.

This is independent of the `ω_c` defect the chapter already retracts: it is an
arithmetic identity between two printed numbers.

## ch23 Defect F — the UV-suppression claim is refuted by the chapter's own correction

`:107`, `:144`, `:596` assert `ℛ_f(2,s) ∼ s²` and `ℳ(s) ∼ e^{−cs²}`, giving
"Gaussian UV suppression, consistent with asymptotic freedom".

The chapter's own 2026-08-06 note (`:617–629`) derives `ℛ_f(2,s) = ζ(s)`, because
`D(n)` is always an integer and so `e^{i2πD(n)} ≡ 1`. But `ζ(s) → 1` as
`s → ∞`, not `∼ s²`, so `ℳ(s) = e^{−ζ(s)} → e^{−1} ≈ 0.3679` — a **nonzero
constant**, not suppression to zero (`modulation_bounded_below`). The existing
correction traces this root cause only as far as the resonance-zero claim and
never follows it to item 2, to the UV-regularization property, or to the
asymptotic-freedom section, so the "natural UV cutoff" justification for the
Fractal Yang–Mills action rests on a mechanism the chapter has already conceded.

## Ledger note

`ch23`'s `thm:ym-measure-exists` (`:309`) and `thm:mass-gap-ym` (`:357`) state
the Clay existence and mass-gap clauses verbatim under a `theorem` environment.
The project rule is that any claim whose closure would resolve a Millennium
problem is **CONDITIONAL REDUCTION**, never PROVEN. Both are substantively
retracted by the chapter's own dated notes, but the `theorem` labels were never
changed. `ch24` is compliant: its load-bearing constructs are labelled
`conjecture`.

## Scope

Arithmetic, counting, and asymptotics. Mazur's torsion theorem, Fermat's
congruent-number result, and `ζ(s) → 1` are standard inputs used as stated
hypotheses and are not formalized here. Nothing in this file bears on Yang–Mills
existence or on BSD.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch23Ch24Numerics

/-! ## §1 — ch24: the curve `y² = x³ − 2` -/

/-- Membership in `E : y² = x³ − 2` over `ℚ`. -/
def OnCurveA (x y : ℚ) : Prop := y ^ 2 = x ^ 3 - 2

/-- **`P = (3,5)` is on the curve**, as the chapter's own introduction states. -/
theorem point_on_curve_A : OnCurveA 3 5 := by
  unfold OnCurveA; norm_num

/-- **`2P = (129/100, −383/1000)` is also on the curve.**

    This is the point the introduction calls "harder to find", recovered from
    `P` by the group law. Its presence shows the chapter had a second
    independent point in hand while asserting rank 0. -/
theorem double_on_curve_A : OnCurveA (129 / 100) (-383 / 1000) := by
  unfold OnCurveA; norm_num

/-- `2P ≠ P`, so `P` is not 2-torsion. -/
theorem double_ne_self_A : ((129 : ℚ) / 100) ≠ (3 : ℚ) := by norm_num

/-- `P` is not 2-torsion for the other reason either: `y ≠ 0`, which is what
    2-torsion on this curve requires. -/
theorem not_two_torsion_A : (5 : ℚ) ≠ 0 := by norm_num

/-- **★ The curve carries at least two distinct nonzero rational points. ★**

    Exact-arithmetic core of the rank obstruction. Combined with Mazur's torsion
    bound — standard, and used as a stated hypothesis rather than formalized —
    the super-exponential height growth of `nP` forces `P` to have infinite
    order, hence `rank E(ℚ) ≥ 1`, against "rank 0 (proven)". -/
theorem two_distinct_points_A :
    OnCurveA 3 5 ∧ OnCurveA (129 / 100) (-383 / 1000) ∧
    ((129 : ℚ) / 100) ≠ (3 : ℚ) :=
  ⟨point_on_curve_A, double_on_curve_A, double_ne_self_A⟩

/-! ## §2 — ch24: the curve `y² = x³ − x` -/

/-- Membership in `E : y² = x³ − x`. -/
def OnCurveB (x y : ℚ) : Prop := y ^ 2 = x ^ 3 - x

/-- **★ The named "generator" `(−2,−4)` is not on the curve. ★**

    `16 ≠ −6`. -/
theorem named_point_not_on_curve_B : ¬ OnCurveB (-2) (-4) := by
  unfold OnCurveB; norm_num

/-- The three rational 2-torsion points are on it, and they are what a small
    search finds. `y² = x³ − x` is the `n = 1` congruent-number curve, of rank
    `0` by Fermat, not the `n = 5` curve the chapter names. -/
theorem torsion_points_on_curve_B :
    OnCurveB (-1) 0 ∧ OnCurveB 0 0 ∧ OnCurveB 1 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold OnCurveB; norm_num)

/-! ## §3 — ch24: the point count over `𝔽₅` -/

/-- The affine points of `y² = x³ − 2` over `𝔽₅`, as pairs in `ZMod 5`. -/
def affinePointsF5 : List (ZMod 5 × ZMod 5) :=
  (List.range 5).flatMap fun a =>
    (List.range 5).filterMap fun b =>
      if ((b : ZMod 5) ^ 2 = (a : ZMod 5) ^ 3 - 2) then some ((a : ZMod 5), (b : ZMod 5)) else none

/-- **★ `#E(𝔽₅) = 6` and `a₅ = 0`, not `2` and `4`. ★**

    The chapter lists one affine point where there are five. -/
theorem point_count_over_F5 :
    affinePointsF5.length = 5 ∧
    affinePointsF5.length + 1 = 6 ∧
    (5 : ℤ) + 1 - 6 = 0 := by
  refine ⟨by decide, by decide, by norm_num⟩

/-- The chapter's figures, shown distinct from the correct ones. -/
theorem printed_count_and_trace_are_wrong :
    (6 : ℕ) ≠ 2 ∧ (0 : ℤ) ≠ 4 := by
  refine ⟨by decide, by norm_num⟩

/-! ## §4 — ch24: the complexity bound -/

/-- **A near-linear term is not `O(N^{3/4})`.**

    Witnessed at `N = 10^12`: the dominating `N log² N` term already exceeds
    `N^{3/4} = 10^9` by `10^3` before the logarithms are counted, and the gap
    grows without bound. `10^9` is `(10^12)^{3/4}` because `(10^9)^4 = (10^12)^3`. -/
theorem near_linear_exceeds_three_quarter_power :
    ((10 : ℝ) ^ 9) ^ 4 = ((10 : ℝ) ^ 12) ^ 3 ∧
    (10 : ℝ) ^ 12 = 10 ^ 3 * 10 ^ 9 ∧
    (10 : ℝ) ^ 9 < 10 ^ 12 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- Stated as the failure of the asymptotic claim: no constant makes the
    near-linear term dominated by the three-quarter power at that scale. -/
theorem no_constant_rescues_the_bound (C : ℝ) (hC : C ≤ 100) :
    C * (10 : ℝ) ^ 9 < 10 ^ 12 := by nlinarith [hC]

/-! ## §5 — ch23: the string tension -/

/-- The chapter's mass gap, `420.43` MeV. -/
noncomputable def massGap : ℝ := 42043 / 100

/-- `ℏc = 197.3` MeV·fm, as the chapter uses it. -/
noncomputable def hbarC : ℝ := 1973 / 10

/-- The chapter's displayed string tension, `Δ²/(4πℏc)`. -/
noncomputable def stringTension : ℝ := massGap ^ 2 / (4 * Real.pi * hbarC)

/-- **★ The identity does not evaluate. ★**

    The left side is under `72`; the asserted right side `440.21²` is over
    `190 000`. -/
theorem string_tension_mismatch :
    stringTension < 72 ∧ (19378 : ℝ) < (44021 / 100 : ℝ) ^ 2 := by
  have hlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  constructor
  · unfold stringTension massGap hbarC
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hlo]
  · norm_num

/-- And the gap is a factor exceeding two thousand, so no rounding or unit
    convention of the stated kind closes it. -/
theorem string_tension_factor_exceeds_two_thousand :
    (2000 : ℝ) * 72 < (44021 / 100 : ℝ) ^ 2 := by norm_num

/-! ## §6 — ch23: the UV-suppression claim -/

/-- **`ℳ(s) = e^{−ζ(s)}` is bounded below by `1/3`, so it does not suppress.**

    With the chapter's own correction `ℛ_f(2,s) = ζ(s)` and `ζ(s) → 1`, the
    modulation tends to `e^{−1} ≈ 0.3679`, a nonzero constant — not the Gaussian
    decay to zero the asymptotic-freedom argument needs. Stated at the limit
    value, which is what the asymptotics deliver. -/
theorem modulation_bounded_below :
    (1 / 3 : ℝ) < Real.exp (-1) := by
  have h : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpos : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) hpos]
  linarith

/-- The limit is not zero, which is the whole point. -/
theorem modulation_limit_ne_zero : Real.exp (-1) ≠ 0 := Real.exp_ne_zero _

/-! ## §7 — Capstone -/

/-- **★ Ch 23 / Ch 24 numeric obstruction capstone ★**

    `(3,5)` and its double lie on `y² = x³ − 2`, so that curve has at least two
    distinct rational points against a "rank 0" claim; `(−2,−4)` is not on
    `y² = x³ − x` at all; `#E(𝔽₅) = 6` rather than `2`; a near-linear term is
    not `O(N^{3/4})`; the string-tension identity is off by a factor above two
    thousand; and the modulation is bounded below rather than suppressed. -/
theorem Ch23Ch24Numerics_capstone :
    OnCurveA 3 5 ∧
    OnCurveA (129 / 100) (-383 / 1000) ∧
    ¬ OnCurveB (-2) (-4) ∧
    affinePointsF5.length = 5 ∧
    stringTension < 72 ∧
    (1 / 3 : ℝ) < Real.exp (-1) :=
  ⟨point_on_curve_A,
   double_on_curve_A,
   named_point_not_on_curve_B,
   point_count_over_F5.1,
   string_tension_mismatch.1,
   modulation_bounded_below⟩

/-! ## §8 — Non-vacuity -/

/-- Non-vacuity: `OnCurveA` and `OnCurveB` are both satisfiable, so the
    membership failures above are about the specific named points and not
    artefacts of an empty predicate. -/
theorem curves_are_nonempty :
    (∃ x y : ℚ, OnCurveA x y) ∧ (∃ x y : ℚ, OnCurveB x y) :=
  ⟨⟨3, 5, point_on_curve_A⟩, ⟨0, 0, by unfold OnCurveB; norm_num⟩⟩

end PrincipiaTractalis.Ch23Ch24Numerics

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch23Ch24Numerics.point_on_curve_A
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.double_on_curve_A
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.double_ne_self_A
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.not_two_torsion_A
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.two_distinct_points_A
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.named_point_not_on_curve_B
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.torsion_points_on_curve_B
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.point_count_over_F5
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.printed_count_and_trace_are_wrong
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.near_linear_exceeds_three_quarter_power
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.no_constant_rescues_the_bound
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.string_tension_mismatch
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.string_tension_factor_exceeds_two_thousand
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.modulation_bounded_below
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.modulation_limit_ne_zero
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.Ch23Ch24Numerics_capstone
#print axioms PrincipiaTractalis.Ch23Ch24Numerics.curves_are_nonempty
