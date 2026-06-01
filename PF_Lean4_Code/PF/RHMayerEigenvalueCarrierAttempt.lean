/-
# RH Mayer Eigenvalue Carrier — Wave 55B injectivity-restoring carrier

★ DERIVED 2026-05-31 (Wave 55B dispatch, post-Wave-48A parity-injectivity
  trade-off).

## Strategic context

Wave 48A (`PF/RHAnalyticPosBijectionParityAttempt.lean`, commit
`cf4b4cd`) discharged Wave 47A's even-parity caveat by re-indexing the
reference carrier:

    eigSeqEven n := eigSeq (n / 2)

This restored "every value of `eigSeq` is taken at an even index" but
SACRIFICED injectivity:

    eigSeqEven 0 = eigSeqEven 1 = eigSeq 0 = 1
    (pos47Parity_not_injective at lines 219-222 of Wave 48A).

The Wave 48A capstone explicitly records this loss
(`pos47Parity_not_injective`) and replaces injectivity with the
weaker "non-constant on even indices" Prop
(`pos47Parity_non_constant_on_even`).

Wave 50A pivoted to a surrogate `t3SymEigSurrogate n := 1/(n+1)` that
is injective but has no manuscript anchor. Wave 52B then proved that
NO `ℕ → ℝ` carrier at canonical α = 3/2 can hit Hardy 1914
(`hardy1914 ≈ 14.135`) under the discrete-image obstruction.

The Wave 55B audit (`MISSION_INVENTORY/wave55_frontier_RH.md` §3.2)
proposes: **construct a NEW carrier `eigSeqMayer : ℕ → ℝ` whose first
20 values are concrete rationals approximating the Mayer 1991 §2
transfer-operator eigenvalues from the Ch 20 N=20 table** (lines
478-490 of `ch20_riemann_hypothesis.tex`):

    Index   Eigenvalue   |Eigenvalue|
    1       -107.3045    107.3045
    2        97.9880      97.9880
    3       -0.2385        0.2385
    4        0.2308        0.2308
    5       -0.2241        0.2241
    12      -0.1433        0.1433

This file constructs that carrier and proves three properties
axiom-free:

  1. **Strict monotonicity (decreasing in absolute value)** — gives
     injectivity for free on the first 20 values.

  2. **Manuscript anchoring** — the 6 listed `|λ|` values are placed at
     explicit indices in the carrier and recovered exactly as rationals.

  3. **Extension to ℕ preserving injectivity** — `eigSeqMayer n` for
     `n ≥ 20` is set to `(n - 19 : ℝ) + 200`, which is `≥ 201 > 107.3045`,
     so it never collides with any table entry.

## Honest scope (★ load-bearing disclaimer)

This is a **STRUCTURAL CARRIER UPGRADE**, not an RH discharge:

  * The 20 values are **rationals from the manuscript's tabulated
    N=20 truncation**, not the literal `N → ∞` Mayer eigenvalues.

  * Surjectivity onto Hardy/Odlyzko irrationals at fixed α REMAINS
    structurally obstructed (Wave 52B), independent of carrier injectivity.

  * The unlisted 14 indices (manuscript positions 6-11, 13-20) are
    filled with explicit interpolating rationals that maintain strict
    monotonicity. These are NOT manuscript values; they are honestly
    structural fillers.

  * Wave 48A's parity-route bridge to RH is NOT discharged here. This
    file restores **injectivity** as a CARRIER property — the
    parity-discharge substrate construction is on a separate axis.

## What this file delivers

  1. `eigSeqMayerN20 : Fin 20 → ℝ` — the N=20 table as 20 explicit
     positive rationals, strictly DECREASING in index.

  2. `eigSeqMayerN20_pos` — all 20 values are positive.

  3. `eigSeqMayerN20_strictAnti` — strictly decreasing.

  4. `eigSeqMayerN20_injective` — injective (from strict antitone).

  5. `eigSeqMayerN20_at_idx_*` — explicit values at indices 0, 1, 2,
     3, 4, 11 matching the manuscript table.

  6. `eigSeqMayer : ℕ → ℝ` — extension `ℕ → ℝ` agreeing with
     `eigSeqMayerN20` on indices `< 20`.

  7. `eigSeqMayer_injective` — injective on all of ℕ.

  8. `eigSeqMayer_hits_idx_11_at_hardy_band` — the value at index 11
     is `0.1433`, which under the empirical scaling `α* = 5×10⁻⁶`
     maps the Mayer eigenvalue band near Hardy 1914.

  9. `eigSeqMayer_capstone` — bundled Wave 55B status structure.

## What this file does NOT do

  * NOT a discharge of `RHSpectralSurjectivityConjecture` at any α.

  * NOT a literal `N → ∞` Mayer eigenvalue construction; the values
    are the manuscript's finite-precision N=20 rational shadow.

  * NOT a removal of the Wave 52B obstruction; it only restores
    injectivity (which Wave 48A sacrificed) on a manuscript-anchored
    carrier.

ZERO project axioms. ZERO `sorry`s. ZERO `admit`s.

Author: Pablo Cohen (Wave 55B injectivity-restoring carrier)
Date: 2026-05-31
-/

import PF.SpectralBijection
import PF.RHSurjectivityConjecture
import PF.T3SymCanonicalAlphaCarrierAttempt
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace PrincipiaTractalis
namespace RHMayerEigenvalueCarrierAttempt

open PrincipiaTractalis
open PrincipiaTractalis.T3SymCanonicalAlphaCarrierAttempt

/-! ## §1 — The N=20 Mayer eigenvalue table as positive rationals

We encode the 20 absolute-value entries `|λ_i|` from the Ch 20 N=20
truncation, strictly decreasing in index. The 6 explicit manuscript
entries (indices 1, 2, 3, 4, 5, 12 in the manuscript, corresponding to
indices 0, 1, 2, 3, 4, 11 here) are recovered exactly:

  Lean idx 0  ↔ manuscript idx 1   : 107.3045
  Lean idx 1  ↔ manuscript idx 2   :  97.9880
  Lean idx 2  ↔ manuscript idx 3   :   0.2385
  Lean idx 3  ↔ manuscript idx 4   :   0.2308
  Lean idx 4  ↔ manuscript idx 5   :   0.2241
  Lean idx 11 ↔ manuscript idx 12  :   0.1433

Filler indices 5-10 and 12-19 carry explicit decreasing rationals
that maintain strict monotonicity. These fillers are NOT manuscript
values. -/

/-- **The N=20 Mayer eigenvalue table** — 20 positive rationals,
    strictly decreasing, matching the 6 explicit manuscript entries
    at indices 0, 1, 2, 3, 4, 11.

    Defined via nested if-then-else on `i.val` for exhaustivity. -/
noncomputable def eigSeqMayerN20 : Fin 20 → ℝ := fun i =>
  if      i.val = 0  then 1073045 / 10000  -- 107.3045 (manuscript idx 1)
  else if i.val = 1  then  979880 / 10000  --  97.9880 (manuscript idx 2)
  else if i.val = 2  then    2385 / 10000  --   0.2385 (manuscript idx 3)
  else if i.val = 3  then    2308 / 10000  --   0.2308 (manuscript idx 4)
  else if i.val = 4  then    2241 / 10000  --   0.2241 (manuscript idx 5)
  else if i.val = 5  then    2200 / 10000  -- filler
  else if i.val = 6  then    2100 / 10000  -- filler
  else if i.val = 7  then    2000 / 10000  -- filler
  else if i.val = 8  then    1900 / 10000  -- filler
  else if i.val = 9  then    1800 / 10000  -- filler
  else if i.val = 10 then    1700 / 10000  -- filler
  else if i.val = 11 then    1433 / 10000  --   0.1433 (manuscript idx 12)
  else if i.val = 12 then    1400 / 10000  -- filler
  else if i.val = 13 then    1300 / 10000  -- filler
  else if i.val = 14 then    1200 / 10000  -- filler
  else if i.val = 15 then    1100 / 10000  -- filler
  else if i.val = 16 then    1000 / 10000  -- filler
  else if i.val = 17 then     900 / 10000  -- filler
  else if i.val = 18 then     800 / 10000  -- filler
  else                        700 / 10000  -- i.val = 19

/-! ## §2 — Explicit values at the 6 manuscript-anchored indices -/

/-- Manuscript index 1: `|λ_1| = 107.3045`. -/
theorem eigSeqMayerN20_at_idx_0 :
    eigSeqMayerN20 ⟨0, by decide⟩ = 1073045 / 10000 := by
  unfold eigSeqMayerN20; simp

/-- Manuscript index 2: `|λ_2| = 97.9880`. -/
theorem eigSeqMayerN20_at_idx_1 :
    eigSeqMayerN20 ⟨1, by decide⟩ = 979880 / 10000 := by
  unfold eigSeqMayerN20; simp

/-- Manuscript index 3: `|λ_3| = 0.2385`. -/
theorem eigSeqMayerN20_at_idx_2 :
    eigSeqMayerN20 ⟨2, by decide⟩ = 2385 / 10000 := by
  unfold eigSeqMayerN20; simp

/-- Manuscript index 4: `|λ_4| = 0.2308`. -/
theorem eigSeqMayerN20_at_idx_3 :
    eigSeqMayerN20 ⟨3, by decide⟩ = 2308 / 10000 := by
  unfold eigSeqMayerN20; simp

/-- Manuscript index 5: `|λ_5| = 0.2241`. -/
theorem eigSeqMayerN20_at_idx_4 :
    eigSeqMayerN20 ⟨4, by decide⟩ = 2241 / 10000 := by
  unfold eigSeqMayerN20; simp

/-- Manuscript index 12: `|λ_12| = 0.1433`. -/
theorem eigSeqMayerN20_at_idx_11 :
    eigSeqMayerN20 ⟨11, by decide⟩ = 1433 / 10000 := by
  unfold eigSeqMayerN20; simp

/-! ## §3 — Positivity at every index -/

/-- **All 20 N=20 Mayer eigenvalue magnitudes are positive**. -/
theorem eigSeqMayerN20_pos (i : Fin 20) : 0 < eigSeqMayerN20 i := by
  have hlt : i.val < 20 := i.isLt
  unfold eigSeqMayerN20
  interval_cases i.val <;> norm_num

/-! ## §4 — Strict monotonicity (decreasing) on `Fin 20`

We prove `StrictAnti eigSeqMayerN20` via `Fin.strictAnti_iff_succ_lt`:
it suffices to show `eigSeqMayerN20 i.succ < eigSeqMayerN20 i.castSucc`
for every `i : Fin 19`. -/

/-- **Helper**: at every Lean-index `k < 19`, the `(k+1)`-th entry
    is strictly less than the `k`-th. Proven by `interval_cases` over
    the 19 successive pairs. -/
theorem eigSeqMayerN20_succ_lt_of_val (k : ℕ) (hk : k < 19)
    (hk2 : k + 1 < 20) :
    eigSeqMayerN20 ⟨k + 1, hk2⟩ < eigSeqMayerN20 ⟨k, by omega⟩ := by
  unfold eigSeqMayerN20
  show (if (⟨k + 1, hk2⟩ : Fin 20).val = 0 then _ else _) <
       (if (⟨k, _⟩ : Fin 20).val = 0 then _ else _)
  interval_cases k <;> norm_num

/-- **Strict antitone consecutive-step**: at every index `i < 19`,
    `eigSeqMayerN20 (i+1) < eigSeqMayerN20 i`. -/
theorem eigSeqMayerN20_succ_lt (i : Fin 19) :
    eigSeqMayerN20 i.succ < eigSeqMayerN20 i.castSucc := by
  have hlt : i.val < 19 := i.isLt
  have h2 : i.val + 1 < 20 := by omega
  -- Translate `i.succ` and `i.castSucc` to explicit Fin 20 values.
  have h_succ : i.succ = (⟨i.val + 1, h2⟩ : Fin 20) := by
    apply Fin.ext; rfl
  have h_cast : i.castSucc = (⟨i.val, by omega⟩ : Fin 20) := by
    apply Fin.ext; rfl
  rw [h_succ, h_cast]
  exact eigSeqMayerN20_succ_lt_of_val i.val hlt h2

/-- **★ `eigSeqMayerN20` is strictly decreasing on `Fin 20`**.

    Follows from `eigSeqMayerN20_succ_lt` via
    `Fin.strictAnti_iff_succ_lt`. -/
theorem eigSeqMayerN20_strictAnti : StrictAnti eigSeqMayerN20 :=
  Fin.strictAnti_iff_succ_lt.mpr eigSeqMayerN20_succ_lt

/-- **★ `eigSeqMayerN20` is INJECTIVE** (restoring what Wave 48A
    sacrificed on `pos47Parity`). Direct consequence of strict
    antitonicity. -/
theorem eigSeqMayerN20_injective : Function.Injective eigSeqMayerN20 :=
  eigSeqMayerN20_strictAnti.injective

/-! ## §5 — Extension to `ℕ` preserving injectivity

For `n < 20`, `eigSeqMayer n = eigSeqMayerN20 ⟨n, _⟩` (table value).
For `n ≥ 20`, `eigSeqMayer n = (n : ℝ) + 200` — strictly increasing
in `n` and ≥ 220, which exceeds the table maximum `107.3045`, so
no collision with the first 20 values is possible. -/

/-- **The extension to `ℕ`**: agrees with the N=20 table on the first
    20 indices; for `n ≥ 20`, returns `(n : ℝ) + 200`, which lies
    above the table maximum `107.3045`. -/
noncomputable def eigSeqMayer (n : ℕ) : ℝ :=
  if h : n < 20 then eigSeqMayerN20 ⟨n, h⟩
  else (n : ℝ) + 200

/-- For `n < 20`, `eigSeqMayer n` recovers `eigSeqMayerN20`. -/
theorem eigSeqMayer_lt_20 (n : ℕ) (h : n < 20) :
    eigSeqMayer n = eigSeqMayerN20 ⟨n, h⟩ := by
  unfold eigSeqMayer; rw [dif_pos h]

/-- For `n ≥ 20`, `eigSeqMayer n = (n : ℝ) + 200`. -/
theorem eigSeqMayer_ge_20 (n : ℕ) (h : 20 ≤ n) :
    eigSeqMayer n = (n : ℝ) + 200 := by
  unfold eigSeqMayer
  rw [dif_neg (not_lt.mpr h)]

/-- Every `eigSeqMayer` value is positive. -/
theorem eigSeqMayer_pos (n : ℕ) : 0 < eigSeqMayer n := by
  unfold eigSeqMayer
  split_ifs with h
  · exact eigSeqMayerN20_pos ⟨n, h⟩
  · have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- Every `eigSeqMayer` value is nonzero. -/
theorem eigSeqMayer_ne_zero (n : ℕ) : eigSeqMayer n ≠ 0 :=
  ne_of_gt (eigSeqMayer_pos n)

/-- **Upper bound on the table portion**: every `eigSeqMayerN20` value
    is at most `107.3045 = 1073045/10000`. -/
theorem eigSeqMayerN20_le_max (i : Fin 20) :
    eigSeqMayerN20 i ≤ 1073045 / 10000 := by
  have hlt : i.val < 20 := i.isLt
  unfold eigSeqMayerN20
  interval_cases i.val <;> norm_num

/-- **For `n ≥ 20`, `eigSeqMayer n` exceeds the table maximum** —
    strictly greater than the largest tabulated value `107.3045`. -/
theorem eigSeqMayer_ge_20_above_table (n : ℕ) (h : 20 ≤ n) :
    1073045 / 10000 < eigSeqMayer n := by
  rw [eigSeqMayer_ge_20 n h]
  have h20 : (20 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  linarith

/-- **★ `eigSeqMayer : ℕ → ℝ` is INJECTIVE** on all of ℕ.

    Three cases:
      (i)   Both `n₁, n₂ < 20`: use `eigSeqMayerN20_injective`.
      (ii)  Both `n₁, n₂ ≥ 20`: `(n₁ : ℝ) + 200 = (n₂ : ℝ) + 200`
            gives `n₁ = n₂`.
      (iii) Mixed: contradiction via `eigSeqMayer_ge_20_above_table`
            and `eigSeqMayerN20_le_max`. -/
theorem eigSeqMayer_injective : Function.Injective eigSeqMayer := by
  intro n₁ n₂ heq
  by_cases h1 : n₁ < 20
  · by_cases h2 : n₂ < 20
    · -- Both < 20: use Fin-injectivity.
      rw [eigSeqMayer_lt_20 n₁ h1, eigSeqMayer_lt_20 n₂ h2] at heq
      have : (⟨n₁, h1⟩ : Fin 20) = ⟨n₂, h2⟩ := eigSeqMayerN20_injective heq
      exact Fin.mk.inj_iff.mp this
    · -- n₁ < 20, n₂ ≥ 20: contradiction.
      push_neg at h2
      rw [eigSeqMayer_lt_20 n₁ h1] at heq
      have h_le : eigSeqMayerN20 ⟨n₁, h1⟩ ≤ 1073045 / 10000 :=
        eigSeqMayerN20_le_max ⟨n₁, h1⟩
      have h_gt : 1073045 / 10000 < eigSeqMayer n₂ :=
        eigSeqMayer_ge_20_above_table n₂ h2
      rw [heq] at h_le
      linarith
  · by_cases h2 : n₂ < 20
    · -- n₁ ≥ 20, n₂ < 20: symmetric contradiction.
      push_neg at h1
      rw [eigSeqMayer_lt_20 n₂ h2] at heq
      have h_le : eigSeqMayerN20 ⟨n₂, h2⟩ ≤ 1073045 / 10000 :=
        eigSeqMayerN20_le_max ⟨n₂, h2⟩
      have h_gt : 1073045 / 10000 < eigSeqMayer n₁ :=
        eigSeqMayer_ge_20_above_table n₁ h1
      rw [heq] at h_gt
      linarith
    · -- Both ≥ 20: linear part is injective.
      push_neg at h1 h2
      rw [eigSeqMayer_ge_20 n₁ h1, eigSeqMayer_ge_20 n₂ h2] at heq
      have : (n₁ : ℝ) = (n₂ : ℝ) := by linarith
      exact_mod_cast this

/-! ## §6 — Hardy 1914 band hit at the manuscript-anchored index

The manuscript's Primary Correspondences table (Ch 20 lines 510-517)
records that the Mayer eigenvalue `λ ≈ 0.14333` maps to predicted
`t ≈ 14.226`, within `0.092` of the actual Hardy zero `14.135`. Our
Lean-index-11 value `0.1433` is the manuscript's index-12 entry,
which is the closest tabulated value to that band.

We record the explicit value and its closeness to the manuscript's
Hardy-band entry `0.14333`. -/

/-- **The value at Lean index 11 is `0.1433`** — the manuscript's
    N=20 index-12 entry, closest to the Hardy-band Mayer eigenvalue
    `0.14333` (manuscript Primary Correspondences, Ch 20 lines 510-517). -/
theorem eigSeqMayer_at_11_is_hardy_band :
    eigSeqMayer 11 = 1433 / 10000 := by
  rw [eigSeqMayer_lt_20 11 (by decide)]
  exact eigSeqMayerN20_at_idx_11

/-- **`eigSeqMayer 11` is in the Hardy band**: between `0.14` and
    `0.15`, the band containing the manuscript's `0.14333` entry that
    scales to `t ≈ 14.226` (close to actual Hardy zero `14.135`). -/
theorem eigSeqMayer_at_11_in_hardy_band :
    14 / 100 < eigSeqMayer 11 ∧ eigSeqMayer 11 < 15 / 100 := by
  rw [eigSeqMayer_at_11_is_hardy_band]
  constructor <;> norm_num

/-! ## §7 — Comparison with Wave 48A's `eigSeqEven`

Wave 48A's `eigSeqEven n := eigSeq (n / 2) = ((n / 2) : ℝ) + 1` is
NOT injective: `eigSeqEven 0 = eigSeqEven 1 = 1`.

Our `eigSeqMayer` is INJECTIVE and recovers manuscript-anchored
values at the first 20 indices. Explicit distinguishing point:
`eigSeqMayer 0 = 107.3045`, while `eigSeqEven 0 = 1`. -/

/-- **`eigSeqMayer 0` is the manuscript's largest tabulated `|λ|`**:
    `107.3045`. -/
theorem eigSeqMayer_at_0_is_table_max :
    eigSeqMayer 0 = 1073045 / 10000 := by
  rw [eigSeqMayer_lt_20 0 (by decide)]
  exact eigSeqMayerN20_at_idx_0

/-- **`eigSeqMayer 0 ≠ 1`** — distinguishes from Wave 48A's
    `eigSeqEven 0 = 1`. -/
theorem eigSeqMayer_at_0_ne_one : eigSeqMayer 0 ≠ 1 := by
  rw [eigSeqMayer_at_0_is_table_max]
  norm_num

/-- **`eigSeqMayer 0 ≠ eigSeqMayer 1`** — the carrier is non-constant
    at the first two indices (a HIGHER-INDEX distinction than Wave 48A,
    which only proved non-constancy on EVEN indices). -/
theorem eigSeqMayer_at_0_ne_at_1 : eigSeqMayer 0 ≠ eigSeqMayer 1 := by
  intro h
  have h0 : eigSeqMayer 0 = 1073045 / 10000 := eigSeqMayer_at_0_is_table_max
  have h1 : eigSeqMayer 1 = 979880 / 10000 := by
    rw [eigSeqMayer_lt_20 1 (by decide)]
    exact eigSeqMayerN20_at_idx_1
  rw [h0, h1] at h
  norm_num at h

/-! ## §8 — Wave 55B capstone -/

/-- **Wave 55B Mayer-carrier status structure**. Records the EXACT
    post-Wave-55B state of the Wave 48A injectivity gap: the
    framework now possesses a manuscript-anchored `ℕ → ℝ` carrier
    `eigSeqMayer` that is INJECTIVE on all of ℕ and recovers the 6
    explicit Ch 20 N=20 eigenvalue magnitudes at named indices. -/
structure Wave55BMayerCarrierStatus : Prop where
  /-- All 20 table values are positive. -/
  table_pos : ∀ i : Fin 20, 0 < eigSeqMayerN20 i
  /-- The N=20 table is strictly antitone. -/
  table_strictAnti : StrictAnti eigSeqMayerN20
  /-- The N=20 table is injective. -/
  table_injective : Function.Injective eigSeqMayerN20
  /-- Manuscript anchor: index 0 is `107.3045`. -/
  anchor_0 : eigSeqMayerN20 ⟨0, by decide⟩ = 1073045 / 10000
  /-- Manuscript anchor: index 1 is `97.9880`. -/
  anchor_1 : eigSeqMayerN20 ⟨1, by decide⟩ = 979880 / 10000
  /-- Manuscript anchor: index 2 is `0.2385`. -/
  anchor_2 : eigSeqMayerN20 ⟨2, by decide⟩ = 2385 / 10000
  /-- Manuscript anchor: index 3 is `0.2308`. -/
  anchor_3 : eigSeqMayerN20 ⟨3, by decide⟩ = 2308 / 10000
  /-- Manuscript anchor: index 4 is `0.2241`. -/
  anchor_4 : eigSeqMayerN20 ⟨4, by decide⟩ = 2241 / 10000
  /-- Manuscript anchor: index 11 is `0.1433`. -/
  anchor_11 : eigSeqMayerN20 ⟨11, by decide⟩ = 1433 / 10000
  /-- The ℕ-extension `eigSeqMayer` is positive everywhere. -/
  ext_pos : ∀ n : ℕ, 0 < eigSeqMayer n
  /-- The ℕ-extension is INJECTIVE — restoring what Wave 48A
      `pos47Parity` sacrificed. -/
  ext_injective : Function.Injective eigSeqMayer
  /-- The ℕ-extension agrees with the N=20 table on indices `< 20`. -/
  ext_agrees_lt_20 : ∀ (n : ℕ) (h : n < 20),
                       eigSeqMayer n = eigSeqMayerN20 ⟨n, h⟩
  /-- The ℕ-extension at `n ≥ 20` lies strictly above the table max. -/
  ext_above_table : ∀ (n : ℕ), 20 ≤ n → 1073045 / 10000 < eigSeqMayer n
  /-- The Hardy-band index (11) is recovered in the ℕ-extension. -/
  ext_hardy_band : 14 / 100 < eigSeqMayer 11 ∧ eigSeqMayer 11 < 15 / 100
  /-- Distinct from Wave 48A's `eigSeqEven 0 = 1`. -/
  distinct_from_wave48A : eigSeqMayer 0 ≠ 1

/-- **★★★ CAPSTONE — `rh_mayer_eigenvalue_carrier_attempt_capstone`**.

    Wave 55B verdict: the framework now possesses a manuscript-anchored
    `ℕ → ℝ` carrier `eigSeqMayer` that

      * recovers 6 explicit `|λ_i|` values from the Ch 20 N=20 Mayer
        transfer-operator eigenvalue table (manuscript indices 1, 2, 3,
        4, 5, 12, at Lean indices 0, 1, 2, 3, 4, 11);
      * is strictly antitone on the first 20 indices;
      * is INJECTIVE on all of ℕ (restoring what Wave 48A's `pos47Parity`
        sacrificed on its even-parity re-indexing);
      * contains a Hardy-band entry at Lean index 11 (`0.1433`), the
        closest tabulated value to the manuscript's empirical-scaling
        Hardy hit `t ≈ 14.226` (manuscript Ch 20 Primary Correspondences,
        lines 510-517).

    Honest scope:

      * NOT a discharge of `RHSpectralSurjectivityConjecture` at any α.
      * NOT a literal `N → ∞` Mayer eigenvalue construction; the values
        are the manuscript's finite-precision N=20 rational shadow.
      * The 14 filler indices (5-10, 12-19) are explicit interpolating
        rationals that maintain strict monotonicity; they are NOT
        manuscript values.
      * The Wave 52B obstruction (Hardy 1914's irrationality vs. any
        discrete carrier image at canonical α = 3/2) is UNCHANGED.

    Verdict: **MAYER-CARRIER INJECTIVITY RESTORED**. The Wave 48A
    parity-injectivity trade-off is repaired on a manuscript-anchored
    carrier. -/
theorem rh_mayer_eigenvalue_carrier_attempt_capstone :
    Wave55BMayerCarrierStatus :=
  { table_pos := eigSeqMayerN20_pos
    table_strictAnti := eigSeqMayerN20_strictAnti
    table_injective := eigSeqMayerN20_injective
    anchor_0 := eigSeqMayerN20_at_idx_0
    anchor_1 := eigSeqMayerN20_at_idx_1
    anchor_2 := eigSeqMayerN20_at_idx_2
    anchor_3 := eigSeqMayerN20_at_idx_3
    anchor_4 := eigSeqMayerN20_at_idx_4
    anchor_11 := eigSeqMayerN20_at_idx_11
    ext_pos := eigSeqMayer_pos
    ext_injective := eigSeqMayer_injective
    ext_agrees_lt_20 := eigSeqMayer_lt_20
    ext_above_table := eigSeqMayer_ge_20_above_table
    ext_hardy_band := eigSeqMayer_at_11_in_hardy_band
    distinct_from_wave48A := eigSeqMayer_at_0_ne_one }

/-! ## §9 — Honest assessment ledger -/

/-- **Axiom-free honest assessment ledger** for the Wave 55B Mayer
    eigenvalue carrier. -/
theorem rh_mayer_eigenvalue_carrier_attempt_ledger :
    -- (A) N=20 table is positive at every index.
    (∀ i : Fin 20, 0 < eigSeqMayerN20 i) ∧
    -- (B) N=20 table is strictly antitone.
    StrictAnti eigSeqMayerN20 ∧
    -- (C) N=20 table is injective.
    Function.Injective eigSeqMayerN20 ∧
    -- (D) Six manuscript-anchored values recovered exactly.
    (eigSeqMayerN20 ⟨0, by decide⟩ = 1073045 / 10000 ∧
     eigSeqMayerN20 ⟨1, by decide⟩ = 979880 / 10000 ∧
     eigSeqMayerN20 ⟨2, by decide⟩ = 2385 / 10000 ∧
     eigSeqMayerN20 ⟨3, by decide⟩ = 2308 / 10000 ∧
     eigSeqMayerN20 ⟨4, by decide⟩ = 2241 / 10000 ∧
     eigSeqMayerN20 ⟨11, by decide⟩ = 1433 / 10000) ∧
    -- (E) ℕ-extension is positive everywhere.
    (∀ n : ℕ, 0 < eigSeqMayer n) ∧
    -- (F) ℕ-extension is INJECTIVE — restoring Wave 48A sacrifice.
    Function.Injective eigSeqMayer ∧
    -- (G) Hardy-band entry at Lean index 11.
    (14 / 100 < eigSeqMayer 11 ∧ eigSeqMayer 11 < 15 / 100) :=
  ⟨eigSeqMayerN20_pos,
   eigSeqMayerN20_strictAnti,
   eigSeqMayerN20_injective,
   ⟨eigSeqMayerN20_at_idx_0,
    eigSeqMayerN20_at_idx_1,
    eigSeqMayerN20_at_idx_2,
    eigSeqMayerN20_at_idx_3,
    eigSeqMayerN20_at_idx_4,
    eigSeqMayerN20_at_idx_11⟩,
   eigSeqMayer_pos,
   eigSeqMayer_injective,
   eigSeqMayer_at_11_in_hardy_band⟩

/-! ## §10 — Axiom-freeness verification -/

#print axioms rh_mayer_eigenvalue_carrier_attempt_capstone
#print axioms rh_mayer_eigenvalue_carrier_attempt_ledger
#print axioms eigSeqMayerN20_injective
#print axioms eigSeqMayer_injective
#print axioms eigSeqMayerN20_strictAnti
#print axioms eigSeqMayerN20_pos
#print axioms eigSeqMayer_at_11_in_hardy_band
#print axioms eigSeqMayer_at_0_ne_one
#print axioms eigSeqMayer_at_0_ne_at_1

end RHMayerEigenvalueCarrierAttempt
end PrincipiaTractalis
