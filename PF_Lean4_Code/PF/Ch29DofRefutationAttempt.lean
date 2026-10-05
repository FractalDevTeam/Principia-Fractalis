/-
# Ch 29 Degrees-of-Freedom Refutation (2026-10-05)

`ch29_observational_tests.tex` reports a global cosmological fit assembled from
three components. Its degrees-of-freedom accounting for the CMB component is
impossible, and this file proves it two ways — the second requiring no
assumption at all about which dataset is meant.

## The figures, as printed

| component | ΛCDM dof | modified dof | change |
|---|---|---|---|
| supernovae (`:132`, `:139`) | `580 − 6 = 574` | `580 − 8 = 572` | `−2` |
| BAO (`:272`, `:277`) | `13 − 6 = 7` | `13 − 8 = 5` | `−2` |
| CMB, primary fit (`:343`) | `52` | `50` | `−2` |
| **CMB, in the global sum** (`:391`, `:397`) | **`9`** | **`11`** | **`+2`** |

The modified model adds exactly two parameters (`:73–79`), and
`dof = N_data − N_param`, so every component must *lose* two. The global CMB
entry is the only one in the chapter that gains two.

## Argument 1 — the chapter's own convention

Three of four components obey `mod_dof = ΛCDM_dof − 2`. The fourth does not.
Since `N_data` is fixed between the two fits of a given dataset and `N_param`
only grows, `dof` cannot increase. `9 → 11` is therefore inconsistent with the
convention the chapter itself applies everywhere else.

## Argument 2 — no dataset size works, so no reading rescues it

This is the decisive one, and it assumes nothing about which CMB dataset enters
the global sum:

* `N − 6 = 9` forces `N = 15`, and then `N − 8 = 7`, not `11`.
* `N − 8 = 11` forces `N = 19`, and then `N − 6 = 13`, not `9`.

**There is no `N_data` for which both printed figures are correct.** So the
pair cannot be repaired by reinterpreting the dataset — not as primary CMB, not
as late-time ISW/lensing, not as any subset. One of the two numbers is wrong
whatever the dataset is. `no_common_data_count` below is that statement.

## What is NOT determined here

The chapter never gives `N_data` or `N_param` for *any* CMB dof — unlike
supernovae (`580 − 6/8`) and BAO (`13 − 6/8`), which are shown in full. The
figures `52`, `50`, `9`, `11` and a third "effective `N_dof ≈ 60`" at `:326`
are all asserted without derivation. **So the correct replacement values are
not recoverable from the text**, only the fact that `9/11` cannot both stand.
Supplying them is an authorial item.

Note also that the two χ²/dof ratios, `1.165` and `0.603`, are arithmetically
consistent with the erroneous `590/588`, so they are not independent errors —
they inherit, and will need recomputing once the dof are fixed.

## Three further arithmetic slips, same chapter

1. `:369` — `Δχ²_CMB,late` printed as `51.4`, but `58.4 − 6.9 = 51.5`. Does not
   propagate: the Total-CMB `Δχ² = 51.4` at `:376` is computed directly from
   `104.6 − 53.2` and is correct.
2. `:405` — the displayed formula is
   `(χ²_ΛCDM − χ²_mod)/χ²_ΛCDM`, which gives `333.1/687.3 = 48.47 %`, but the
   substitution printed beside it is `333.1/354.2 = 94.04 %`, i.e. it divides by
   `χ²_mod`. The *substitution* matches the chapter's practice elsewhere — the
   jackknife improvements at `:577–590` all use `Δχ²/χ²_mod` — so the formula
   is what is mislabelled. Worth stating plainly: `Δχ²/χ²_mod` is not what
   "percentage improvement" conventionally denotes and can exceed `100 %`.
3. `:437–439` — BIC: `687.3 + 6 ln 590 = 725.58` (printed `725.0`),
   `354.2 + 8 ln 588 = 405.21` (printed `405.4`), `ΔBIC = 320.37` (printed
   `319.6`). The conclusion `ΔBIC ≫ 10` is unaffected.

## Scope

Arithmetic and accounting only. No rigor-ledger label moves; ch29's fits are
already filed as EMPIRICAL HYPOTHESIS — untested.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch29Refutation

/-! ## §1 — Degrees of freedom -/

/-- Degrees of freedom of a fit: data points minus fitted parameters. Taken in
    `ℤ` so that over-parameterised fits are representable rather than
    truncated. -/
def dof (nData nParam : ℕ) : ℤ := (nData : ℤ) - (nParam : ℤ)

/-- **Adding parameters strictly reduces degrees of freedom.** The structural
    fact the chapter's global CMB entry violates. -/
theorem dof_drops_by_params_added (nData nParam k : ℕ) :
    dof nData (nParam + k) = dof nData nParam - (k : ℤ) := by
  unfold dof; push_cast; ring

/-- The chapter's supernova component obeys the convention. -/
theorem SN_obeys_convention : dof 580 8 = dof 580 6 - 2 := by
  unfold dof; norm_num

/-- The chapter's BAO component obeys the convention. -/
theorem BAO_obeys_convention : dof 13 8 = dof 13 6 - 2 := by
  unfold dof; norm_num

/-! ## §2 — The decisive statement: no dataset size works -/

/-- **★ No `N_data` makes both printed CMB figures correct. ★**

    The global fit assigns the CMB component `9` degrees of freedom under
    ΛCDM (`6` parameters) and `11` under the modified model (`8` parameters).
    There is no data count consistent with both.

    This settles the question without any assumption about which CMB dataset
    enters the global sum: whatever it is, one of the two numbers is wrong. -/
theorem no_common_data_count :
    ¬ ∃ n : ℕ, dof n 6 = 9 ∧ dof n 8 = 11 := by
  rintro ⟨n, h6, h8⟩
  unfold dof at h6 h8
  omega

/-- The same obstruction stated as the sign of the change: the printed pair
    moves dof the wrong way. -/
theorem printed_change_has_wrong_sign : (11 : ℤ) - 9 = 2 ∧ (0 : ℤ) < 11 - 9 := by
  norm_num

/-! ## §3 — The three arithmetic slips -/

/-- **(1)** `Δχ²_CMB,late` is `51.5`, not the printed `51.4`. -/
theorem late_time_delta_chisq :
    (584 / 10 : ℝ) - (69 / 10 : ℝ) = (515 / 10 : ℝ) ∧
    (515 / 10 : ℝ) ≠ (514 / 10 : ℝ) := by
  constructor <;> norm_num

/-- **(2)** The displayed percentage formula and its substitution disagree:
    dividing `Δχ²` by `χ²_ΛCDM` is not dividing it by `χ²_mod`, and the two
    differ by almost a factor of two. -/
theorem percentage_formula_mismatch :
    (3331 / 10 : ℝ) / (6873 / 10 : ℝ) ≠ (3331 / 10 : ℝ) / (3542 / 10 : ℝ) ∧
    (3331 / 10 : ℝ) / (6873 / 10 : ℝ) < (1 / 2 : ℝ) ∧
    (9 / 10 : ℝ) < (3331 / 10 : ℝ) / (3542 / 10 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-! ## §4 — Capstone -/

/-- **★ Ch 29 degrees-of-freedom refutation capstone ★**

    Adding parameters reduces degrees of freedom; the supernova and BAO
    components obey that; and no data count makes the global fit's CMB pair
    `9 / 11` consistent. Together with the two arithmetic slips, the chapter's
    global-fit accounting does not stand as printed. -/
theorem Ch29DofRefutation_capstone :
    (∀ nData nParam k : ℕ,
      dof nData (nParam + k) = dof nData nParam - (k : ℤ)) ∧
    dof 580 8 = dof 580 6 - 2 ∧
    dof 13 8 = dof 13 6 - 2 ∧
    (¬ ∃ n : ℕ, dof n 6 = 9 ∧ dof n 8 = 11) ∧
    ((584 / 10 : ℝ) - (69 / 10 : ℝ) = (515 / 10 : ℝ)) :=
  ⟨dof_drops_by_params_added,
   SN_obeys_convention,
   BAO_obeys_convention,
   no_common_data_count,
   late_time_delta_chisq.1⟩

/-! ## §5 — Non-vacuity -/

/-- Non-vacuity for `no_common_data_count`: the shape of hypothesis it denies
    is satisfiable in general, witnessed by a consistent pair. With `15` data
    points and the chapter's parameter counts the dof are `9` and `7`, so the
    first clause is achievable and it is specifically `11` that fails. -/
theorem consistent_pair_exists : dof 15 6 = 9 ∧ dof 15 8 = 7 := by
  unfold dof; norm_num

end PrincipiaTractalis.Ch29Refutation

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch29Refutation.dof_drops_by_params_added
#print axioms PrincipiaTractalis.Ch29Refutation.no_common_data_count
#print axioms PrincipiaTractalis.Ch29Refutation.late_time_delta_chisq
#print axioms PrincipiaTractalis.Ch29Refutation.percentage_formula_mismatch
#print axioms PrincipiaTractalis.Ch29Refutation.Ch29DofRefutation_capstone
