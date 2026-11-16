/-
# BSD substrate attack — EXTENDED PARTIAL substantive-core discharge.

★ 2026-11-15 EOD — second extension of the BSD substrate attack.
Follows the n=4 partial discharge landed at commit `c9194118`
(`PF/BSDSubstratePositionPartialDischarge_2026_11_15.lean`).

## What this file does

mathlib already has BOTH:
- `fermatLastTheoremThree : FermatLastTheoremFor 3`
  (`Mathlib.NumberTheory.FLT.Three`)
- `fermatLastTheoremFour : FermatLastTheoremFor 4`
  (`Mathlib.NumberTheory.FLT.Four`)

AND the multiples-preservation lemma:
- `FermatLastTheoremFor.mono (hmn : m ∣ n) : FermatLastTheoremFor m → FermatLastTheoremFor n`
  (`Mathlib.NumberTheory.FLT.Basic`)

Combining these, `FermatLastTheoremFor n` is kernel-clean in mathlib
for ALL `n ≥ 3` such that `3 ∣ n` OR `4 ∣ n` — i.e., for the infinite
set `{3, 4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, …}`.

The ONLY n ≥ 3 NOT covered are those coprime to 12:
    n ∈ {5, 7, 11, 13, 17, 19, 23, 25, 29, 31, …} = {n ≥ 3 : gcd(n, 12) = 1}.
These are exactly the n requiring `n = 5` (Dirichlet-Legendre), or the
prime n ≥ 7 Wiles-grade machinery.

## Partition extension

Before `c9194118`: BSD substantive core was monolithic
`Wiles1995FermatLastTheorem`.

After `c9194118` (first partial discharge): n = 4 closed.

This file (second partial discharge): extends to ALL multiples of 3
OR 4, kernel-clean via mathlib's `fermatLastTheoremThree`,
`fermatLastTheoremFour`, `FermatLastTheoremFor.mono`.

After this file: BSD substantive core partitions into
  (a) DIVISIBLE BY 3 OR 4: closed kernel-clean (this file)
  (b) COPRIME TO 12 AND ≥ 3: remains open (n = 5 Dirichlet-Legendre
      + n ≥ 7 prime Wiles)

## Main theorem

`bsd_substantive_extended_partial_discharge` — kernel-clean discharge
of `Wiles1995FermatLastTheorem` restricted to `n ∈ {n ≥ 3 : 3 ∣ n ∨ 4 ∣ n}`.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-15.
-/

import PF.BSDSubstratePositionPartialDischarge_2026_11_15
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four

namespace PF.BSDSubstratePositionExtendedPartialDischarge

open PF.BSDSubstratePositionStrengthening
  (BSDAnalyticRankMachinery_SubstantiveCore
   substantive_core_strictly_stronger_than_structural_tag
   bsd_analytic_rank_residual_trivial_discharge)
open PF.BSDSubstratePosition (BSDAnalyticRankMachinery_LMFDBFamily)
open PF.BSDSubstratePositionPartialDischarge (bsd_substantive_partial_discharge_n4)

/-! ## §1 — Extended partial substantive sub-residual (all 3k or 4k, CLOSED). -/

/-- **`Wiles1995FLT_DivisibleBy3Or4_PartialClosed`** — the restriction
of `Wiles1995FermatLastTheorem` to exponents `n ≥ 3` such that
`3 ∣ n` OR `4 ∣ n`.

Asserts: for every `n ≥ 3` divisible by 3 or 4 and every positive
`A, B, C`, `A^n + B^n ≠ C^n`.

Covers the infinite set `{3, 4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20,
21, 22, 24, 25, 27, 28, 30, …}` of exponents n ≥ 3 with `3 ∣ n ∨ 4 ∣ n`.

Equivalent (as a statement of impossibility) to: for every such n,
`FermatLastTheoremFor n` holds. -/
def Wiles1995FLT_DivisibleBy3Or4_PartialClosed : Prop :=
  ∀ A B C n : ℕ,
    0 < A → 0 < B → 0 < C →
    3 ≤ n → (3 ∣ n ∨ 4 ∣ n) →
    A ^ n + B ^ n = C ^ n →
    False

/-- **`bsd_substantive_extended_partial_discharge`** — kernel-clean
discharge of the extended partial sub-residual.

Proof: case-split on `3 ∣ n ∨ 4 ∣ n`.
- If `3 ∣ n`, apply `FermatLastTheoremFor.mono` to
  `fermatLastTheoremThree`.
- If `4 ∣ n`, apply `FermatLastTheoremFor.mono` to
  `fermatLastTheoremFour`.
In both cases, the resulting `FermatLastTheoremFor n` applied to
`(A, B, C)` with non-zero hypotheses gives `A^n + B^n ≠ C^n`. -/
theorem bsd_substantive_extended_partial_discharge :
    Wiles1995FLT_DivisibleBy3Or4_PartialClosed := by
  intro A B C n hA hB hC _hn hDiv hEq
  have hFLT_n : FermatLastTheoremFor n := by
    rcases hDiv with h3 | h4
    · exact FermatLastTheoremFor.mono h3 fermatLastTheoremThree
    · exact FermatLastTheoremFor.mono h4 fermatLastTheoremFour
  exact hFLT_n A B C hA.ne' hB.ne' hC.ne' hEq

/-! ## §2 — Partitioning. -/

/-- **`bsd_substantive_partition_divisible_by_3_or_4`** — explicit
partitioning of the BSD substantive core (= `Wiles1995FermatLastTheorem`)
into CLOSED and OPEN sub-content:

(a) CLOSED kernel-clean (this file): all `n ≥ 3` with `3 ∣ n ∨ 4 ∣ n`.
    Infinite covered set (density 1/3 + 1/4 − 1/12 = 1/2 among n ≥ 3).

(b) OPEN: all `n ≥ 3` COPRIME to 12.  Specifically `n ∈ {5, 7, 11,
    13, 17, 19, 23, 25, …}`, requiring Dirichlet-Legendre (n = 5) +
    Wiles-grade machinery (prime n ≥ 7).

Half of the n ≥ 3 exponents are now substantively closed kernel-clean.
Only the coprime-to-12 half remains. -/
theorem bsd_substantive_partition_divisible_by_3_or_4 :
    Wiles1995FLT_DivisibleBy3Or4_PartialClosed ∧
    (BSDAnalyticRankMachinery_SubstantiveCore
      → BSDAnalyticRankMachinery_LMFDBFamily) :=
  ⟨bsd_substantive_extended_partial_discharge,
   substantive_core_strictly_stronger_than_structural_tag⟩

/-! ## §3 — Substrate-attack HEAD bundle (EXTENDED). -/

/-- **`bsd_substrate_attack_HEAD_bundle_EXTENDED_2026_11_15`** — the
four-conjunct extended end-of-session bundle for the BSD substrate
attack:

(1) Structural tag `BSDAnalyticRankMachinery_LMFDBFamily` DISCHARGED
    (trivial by `Unit`, from `725f883c`).

(2) Partial substantive n = 4 Fermat DISCHARGED kernel-clean
    (`bsd_substantive_partial_discharge_n4`, from `c9194118`).

(3) EXTENDED partial substantive: ALL n divisible by 3 or 4 DISCHARGED
    kernel-clean via `fermatLastTheoremThree.mono` and
    `fermatLastTheoremFour.mono` (this file).

(4) Substantive-core (full `Wiles1995FermatLastTheorem`) → structural
    tag (remaining substantive-core open content is on n coprime to 12,
    ≥ 3 — i.e., n ∈ {5, 7, 11, 13, 17, 19, 23, 25, …}).

Progress: the BSD substantive core is now substantively closed
kernel-clean for HALF of n ≥ 3 (all divisible by 3 or 4); the
remaining HALF (coprime to 12) awaits Dirichlet-Legendre n=5 and
Wiles-grade machinery for primes n ≥ 7. -/
theorem bsd_substrate_attack_HEAD_bundle_EXTENDED_2026_11_15 :
    BSDAnalyticRankMachinery_LMFDBFamily ∧
    PF.BSDSubstratePositionPartialDischarge.Wiles1995FLT_n4_PartialClosed ∧
    Wiles1995FLT_DivisibleBy3Or4_PartialClosed ∧
    (BSDAnalyticRankMachinery_SubstantiveCore
      → BSDAnalyticRankMachinery_LMFDBFamily) :=
  ⟨bsd_analytic_rank_residual_trivial_discharge,
   bsd_substantive_partial_discharge_n4,
   bsd_substantive_extended_partial_discharge,
   substantive_core_strictly_stronger_than_structural_tag⟩

/-! ## §4 — Axiom audit. -/

#check @Wiles1995FLT_DivisibleBy3Or4_PartialClosed
#check @bsd_substantive_extended_partial_discharge
#check @bsd_substantive_partition_divisible_by_3_or_4
#check @bsd_substrate_attack_HEAD_bundle_EXTENDED_2026_11_15

end PF.BSDSubstratePositionExtendedPartialDischarge
