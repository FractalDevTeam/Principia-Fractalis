/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen + Claude Opus 5 (1M context)
-/
import PF.YangMills.WilsonSectorDecomposition_2026_10_19

/-!
# `Even L` is NECESSARY for this sector decomposition — a counterexample at L = 3

`wilson_reflection_positivity_of_continuous` (r385) carries the hypothesis
`Even L`, and the frontier list records removing it as the first open direction,
with the note that it "may not be possible — a genuine lattice hypothesis, not a
formality." This file settles that, in the honest direction: **for the sector
decomposition the corpus actually uses, `Even L` is necessary, not cosmetic.**

## Where the hypothesis is really consumed

Of the 26 files mentioning `Even L`, the root is a single lemma:

  `linkSector_linkTheta (hL : Even L) (ℓ) : linkSector (linkTheta ℓ) = (linkSector ℓ).reflect`

Every other occurrence threads `hL` to reach it (`plaquette_links_plusOrZero`,
`plaquette_links_minusOrZero`, `no_straddling`, and onward to r385). It consumes
`hL` immediately, as `obtain ⟨M, hM⟩ := hL; have : L = 2 * M`.

## Why it fails for odd L, in one line

`timeReflectionSite` is `t ↦ -t`, which on `Fin L` fixes exactly those `t` with
`2t ≡ 0 (mod L)`: for even `L` that is `{0, L/2}`, for odd `L` only `{0}`. But
`linkSector` labels a spatial link `zero` when `t = 0 ∨ t = M` with
`M = L / 2` in **natural** division. For odd `L` that `M` is `(L-1)/2`, whose
reflection is `L - M = M + 1` — which `linkSector` labels `minus`. So the map
sends a `zero` link to a `minus` link while `reflect` fixes `zero`.

At `L = 3`: `M = 1`. The spatial link based at time `1` is `zero`; its reflection
sits at time `-1 = 2`, which is `minus`; and `reflect zero = zero`. Hence
`minus ≠ zero` and the intertwining relation is false. That is
`linkSector_linkTheta_false_at_three` below, decided by the kernel.

## What this does and does not establish

It establishes that `Even L` cannot be dropped from `linkSector_linkTheta` as it
stands, so no amount of proof engineering removes it from r385 while this sector
map is in use. The frontier item is therefore **not** a formality.

It does NOT show that reflection positivity fails for odd `L`. The obstruction is
in the *labelling*, not in the physics: for odd `L` the reflection has one fixed
time slice rather than two, and the honest repair is a parity-dependent `zero`
set — `{0}` for odd `L`, `{0, L/2}` for even `L` — under which `{1, …, M}` and
`{M+1, …, L-1}` have equal size `(L-1)/2` and are exchanged by `t ↦ L - t`. That
development is a separate piece of work and is not attempted here; nothing below
claims reflection positivity at any odd `L`.

SPDX-License-Identifier: Apache-2.0
-/

set_option autoImplicit false

namespace PF.YangMills

/-! ## §1 — The witness -/

/-- A lattice site on the `L = 3` lattice with time coordinate `1`. -/
def oddWitnessSite : LatticeSite 3 := fun d => if d = 0 then 1 else 0

/-- A **spatial** link (direction `1 ≠ 0`) based at time `1`, on `L = 3`. -/
def oddWitnessLink : LatticeLink 3 := (oddWitnessSite, 1)

@[simp] theorem oddWitnessSite_time : (oddWitnessSite 0).val = 1 := by decide

@[simp] theorem oddWitnessLink_spatial : oddWitnessLink.2 ≠ 0 := by decide

/-! ## §2 — The two sector labels, computed -/

/-- The witness link is labelled `zero`: at `L = 3` we have `M = L / 2 = 1`, and
the link sits at time `1 = M`, which `linkSector` declares a fixed slice. -/
theorem linkSector_oddWitness : linkSector oddWitnessLink = LinkSector.zero := by
  decide

/-- Its reflection is labelled `minus`: the reflection of time `1` is `-1 = 2`,
and `2` is neither `0` nor `M = 1`, nor `< M`. -/
theorem linkSector_linkTheta_oddWitness :
    linkSector (linkTheta oddWitnessLink) = LinkSector.minus := by
  decide

/-! ## §3 — The intertwining relation is false at L = 3 -/

/-- **`linkSector_linkTheta` fails without `Even L`.** At `L = 3` the witness
gives `minus` on the left and `reflect zero = zero` on the right. -/
theorem linkSector_linkTheta_false_at_three :
    linkSector (linkTheta oddWitnessLink)
      ≠ (linkSector oddWitnessLink).reflect := by
  decide

/-- The same statement in the shape that makes the dependency explicit: there is
a lattice size and a link for which the intertwining relation fails, so the
relation is not a theorem for all `L`. -/
theorem exists_odd_lattice_sector_reflection_failure :
    ∃ ℓ : LatticeLink 3, linkSector (linkTheta ℓ) ≠ (linkSector ℓ).reflect :=
  ⟨oddWitnessLink, linkSector_linkTheta_false_at_three⟩

/-- **`Even 3` is false**, recorded so the counterexample is visibly outside the
hypothesis of `linkSector_linkTheta` rather than contradicting it. -/
theorem three_not_even : ¬ Even 3 := by decide

/-- **The two results together.** `linkSector_linkTheta` holds under `Even L`
and fails at `L = 3`, which is odd — so `Even L` is a necessary hypothesis of
that lemma and not an artefact of its proof. -/
theorem even_hypothesis_is_necessary :
    (¬ Even 3)
      ∧ (∃ ℓ : LatticeLink 3, linkSector (linkTheta ℓ) ≠ (linkSector ℓ).reflect) :=
  ⟨three_not_even, exists_odd_lattice_sector_reflection_failure⟩

/-! ## §3b — Control: the same construction at an even `L` succeeds

Without this, the failure above could be an artefact of how the witness was
built rather than a fact about parity. -/

/-- The analogous site at `L = 4`, sitting at the fixed slice `t = M = 2`. -/
def evenWitnessSite : LatticeSite 4 := fun d => if d = 0 then 2 else 0

/-- The analogous **spatial** link at `L = 4`, based at `t = M = 2`. -/
def evenWitnessLink : LatticeLink 4 := (evenWitnessSite, 1)

/-- **CONTROL.** At `L = 4` the identically-constructed link DOES satisfy the
intertwining relation: `t = 2 = M` is labelled `zero`, its reflection is
`-2 = 2` which is again `zero`, and `reflect zero = zero`. So the failure at
`L = 3` is a fact about parity, not about the choice of witness. -/
theorem linkSector_linkTheta_holds_at_four :
    linkSector (linkTheta evenWitnessLink)
      = (linkSector evenWitnessLink).reflect := by
  decide

/-- The control and the counterexample side by side: the same construction
succeeds at `L = 4` and fails at `L = 3`. -/
theorem parity_is_the_discriminant :
    (linkSector (linkTheta evenWitnessLink)
        = (linkSector evenWitnessLink).reflect)
      ∧ (linkSector (linkTheta oddWitnessLink)
        ≠ (linkSector oddWitnessLink).reflect) :=
  ⟨linkSector_linkTheta_holds_at_four, linkSector_linkTheta_false_at_three⟩

/-! ## §4 — The obstruction is the labelling, not the reflection

For odd `L` the reflection `t ↦ -t` on `Fin L` has exactly one fixed point,
`t = 0`, whereas `linkSector` reserves two slices. The counts below are the
arithmetic behind the repair route named in the header: with a `zero` set of
`{0}` only, the candidate plus-block `{1, …, M}` and minus-block
`{M+1, …, L-1}` have equal size `(L-1)/2` for odd `L`, so a parity-dependent
labelling has the symmetry this one lacks. Recorded as arithmetic, not as a
reflection-positivity claim. -/

/-- At `L = 3`: one fixed time slice, and two blocks of size 1 either side. -/
theorem odd_three_block_sizes :
    (Finset.univ.filter (fun t : Fin 3 => t = -t)).card = 1
      ∧ (3 - 1) / 2 = 1 := by
  refine ⟨by decide, by norm_num⟩

/-- At `L = 4`, by contrast, the reflection fixes two slices — which is what the
current `zero` set of `{0, L/2}` is built for. -/
theorem even_four_fixed_slices :
    (Finset.univ.filter (fun t : Fin 4 => t = -t)).card = 2 := by decide

/-- At `L = 5`: again one fixed slice, two blocks of size 2. -/
theorem odd_five_block_sizes :
    (Finset.univ.filter (fun t : Fin 5 => t = -t)).card = 1
      ∧ (5 - 1) / 2 = 2 := by
  refine ⟨by decide, by norm_num⟩

end PF.YangMills
