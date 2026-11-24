/-
# Counter-rotating vortex pairs: the helicity the current encoding cannot see

**Date**: 2026-11-23 (Legion).

## Why this file exists

`PF/Cosmology/CounterRotatingVorticesZeroPointFreeEnergy.lean` encodes a
counter-rotating pair as **two real scalars** `ω₁, ω₂` with `ω₁ + ω₂ = 0`, and
`PF/Cosmology/VortexCavitationBridgeChecks.lean` already corrects the
misreading that this makes angular *momentum* vanish. What neither file carries
is **helicity**, and helicity is the quantity the dark-energy sector needs.

The chain, from `codex/COSMOLOGY_DE_DERIVATION_2026-10-11.md` (rev 4/5):
varying the gauge connection in PF's action-as-written gives the constraint
`dφ ∧ F = 0`, which on a rolling `φ` forces `B = 0`, hence `Tr(F ∧ F) = 0`,
hence pure exponential quintessence with **`w ≥ −1` as a theorem**. Only a
**helical, parity-odd** background makes `Tr(F ∧ F) ≠ 0`. And
`codex/gravitational_reconnection_2026-11-10/track_A_claim_inventory.md`
records that Comisso–Asenjo's gravitational reconnection is driven by
`𝓔·𝓑` — in the paper's own words, "the gravitational analogue of plasma
reconnection's `E·B`" — with helicity evolution
`dH/dt = 2∫ α√γ (𝓡·𝓑)/Γ`.

So helicity is the missing object, in both sectors.

## What is DEFINED here, and what is PROVED

Helicity of a system of thin vortex tubes is **Moffatt's decomposition**

```
H = Σᵢ Γᵢ² (Wrᵢ + Twᵢ) + 2 Σᵢ<ⱼ Γᵢ Γⱼ Lkᵢⱼ
```

(Moffatt 1969; Moffatt–Ricca 1992). That is **classical fluid dynamics and is
not proved here** — it is the *definition* `totalHelicity` below, in exactly
the sense that the corpus's other encodings pin a definition and then compute
with it. Specialising it to `Γ₂ = −Γ₁` is arithmetic, and that part IS proved.

For a counter-rotating pair, `Γ₁ = Γ`, `Γ₂ = −Γ`, so the mutual term is
`2 Γ (−Γ) Lk = −2 Γ² Lk` and

```
H = Γ² [ (Wr₁ + Tw₁) + (Wr₂ + Tw₂) − 2 Lk ]
```

Proved below:

1. `helicity_planar_unlinked_eq_zero` — flat, untwisted, unlinked ⟹ `H = 0`.
   **The symmetric pair is helicity-free.** This is why the existing
   two-scalar encoding looked sufficient and is not.
2. `helicity_flat_eq_neg_two_linking` — flat and untwisted ⟹
   `H = −2 n Γ²`, closed form in the linking number.
3. `helicity_ne_zero_of_linked` — `Γ ≠ 0` and `n ≠ 0` ⟹ `H ≠ 0`.
   Nonzero helicity **coexists with `ω₁ + ω₂ = 0`**.
4. `helicity_parity_odd` — reversing the linking reverses the helicity:
   `H(−n) = −H(n)`. This is the parity-odd property the Pontryagin source
   requires.
5. `omegaSumZero_does_not_determine_helicity` — **the sharp instrument.** Two
   configurations with *identical* `(ω₁, ω₂)`, both satisfying `ω₁ + ω₂ = 0`,
   with *different* helicity. So no function of `ω₁` and `ω₂` can compute
   helicity, and the existing encoding is helicity-blind as a matter of
   type, not of oversight.

## What this does NOT establish — read before citing

This file supplies a parity-odd invariant. It does **not** supply the
identification of that invariant with `Tr(F ∧ F)`, and four obstructions stand
between them, each already documented elsewhere:

* **(O1) The bundle map is absent.** ch06's `F_∇` is the curvature of the
  consciousness bundle `(E, ∇)` over a base `X`; `ω` is a vorticity 2-form on
  physical space. Identifying them is a specific construction nobody has
  written. It is the same missing object as `(P★)` in
  `codex/PF_VORTEX_CAVITATION_WHOLE_TOE_INVESTIGATION.md` §5.3 and as `D1` in
  `codex/gravitational_reconnection_2026-11-10/track_D_PF_interface_assessment.md`.
* **(O2) `X = M⁴` is open.** The spacetime-emergence quotient was
  machine-proved to COLLAPSE at r333–r335.
* **(O3) A character is not a density.** ch06's `ch₂` is a coherent-sheaf second
  Chern *character* — a number, class **S7** in
  `codex/CH2_SEMANTIC_DISAMBIGUATION_LEDGER_2026-09-14.md` — while the action's
  `Tr(F ∧ F)` is a *density*. That conflation is already on the books (rev 3 of
  the DE derivation). Nothing here resolves it.
* **(O4) The `0.95` gate does not transfer.** Per the same ledger, the `0.95`
  threshold (class S5) attaches to S1/S2, where S2 is a bare real in `[0,1]`
  with **no bundle and no connection**. A helicity route lives in S7 and may
  not borrow that gate.

What the file *does* change is the shape of the gap: it is no longer "PF has no
parity-odd source available", it is "PF has a parity-odd invariant and needs one
specific bundle map". Progress of a kind that can be stated, not progress toward
a claim.

One further note, in the construction's favour: helicity **density** `u·ω`
varies in space, so it supplies a *gradient*, which is what
`rem:Jnu-gradient-2026-10-03` now demands of any candidate `(P★)` — a region
uniform in `𝒞` sources no momentum. A single object would address `(P★)`, `D1`
and the parity-odd requirement together. That is an observation about what to
try next, not a result.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-23.
-/

import PF.Cosmology.CounterRotatingVorticesZeroPointFreeEnergy
import Mathlib.Tactic

namespace PF.Cosmology.VortexHelicity

open PrincipiaTractalis.Cosmology

/-! ## §1 — A counter-rotating pair carrying its own topology -/

/-- A counter-rotating thin-tube pair with the geometric data helicity actually
    depends on. Tube 1 has circulation `Γ`, tube 2 has `-Γ`, so net circulation
    vanishes exactly as in `CounterRotatingVortexPair`.

    `linking` is the Gauss linking number `Lk₁₂ ∈ ℤ`; `writhe` and `twist` are
    the self-linking contributions of each tube. -/
structure LinkedCounterRotatingPair : Type where
  /-- Circulation of tube 1; tube 2 carries `-Γ`. -/
  Γ : ℝ
  /-- Gauss linking number of the two tube axes. -/
  linking : ℤ
  /-- Writhe of tube 1's axis. -/
  writhe₁ : ℝ
  /-- Writhe of tube 2's axis. -/
  writhe₂ : ℝ
  /-- Internal twist of tube 1's field lines. -/
  twist₁ : ℝ
  /-- Internal twist of tube 2's field lines. -/
  twist₂ : ℝ

/-- **Moffatt's helicity decomposition, specialised to `Γ₂ = -Γ₁`.**

    This is a DEFINITION encoding the classical result (Moffatt 1969;
    Moffatt–Ricca 1992), not a theorem proved here. The mutual term carries the
    factor `-2` because the circulations are opposite:
    `2 Γ₁ Γ₂ Lk = 2 Γ (-Γ) Lk = -2 Γ² Lk`. -/
noncomputable def totalHelicity (p : LinkedCounterRotatingPair) : ℝ :=
  p.Γ ^ 2 * ((p.writhe₁ + p.twist₁) + (p.writhe₂ + p.twist₂)
             - 2 * (p.linking : ℝ))

/-! ## §2 — The symmetric pair is helicity-free -/

/-- **A flat, untwisted, unlinked counter-rotating pair has zero helicity.**

    This is why the two-scalar encoding looked adequate: in the configuration
    everyone pictures, there is no helicity to miss. -/
theorem helicity_planar_unlinked_eq_zero (Γ : ℝ) :
    totalHelicity ⟨Γ, 0, 0, 0, 0, 0⟩ = 0 := by
  unfold totalHelicity
  norm_num

/-! ## §3 — Linking makes it nonzero, in closed form -/

/-- **`H = -2 n Γ²` for a flat, untwisted pair with linking number `n`.** -/
theorem helicity_flat_eq_neg_two_linking (Γ : ℝ) (n : ℤ) :
    totalHelicity ⟨Γ, n, 0, 0, 0, 0⟩ = -2 * (n : ℝ) * Γ ^ 2 := by
  unfold totalHelicity
  ring

/-- **Nonzero helicity coexists with `ω₁ + ω₂ = 0`.**

    The net circulation vanishes by construction, and the helicity does not. -/
theorem helicity_ne_zero_of_linked (Γ : ℝ) (n : ℤ) (hΓ : Γ ≠ 0) (hn : n ≠ 0) :
    totalHelicity ⟨Γ, n, 0, 0, 0, 0⟩ ≠ 0 := by
  rw [helicity_flat_eq_neg_two_linking]
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have h2 : (Γ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hΓ
  simpa using mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) hn') h2

/-! ## §4 — Parity-odd: the property the Pontryagin source requires -/

/-- **Reversing the linking reverses the helicity.**

    Under a reflection `Lk → -Lk`, so `H → -H`. Helicity is parity-odd, which
    is exactly the character `Tr(F ∧ F)` needs its source to have. -/
theorem helicity_parity_odd (Γ : ℝ) (n : ℤ) :
    totalHelicity ⟨Γ, -n, 0, 0, 0, 0⟩
      = -totalHelicity ⟨Γ, n, 0, 0, 0, 0⟩ := by
  rw [helicity_flat_eq_neg_two_linking, helicity_flat_eq_neg_two_linking]
  push_cast
  ring

/-! ## §5 — THE SHARP INSTRUMENT: the existing encoding is helicity-blind -/

/-- The existing two-scalar encoding, recovered from the geometric one. Net
    circulation vanishes, which is `CounterRotatingVortexPair`'s only content. -/
noncomputable def toScalarPair (p : LinkedCounterRotatingPair) :
    CounterRotatingVortexPair where
  ω₁ := p.Γ
  ω₂ := -p.Γ
  counter_rotating := by ring

/-- **Two configurations, identical `(ω₁, ω₂)`, different helicity.**

    Both have `ω₁ + ω₂ = 0`; both map to the *same* `CounterRotatingVortexPair`;
    their helicities are `0` and `-2`. Therefore **no function of `ω₁` and `ω₂`
    computes helicity**, and the existing encoding cannot represent it — a fact
    about its type, not an oversight in its use.

    This is the two-distinct-witnesses pattern the corpus requires before any
    claim that a structure carries content. -/
theorem omegaSumZero_does_not_determine_helicity :
    ∃ p q : LinkedCounterRotatingPair,
      toScalarPair p = toScalarPair q ∧ totalHelicity p ≠ totalHelicity q := by
  refine ⟨⟨1, 0, 0, 0, 0, 0⟩, ⟨1, 1, 0, 0, 0, 0⟩, rfl, ?_⟩
  rw [helicity_planar_unlinked_eq_zero, helicity_flat_eq_neg_two_linking]
  norm_num

/-! ## §6 — One citable bundle -/

/-- **`vortex_helicity_parity_odd_bundle`** — the five facts in one theorem.

    Nonzero parity-odd helicity exists on a counter-rotating pair whose net
    circulation vanishes, in closed form `-2 n Γ²`; and the corpus's existing
    encoding provably cannot see it.

    No claim is made that this helicity sources `Tr(F ∧ F)`. See obstructions
    (O1)-(O4) in this file's header. -/
theorem vortex_helicity_parity_odd_bundle :
    (totalHelicity ⟨1, 0, 0, 0, 0, 0⟩ = 0) ∧
    (∀ (Γ : ℝ) (n : ℤ),
      totalHelicity ⟨Γ, n, 0, 0, 0, 0⟩ = -2 * (n : ℝ) * Γ ^ 2) ∧
    (totalHelicity ⟨1, 1, 0, 0, 0, 0⟩ ≠ 0) ∧
    (∀ (Γ : ℝ) (n : ℤ),
      totalHelicity ⟨Γ, -n, 0, 0, 0, 0⟩
        = -totalHelicity ⟨Γ, n, 0, 0, 0, 0⟩) ∧
    (∃ p q : LinkedCounterRotatingPair,
      toScalarPair p = toScalarPair q ∧ totalHelicity p ≠ totalHelicity q) :=
  ⟨helicity_planar_unlinked_eq_zero 1,
   helicity_flat_eq_neg_two_linking,
   helicity_ne_zero_of_linked 1 1 one_ne_zero one_ne_zero,
   helicity_parity_odd,
   omegaSumZero_does_not_determine_helicity⟩

end PF.Cosmology.VortexHelicity

/-! ## §Axiom audit -/
#print axioms PF.Cosmology.VortexHelicity.helicity_planar_unlinked_eq_zero
#print axioms PF.Cosmology.VortexHelicity.helicity_flat_eq_neg_two_linking
#print axioms PF.Cosmology.VortexHelicity.helicity_ne_zero_of_linked
#print axioms PF.Cosmology.VortexHelicity.helicity_parity_odd
#print axioms PF.Cosmology.VortexHelicity.omegaSumZero_does_not_determine_helicity
#print axioms PF.Cosmology.VortexHelicity.vortex_helicity_parity_odd_bundle
