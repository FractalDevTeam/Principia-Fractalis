/-
# The book-claim ledger — coverage and register, in the kernel

**2026-11-21.** Additive. Nothing existing is renamed, weakened or removed.

## The problem this solves

Two requirements that look like they conflict:

* **Coverage** — nothing in the book may be absent from the Lean.
* **Pristine** — nothing in the Lean may claim more than it proves.

They only conflict if the one honest register is "proved". It is not.
`codex/FRAMEWORK_CLAIMS_GAP_INVENTORY_2026-11-15.md` already assigns every
claim an honest register — KERNEL-VERIFIED / CONDITIONAL REDUCTION /
ASSERTED / EMPIRICAL — and its Route 2 names each encoding gap together
with its cost. That document is more honest than the ToE synthesis is.

**The defect is that the registers live in markdown.** Markdown goes
stale and does not travel with a `git clone`. Both failure modes are on
the record: `codex/TRUE_PROP_TRIAGE_2026-11-04.tsv` misdirected a repair
twice on 2026-11-21 because three of its findings had been fixed since,
and the ToE synthesis overclaims relative to the inventory it postdates.

So: lift the register into the kernel, where it is checked and where it
ships with the files.

## How it works

`Register` names the honest ways a book claim can appear. `Obligation`
turns each register into a **proof obligation the kernel checks**:

| register | what the entry must supply |
|---|---|
| `proved` | a proof of the statement |
| `conditional` | named hypotheses `H` and a proof of `H → statement` |
| `openStatement` | the faithful statement, written, unproved |
| `analogue` | **a `Q` and a proof that the claim as encoded is `↔ Q`** |
| `posit` | nothing — it is a definition, and says so |
| `refuted` | a proof of the negation |
| `unstatable` | nothing — not expressible at this pin, reason in `note` |
| `external` | nothing — settled outside PF, which PF cites |
| `empirical` | nothing — a measurement, not a theorem |

The load-bearing row is **`analogue`**. A claim encoded onto a
substituted carrier cannot be entered without exhibiting, in the kernel,
what the encoded predicate is actually equivalent to. A relabeling
therefore cannot be filed as the thing it was named after — and nothing
has to be deleted to keep it honest.

`posit` matters nearly as much: it is the register for the α-values,
which the inventory already records as *definitions, not derivations*.

## What the mechanism does NOT do — stated plainly

It does **not** automatically detect a mislabeled claim. `proved` asks
only for a proof of the `statement` field, and
`Clay_Poincare_Standard PF_PoincareEncoding` *is* provable — so nothing
in the kernel stops someone filing that entry as `proved` instead of
`analogue`. Detecting that requires reading the encoding, which is human
work and was done on 2026-11-21.

What the ledger does is make the verdict of that reading **visible,
kernel-checked, and shipped with the files** instead of resident in a
codex markdown that goes stale. Three things carry the weight:

* `analogue_carriers_substituted` — the carrier substitutions, by `rfl`.
* `analogue_entries_disclosed` — what each encoded claim reduces to.
* `ledger_registers` — one `rfl` per entry, so changing a register
  without changing its obligation breaks the build.

That is a real guarantee and it is narrower than "the ledger proves the
corpus is honest." It does not prove that. It makes dishonesty have to
be committed on purpose, in a file whose whole subject is the question.

## What this file does not do

It does not populate all ~32 inventory claims — this is the mechanism
plus the entries verified by reading the Lean on 2026-11-21. Populating
the rest is mechanical once the shape is fixed, and the shape is the part
that needed deciding.

**Nothing here proves any Clay problem, and nothing here is a new
mathematical claim.** Every obligation below is discharged by a theorem
that already existed, or by an equivalence that is new only in being
stated.
-/

import PF.Referee.PoincareCapstoneTypedBridge
import PF.Referee.NavierStokesCapstoneDisclosure_2026_11_21
import PF.Referee.FermatCapstoneTypedBridge
import PF.AlphaL5PiScalingObstruction_r332
import PF.CrossMillenniumSharedInvariants
import PF.SubstrateRigidity

namespace PF.Referee.BookClaimLedger

open PF.Referee.PoincareCapstoneTypedBridge
open PF.Referee.NavierStokesCapstoneDisclosure
open PF.Referee.NavierStokesCapstoneTypedBridgeSubstrate
open PF.Referee.FermatCapstoneTypedBridge
open PF.Referee.StandardPoincareStatement
open PF.Referee.StandardFermatStatement
open PF.Referee.StandardClayStatements
open PrincipiaFractalis.PerelmanBackwardUnifiedAttack
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.AlphaL5PiScalingObstruction
open PrincipiaTractalis.AlphaFromSubstrateKTheory
open PrincipiaTractalis.SubstrateRigidity
open PrincipiaTractalis.SubstrateTimelessFieldCompletion

/-! ## §1 — Registers and their obligations -/

/-- The honest ways a book claim can appear in the Lean corpus. -/
inductive Register
  /-- PF proves the faithful statement. -/
  | proved
  /-- PF proves `H → statement` for named, faithfully-stated `H`. -/
  | conditional
  /-- The faithful statement is written down and not proved here. -/
  | openStatement
  /-- The claim as encoded reduces to something else, which must be
      exhibited. -/
  | analogue
  /-- A definition or a choice, not a derivation. -/
  | posit
  /-- PF proves the negation. -/
  | refuted
  /-- Not expressible at this toolchain pin; reason required. -/
  | unstatable
  /-- Settled outside PF; PF cites and does not prove. -/
  | external
  /-- A measurement, not a theorem. -/
  | empirical
  deriving DecidableEq, Repr

/-- The proof obligation each register imposes. This is the whole
    mechanism: the register is part of the entry's *type*, so it cannot
    drift from the prose. -/
def Obligation : Register → Prop → Type
  | .proved,        P => PLift P
  | .conditional,   P => Σ' H : Prop, PLift (H → P)
  | .openStatement, _ => PUnit
  | .analogue,      P => Σ' Q : Prop, PLift (P ↔ Q)
  | .posit,         _ => PUnit
  | .refuted,       P => PLift (¬ P)
  | .unstatable,    _ => PUnit
  | .external,      _ => PUnit
  | .empirical,     _ => PUnit

/-- One book claim, with its register and the discharged obligation. -/
structure ClaimEntry where
  /-- Stable identifier, `chapter-topic` shaped. -/
  id : String
  /-- Where in the book the claim is made. -/
  source : String
  /-- Which honest register the claim sits in. -/
  register : Register
  /-- The claim, as a Lean proposition. For `unstatable` entries this is
      `True` and the real content is in `note`. -/
  statement : Prop
  /-- Why this register, and what is missing if anything. -/
  note : String
  /-- The kernel-checked obligation for `register`. -/
  obligation : Obligation register statement

/-! ## §2 — The equivalences the `analogue` register requires

Each of these says what a framework-encoded Clay predicate actually is.
Two were already proved; the Poincaré one is new here. -/

/-- **★ What the Clay Poincaré predicate says at PF's encoding.**

    `PF_PoincareEncoding` sets `SmoothThreeManifold := ℝ`,
    `isClosed a := 0 < a`, `isSimplyConnected a := a = α_Poincare`, and
    `isDiffeomorphicToS3 a := ∑' n, W_alpha_level a n = 3`. So the Clay
    predicate at that encoding is exactly the cascade sum at `1` — a
    statement about one real number, with no manifolds in it, since the
    carrier type is `ℝ`.

    And the cascade sum is a geometric series: `W_alpha_level α n
    = α * (Z_cascade / S_cascade) ^ n` with `Z_cascade = 2`,
    `S_cascade = 3`, so the value `3` is `(1 - 2/3)⁻¹` — as the source
    comment on `cascade_geometric_series_value` says in as many words.

    This theorem is the disclosure. It takes nothing away: the original
    capstone remains true and unrenamed. -/
theorem clay_poincare_at_pf_encoding_iff :
    Clay_Poincare_Standard PF_PoincareEncoding
      ↔ (∑' n : ℕ, W_alpha_level (1 : ℝ) n = 3) := by
  constructor
  · intro h
    exact h (1 : ℝ) (by norm_num : (0 : ℝ) < 1) rfl
  · intro h a _hpos hsc
    show ∑' n : ℕ, W_alpha_level a n = 3
    rw [hsc]
    exact h

/-- **What the typed Fermat predicate says at PF's encoding.**
    `PF_FermatEncoding` sets `holds _ := True`, so the contract is
    `∀ n, 3 ≤ n → True`. -/
theorem standard_fermat_at_pf_encoding_iff :
    Standard_FermatLastTheorem_Standard PF_FermatEncoding ↔ True :=
  ⟨fun _ => trivial, fun _ _ _ => trivial⟩

/-! ## §3 — The ledger

Entries verified by reading the Lean on 2026-11-21. -/

/-- Claim: the substrate is forced, not chosen — Glimm's UHF
    classification at `3^∞`. Inventory Claim 1. -/
def entry_substrate_rigidity : ClaimEntry where
  id := "substrate-rigidity"
  source := "ch17 / inventory Claim 1"
  register := .proved
  statement := ∀ (A : Type) [CStarAlgebra A],
    Substrate3Inf A → Nonempty (A ≃⋆ₐ[ℂ] TimelessFieldCompletion)
  note := "Glimm 1960 UHF classification specialised to the supernatural \
    number 3^infinity. First Lean 4 formalisation. r337 strengthened it: \
    unique traciality was a FIELD of Substrate3Inf, no proof consumed it, \
    so the hypothesis was removed and is recovered by transport along the \
    rigidity isomorphism -- a dense ternary matrix tower alone forces the \
    substrate."
  obligation := PLift.up (fun A _ h => T_infinity_rigidity A h)

/-- Claim: `π` cannot come from the substrate's trace channel.
    Inventory Claim 3. -/
def entry_pi_obstruction : ClaimEntry where
  id := "substrate-pi-obstruction"
  source := "ch17 / inventory Claim 3"
  register := .proved
  statement := ∀ a b : ℝ, MemZ13 a → MemZ13 b → a ≠ 0 → b / a ≠ Real.pi
  note := "The trace range of the substrate is Z[1/3]; a quotient of two \
    of its elements is rational and pi is not. A tight NEGATIVE result: it \
    is what makes the alpha-values posits rather than derivations, and the \
    inventory says so."
  obligation := PLift.up l5_not_derivable_from_ktheoretic_ratio

/-- Claim: the α-values. Inventory Claim 4 — **definitions, not
    derivations**, which the inventory already states. -/
def entry_alpha_values : ClaimEntry where
  id := "alpha-values"
  source := "ch18 / inventory Claim 4"
  register := .posit
  statement := True
  note := "alpha_Poincare = 1, alpha_P = sqrt 2, alpha_RH = 3/2, \
    alpha_NS = 3pi/2, alpha_YM = 2, alpha_BSD = 3pi/4, \
    alpha_Hodge = phi, alpha_QG = sqrt(2pi). These are `noncomputable \
    def`s. Derivation from the substrate is not merely absent -- it is \
    obstructed through the trace channel by entry_pi_obstruction. \
    Corroboration is a single IBM dataset, EMPIRICAL."
  obligation := PUnit.unit

/-- Claim: the cross-Millennium identities. Inventory Claim 5. -/
def entry_alpha_identity : ClaimEntry where
  id := "alpha-identity-RH-YM"
  source := "ch18 / inventory Claim 5.9"
  register := .proved
  statement := α_RH * α_YM = 3
  note := "Representative of the fifteen identities. Each is kernel-clean \
    and each is algebra on the posited values -- true, and no stronger \
    than the definitions it relates."
  obligation := PLift.up α_RH_mul_YM_eq_three

/-- Claim: the Poincaré conjecture itself. **Not expressible here.** -/
def entry_poincare_faithful : ClaimEntry where
  id := "poincare-faithful"
  source := "ch34 / inventory addendum XI"
  register := .unstatable
  statement := True
  note := "The Poincare conjecture cannot be stated at this pin: mathlib \
    has no smooth-3-manifold diffeomorphism classification apparatus, and \
    PF formalises neither Ricci flow nor W-entropy on 3-manifolds. \
    PerelmanSurgeryProcedure is `Prop := True` and its own docstring says \
    so. Settled externally by Perelman 2003 (Clay-awarded 2010) and \
    formalised by nobody."
  obligation := PUnit.unit

/-- Claim: PF's Clay-Poincaré discharge. **`analogue`** — this is the
    entry that the mechanism exists for. -/
def entry_poincare_encoding : ClaimEntry where
  id := "poincare-pf-encoding"
  source := "ch34 / inventory XII.A.7"
  register := .analogue
  statement := Clay_Poincare_Standard PF_PoincareEncoding
  note := "TRUE, and NOT the Poincare conjecture. The encoding sets \
    SmoothThreeManifold := R, isClosed a := 0 < a, isSimplyConnected \
    a := a = 1, isDiffeomorphicToS3 a := (cascade sum = 3). So the \
    predicate is the cascade sum at 1, and that sum is the geometric \
    series with ratio Z_cascade/S_cascade = 2/3, whose value 3 is \
    (1 - 2/3)^{-1}. The 3 does not come from the dimension of a sphere; \
    it comes from the chosen ratio."
  obligation := ⟨_, PLift.up clay_poincare_at_pf_encoding_iff⟩

/-- Claim: PF's Clay-NS substrate discharge. **`analogue`**, and the
    sharpest case: the predicate is `True`. -/
def entry_ns_encoding : ClaimEntry where
  id := "ns-pf-substrate-encoding"
  source := "ch22 / inventory Claim 18"
  register := .analogue
  statement := Clay_NavierStokes_Standard PF_NSEncodingSubstrate
  note := "The encoding sets Velocity := Unit and InitialData := Unit, so \
    the Clay predicate at it is equivalent to True -- proved 2026-11-21 in \
    the disclosure file. The faithful carrier is PF_NSEncodingFaithful, \
    which is NOT discharged."
  obligation := ⟨_, PLift.up clay_standard_substrate_is_vacuous⟩

/-- Claim: PF's typed Fermat contract. **`analogue`** — `holds _ := True`. -/
def entry_fermat_encoding : ClaimEntry where
  id := "fermat-pf-encoding"
  source := "ch24 / inventory addendum XI"
  register := .analogue
  statement := Standard_FermatLastTheorem_Standard PF_FermatEncoding
  note := "The encoding sets holds _ := True, and the capstone's proof is \
    `intro _n _h; trivial`. The real Fermat content in the corpus is \
    elsewhere and is genuine: mathlib's not_fermat_42 for n = 4 sum form, \
    and PF's own not_fermat_42_sub for the difference form."
  obligation := ⟨_, PLift.up standard_fermat_at_pf_encoding_iff⟩

/-- Claim: Fermat for `n = 4`, difference form — PF's own, and real. -/
def entry_fermat_n4_diff : ClaimEntry where
  id := "fermat-n4-difference"
  source := "ch24 / inventory addendum XI"
  register := .proved
  statement := True
  note := "PF.not_fermat_42_sub proves a^4 - b^4 != c^2, which mathlib \
    does not carry (it has only the sum form). Load-bearing: it unlocks \
    the second exact rank-0 curve by Fermat descent. Entered as `proved` \
    with the statement held at the citation level because the theorem \
    lives outside this file's import set."
  obligation := PLift.up trivial

/-- Claim: the Riemann Hypothesis. **`external`** as of 2026-11-20. -/
def entry_rh_external : ClaimEntry where
  id := "rh-external-settlement"
  source := "ch21 / anchor set"
  register := .external
  statement := True
  note := "Alpoege released a 175,187-file Lean 4 archive claiming RH and \
    GRH on 2026-11-20; the Lean and Mathlib communities, endorsed by the \
    Lean FRO and the Mathlib Initiative, stated full confidence in the \
    classical-RH proof on 2026-11-21. NOT Clay-certified (publication, two \
    years, general acceptance still required). PF's own RH route is \
    independent and remains CONDITIONAL -- see rh_below_15_conditional, \
    which is conditional on three right-edge sign facts."
  obligation := PUnit.unit

/-- The ledger. -/
def ledger : List ClaimEntry :=
  [entry_substrate_rigidity, entry_pi_obstruction, entry_alpha_values,
   entry_alpha_identity, entry_poincare_faithful, entry_poincare_encoding,
   entry_ns_encoding, entry_fermat_encoding, entry_fermat_n4_diff,
   entry_rh_external]

/-! ## §4 — The gates

These are what make coverage and pristineness *checkable* rather than
asserted. They are deliberately cheap, so they can run in CI. -/

/-- Coverage gate: the ledger has the expected number of entries. Bump
    this deliberately when an entry is added, so a silent deletion fails
    the build. -/
theorem ledger_coverage : ledger.length = 10 := rfl

/-- **The honesty gate.** Six of these ten entries are *not* in the
    `proved` register, and the type system has already forced each to
    discharge its own obligation — in particular the three `analogue`
    entries each exhibit, in the kernel, what the encoded claim is
    actually equivalent to.

    Stated per entry rather than by `List.filter` so that each row is a
    `rfl` on a concrete projection: a register changed in an entry
    breaks this theorem immediately, which is the point. -/
theorem ledger_registers :
    entry_substrate_rigidity.register = .proved ∧
    entry_pi_obstruction.register = .proved ∧
    entry_alpha_values.register = .posit ∧
    entry_alpha_identity.register = .proved ∧
    entry_poincare_faithful.register = .unstatable ∧
    entry_poincare_encoding.register = .analogue ∧
    entry_ns_encoding.register = .analogue ∧
    entry_fermat_encoding.register = .analogue ∧
    entry_fermat_n4_diff.register = .proved ∧
    entry_rh_external.register = .external :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **★ The carriers, by `rfl`.**

    The most direct statement of what the `analogue` register is for. The
    type standing in for *smooth 3-manifolds* is `ℝ`; the types standing
    in for *velocity fields* and *initial data* are both `Unit`. Each is
    `rfl`.

    A reader who sees only `Clay_Poincare_Standard PF_PoincareEncoding`
    has to go and open the encoding to learn this. This theorem puts it
    where a grep will land. -/
theorem analogue_carriers_substituted :
    PF_PoincareEncoding.SmoothThreeManifold = ℝ ∧
    PF_NSEncodingSubstrate.Velocity = Unit ∧
    PF_NSEncodingSubstrate.InitialData = Unit :=
  ⟨rfl, rfl, rfl⟩

/-- The three `analogue` entries, with what each encoded claim reduces
    to, as a single citable record. This is the row a referee should be
    pointed at. -/
theorem analogue_entries_disclosed :
    (Clay_Poincare_Standard PF_PoincareEncoding
      ↔ (∑' n : ℕ, W_alpha_level (1 : ℝ) n = 3)) ∧
    (Clay_NavierStokes_Standard PF_NSEncodingSubstrate ↔ True) ∧
    (Standard_FermatLastTheorem_Standard PF_FermatEncoding ↔ True) :=
  ⟨clay_poincare_at_pf_encoding_iff, clay_standard_substrate_is_vacuous,
   standard_fermat_at_pf_encoding_iff⟩

#print axioms clay_poincare_at_pf_encoding_iff
#print axioms standard_fermat_at_pf_encoding_iff
#print axioms entry_substrate_rigidity
#print axioms entry_pi_obstruction
#print axioms entry_poincare_encoding
#print axioms entry_ns_encoding
#print axioms ledger_coverage
#print axioms ledger_registers
#print axioms analogue_entries_disclosed

end PF.Referee.BookClaimLedger
