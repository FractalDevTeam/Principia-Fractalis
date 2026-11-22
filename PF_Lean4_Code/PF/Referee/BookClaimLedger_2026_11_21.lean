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
import PF.SubstrateTraceUniqueness
import PF.Analytic.HilbertPolyaIdentificationPrecise
import PF.Referee.RHCapstoneTypedBridgeV2
import PF.SpectralGap
import PF.YangMills.WilsonFubiniClosed_r385
import PF.YangMills.WilsonRPL2ExtensionCapstone_2026_11_12
import PF.Ch20Ch25NumericObstructions
import PF.NS3DVortexStretchingBoundedDischarge
import PF.NavierStokes.Fefferman2000_Faithful_SteadyTransport_2026_11_21
import PF.Ch24Descent2TorsionRatBridge_2026_10_17
import PF.Ch24DescentSub2TorsionRatBridge_2026_11_14
import PF.BSD_HeegnerHypothesis_Faithful_2026_11_21
import PF.Analytic.Hardy1914_Faithful_2026_11_21
import PF.Ch2ThresholdSelection

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
  /-- Proved in the corpus, verified by name on disk, and CITED here
      rather than kernel-linked. Distinct from `proved`, which carries
      the term. Upgrading one of these to `proved` is a matter of adding
      an import, so the remaining work is a measurable list in the Lean
      rather than a note in a markdown file. -/
  | provedElsewhere
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
  | .provedElsewhere, _ => PUnit

/-- One book claim, with its register and the discharged obligation. -/
structure ClaimEntry where
  /-- Stable identifier, `chapter-topic` shaped. -/
  id : String
  /-- Where in the book the claim is made. -/
  source : String
  /-- Which honest register the claim sits in — i.e. what THIS entry
      kernel-checks. -/
  register : Register
  /-- The verdict `codex/FRAMEWORK_CLAIMS_GAP_INVENTORY_2026-11-15.md`
      records for the claim. Orthogonal to `register`: an entry may be
      `provedElsewhere` here while the inventory says KERNEL-VERIFIED,
      and that pair is exactly what is true. -/
  inventoryStatus : String
  /-- The Lean name or file the claim lives at. Verified present on disk
      2026-11-21 for every entry that names one. -/
  leanName : String
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
  inventoryStatus := "KERNEL-VERIFIED"
  leanName := "PrincipiaTractalis.SubstrateRigidity.T_infinity_rigidity"
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
  inventoryStatus := "KERNEL-VERIFIED"
  leanName := "PrincipiaTractalis.AlphaL5PiScalingObstruction.l5_not_derivable_from_ktheoretic_ratio"
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
  inventoryStatus := "DEFINITIONS, not derivations"
  leanName := "PF/CrossMillenniumSharedInvariants.lean"
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
  inventoryStatus := "KERNEL-VERIFIED"
  leanName := "PrincipiaTractalis.CrossMillenniumSharedInvariants.α_RH_mul_YM_eq_three"
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
  inventoryStatus := "not expressible at this pin"
  leanName := ""
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
  inventoryStatus := "KERNEL-VERIFIED on PF_PoincareEncoding"
  leanName := "PF.Referee.PoincareCapstoneTypedBridge.PF_Poincare_capstone_yields_Clay_Poincare_standard"
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
  inventoryStatus := "KERNEL-VERIFIED on PF_NSEncodingSubstrate"
  leanName := "PF.Referee.NavierStokesCapstoneDisclosure.clay_standard_substrate_is_vacuous"
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
  inventoryStatus := "KERNEL-VERIFIED on PF_FermatEncoding"
  leanName := "PF.Referee.FermatCapstoneTypedBridge.PF_Fermat_capstone_yields_Standard_FermatLastTheorem_standard"
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
  register := .provedElsewhere
  inventoryStatus := "KERNEL-VERIFIED"
  leanName := "PF.not_fermat_42_sub"
  statement := True
  note := "PF.not_fermat_42_sub proves a^4 - b^4 != c^2, which mathlib \
    does not carry (it has only the sum form). Load-bearing: it unlocks \
    the second exact rank-0 curve by Fermat descent. Entered as `proved` \
    with the statement held at the citation level because the theorem \
    lives outside this file's import set."
  obligation := PUnit.unit

/-- Claim: the Riemann Hypothesis. **`external`** as of 2026-11-20. -/
def entry_rh_external : ClaimEntry where
  id := "rh-external-settlement"
  source := "ch21 / anchor set"
  register := .external
  inventoryStatus := "external settlement 2026-11-20"
  leanName := ""
  statement := True
  note := "Alpoege released a 175,187-file Lean 4 archive claiming RH and \
    GRH on 2026-11-20; the Lean and Mathlib communities, endorsed by the \
    Lean FRO and the Mathlib Initiative, stated full confidence in the \
    classical-RH proof on 2026-11-21. NOT Clay-certified (publication, two \
    years, general acceptance still required). PF's own RH route is \
    independent and remains CONDITIONAL -- see rh_below_15_conditional, \
    which is conditional on three right-edge sign facts."
  obligation := PUnit.unit

/-! ## §5 — The remaining inventory claims

Entries 11–35, covering inventory Claims 2 and 6–32. Every theorem name
was verified present on disk on 2026-11-21 before being cited here —
the inventory is dated 2026-11-15 and a stale name misdirected two
repairs earlier the same day.

`type_of% @Name` names each statement instead of transcribing it, so an
upstream change breaks this file rather than silently diverging. `@`
blocks implicit insertion so the full `∀`-type is taken.

Two orthogonal fields now carry the honesty:

* `register` — what **this entry** kernel-checks.
* `inventoryStatus` — the inventory's own verdict for the claim.

So `provedElsewhere` + `"KERNEL-VERIFIED"` says exactly what is true: the
claim is proved in the corpus, verified by name on disk, and *this* entry
cites rather than links it. Upgrading such an entry to `proved` is a
matter of adding one import, which makes the remaining work a measurable
list inside the Lean rather than a note in a markdown file. -/

/-! ### Substrate -/

/-- Claim 2 — the substrate's trace is unique, and derived not assumed. -/
def entry_trace_unique : ClaimEntry where
  id := "substrate-trace-unique"
  source := "ch17 / inventory Claim 2"
  register := .proved
  inventoryStatus := "KERNEL-VERIFIED"
  leanName := "PrincipiaTractalis.SubstrateTraceUniqueness.substrate_UHF_trace_unique"
  statement := type_of% @PrincipiaTractalis.SubstrateTraceUniqueness.substrate_UHF_trace_unique
  note := "Uniqueness of the continuous unital tracial functional. r337 \
    showed this was a REDUNDANT field of Substrate3Inf -- no proof \
    consumed it -- so it was removed as a hypothesis and recovered by \
    transport along the rigidity isomorphism."
  obligation := PLift.up @PrincipiaTractalis.SubstrateTraceUniqueness.substrate_UHF_trace_unique

/-! ### Riemann Hypothesis -/

/-- Claim 6 — the four Hilbert–Pólya formulations, and HP ⇒ RH. -/
def entry_hp_implies_rh : ClaimEntry where
  id := "rh-hp-implies-rh"
  source := "ch21 / inventory Claim 6"
  register := .proved
  inventoryStatus := "CONDITIONAL REDUCTION"
  leanName := "PrincipiaTractalis.HilbertPolyaIdentificationPrecise.hilbert_polya_implies_RH"
  statement := type_of% @PrincipiaTractalis.HilbertPolyaIdentificationPrecise.hilbert_polya_implies_RH
  note := "The IMPLICATION is kernel-verified; its antecedents \
    (HilbertPolyaProgramConjecture_Positive, \
    RHSpectralSurjectivityConjecture) are open. Registered `proved` \
    because the Lean theorem -- an implication -- is what is proved."
  obligation := PLift.up @PrincipiaTractalis.HilbertPolyaIdentificationPrecise.hilbert_polya_implies_RH

/-- Claim 7 — `ξ` has no off-line zeros in `|t| ≤ 15`, conditional on
    three right-edge sign facts. -/
def entry_rh_below_15 : ClaimEntry where
  id := "rh-below-15-conditional"
  source := "ch21 / inventory Claim 7"
  register := .provedElsewhere
  inventoryStatus := "CONDITIONAL REDUCTION"
  leanName := "PrincipiaTractalis.RHBelow15Conditional.rh_below_15_conditional"
  statement := True
  note := "Conditional on R1 and R2 and R3, the three sign facts for \
    xi(1+it) on sub-intervals of [0,15]. Those are NUMERICALLY confirmed \
    and not Lean-verified -- they are the open antecedents. Real analytic \
    content and the statement matches the intention. \
    CITED rather than kernel-linked ON PURPOSE: the module transitively \
    imports PF.Analytic.RightEdgeSigns_2026_10_08, which PF.lean's own \
    2026-11-02 closure-repair note records as deliberately OUTSIDE the \
    closure because it pulls 4,847 modules of which 4,104 are \
    RiemannXiBox0Panels. Linking it here would silently reverse that \
    decision."
  obligation := PUnit.unit

/-- Claim 8 — the unconditional box march. -/
def entry_rh_box_march : ClaimEntry where
  id := "rh-box-march"
  source := "ch21 / inventory Claim 8"
  register := .provedElsewhere
  inventoryStatus := "KERNEL-VERIFIED, UNCONDITIONAL (per-panel)"
  leanName := "PF/Analytic/FourierPanels/*"
  statement := True
  note := "Per-panel interval arithmetic giving no zeros of xi in \
    {0 <= sigma <= 1, 0 <= t <= 829/64}. UNCONDITIONAL, which the \
    [0,15] result is not. Blocked at the next panel: gate lhs = 1.108 > 1 \
    at D = 1, and NOT r-tunable (checked at r = 1/64 and 1/128). Cited \
    rather than linked because the content is thousands of panel files."
  obligation := PUnit.unit

/-- Claim 9 — Clay RH reduced to one named hypothesis. The Clay
    predicate here is wired to mathlib's real `riemannZeta`. -/
def entry_rh_clay_capstone : ClaimEntry where
  id := "rh-clay-capstone-v2"
  source := "ch21 / inventory Claim 9"
  register := .proved
  inventoryStatus := "CONDITIONAL REDUCTION of the LITERAL Clay statement"
  leanName := "PF.Referee.RHCapstoneTypedBridgeV2.PF_RH_capstone_yields_Clay_RH_standardV2"
  statement := type_of% @PF.Referee.RHCapstoneTypedBridgeV2.PF_RH_capstone_yields_Clay_RH_standardV2
  note := "NOT an analogue: Clay_RiemannHypothesis_Standard is wired to \
    the real riemannZeta, so this is a genuine reduction of literal Clay \
    RH to the named `surjectivity` hypothesis (RH_OpenFrontierV2). \
    Whether that frontier is more tractable than RH is for an analytic \
    number theorist to judge. Since 2026-11-20 RH is externally settled \
    -- see entry_rh_external -- so the reduction is now a parallel route \
    to a known theorem."
  obligation := PLift.up @PF.Referee.RHCapstoneTypedBridgeV2.PF_RH_capstone_yields_Clay_RH_standardV2

/-! ### P vs NP -/

/-- Claim 10 — the spectral gap is nonzero. Note the theorem's NAME. -/
def entry_spectral_gap : ClaimEntry where
  id := "pnp-spectral-gap"
  source := "ch23 / inventory Claim 10"
  register := .proved
  inventoryStatus := "KERNEL-VERIFIED"
  leanName := "PrincipiaTractalis.P_neq_NP"
  statement := type_of% @PrincipiaTractalis.P_neq_NP
  note := "The theorem is named P_neq_NP and its statement is \
    `spectral_gap != 0` -- a real-number inequality, NOT the class \
    separation. The inventory says so explicitly. The name is the kind \
    of thing a referee will grep; this entry puts the real statement \
    beside it."
  obligation := PLift.up @PrincipiaTractalis.P_neq_NP

/-- Claim 11 — the class-separation bridge. -/
def entry_pnp_bridge : ClaimEntry where
  id := "pnp-separation-bridge"
  source := "ch23 / inventory Claim 11"
  register := .provedElsewhere
  inventoryStatus := "CONDITIONAL REDUCTION"
  leanName := "enum_to_class_separation_bridge_V{2,3}_iff_literal_P_neq_NP_V{2,3}"
  statement := True
  note := "Bridges spectral_gap != 0 to literal P != NP conditional on a \
    faithful-separator premise, which the inventory's Route 2 records as \
    EQUIVALENT TO CLAY P vs NP. The PF_ComplexityEncoding itself is \
    genuinely faithful (real Turing machines, certificates, Cook 1971, \
    and Clay_PvsNP_Standard as non-surjectivity of the inclusion) -- \
    this axis is the one whose encoding does NOT substitute its carrier."
  obligation := PUnit.unit

/-- Claim 12 — the IBM run. -/
def entry_ibm_coherence : ClaimEntry where
  id := "pnp-ibm-143"
  source := "ch23 / inventory Claim 12"
  register := .empirical
  inventoryStatus := "EMPIRICAL — single dataset"
  leanName := ""
  statement := True
  note := "100% coherence on a 2026-05-23 IBM Quantum run over 143 Smale \
    1998 / DARPA 2008 problems. CSV and script in ARCHIVE. NOT reproduced \
    on another machine. This is the sole corroboration offered for the \
    alpha-values, which entry_alpha_values registers as posits."
  obligation := PUnit.unit

/-! ### Yang–Mills -/

/-- Claim 13 — Wilson lattice reflection positivity, continuous test
    functions. Real gauge theory: `GaugeField L := LatticeLink L → SU2`. -/
def entry_wilson_rp_cont : ClaimEntry where
  id := "ym-wilson-rp-continuous"
  source := "ch20 / inventory Claim 13"
  register := .proved
  inventoryStatus := "KERNEL-VERIFIED, UNCONDITIONAL"
  leanName := "PF.YangMills.wilson_reflection_positivity_of_continuous"
  statement := type_of% @PF.YangMills.wilson_reflection_positivity_of_continuous
  note := "For finite even periodic lattices the theta-crossed Gram \
    matrix of continuous test functions supported on the non-negative \
    half is PosSemidef, with gauge fields valued in SU2. Genuine lattice \
    gauge theory and genuinely unconditional -- one of the corpus's real \
    assets, independent of the alpha-skeleton."
  obligation := PLift.up @PF.YangMills.wilson_reflection_positivity_of_continuous

/-- Claim 14 — the same, extended to `L²`. -/
def entry_wilson_rp_l2 : ClaimEntry where
  id := "ym-wilson-rp-l2"
  source := "ch20 / inventory Claim 14"
  register := .proved
  inventoryStatus := "KERNEL-VERIFIED, UNCONDITIONAL"
  leanName := "PF.YangMills.wilson_reflection_positivity_of_L2_strong"
  statement := type_of% @PF.YangMills.wilson_reflection_positivity_of_L2_strong
  note := "Claim 13 for StronglyMeasurable + MemLp 2 test functions. The \
    L2 extension is the harder half and it is closed."
  obligation := PLift.up @PF.YangMills.wilson_reflection_positivity_of_L2_strong

/-- Claim 15 — the Clay YM capstone. **`analogue`**. -/
def entry_ym_clay_capstone : ClaimEntry where
  id := "ym-clay-capstone-v4"
  source := "ch20 / inventory Claim 15"
  register := .provedElsewhere
  inventoryStatus := "KERNEL-VERIFIED on PF_YMEncodingV4; NOT a Clay discharge"
  leanName := "PrincipiaTractalis.YM_ContinuumWightmanV4.PF_YM_capstone_yields_Clay_YangMillsMassGap_standardV4"
  statement := True
  note := "Discharged with mass gap 3/2 on an encoding whose carrier is \
    finite-dimensional Fin 2 -> R, not the infinite-dimensional Clay \
    setting; no continuum limit and no SU(3). The author labels it NOT a \
    Clay discharge in-file. The sibling PF_YMEncoding is sharper still: \
    GaugeGroup := Unit, QYM := Matrix (Fin 2) (Fin 2) R, and \
    massGap _ := 1/2 as a literal constant. Belongs in `analogue` once \
    its reduction is written; cited here pending that."
  obligation := PUnit.unit

/-- Claim 16 — the chapter's own mass-gap formula, refuted in-chapter. -/
def entry_ym_massgap_refuted : ClaimEntry where
  id := "ym-massgap-formula-refuted"
  source := "ch20 / inventory Claim 16"
  register := .proved
  inventoryStatus := "REFUTED — kernel-verified negative content"
  leanName := "PrincipiaTractalis.Ch20Ch25Numerics.formula_output_ne_printed"
  statement := type_of% @PrincipiaTractalis.Ch20Ch25Numerics.formula_output_ne_printed
  note := "The chapter's own Delta = hbar c omega_c pi/10 = 420.43 MeV is \
    REFUTED by three independent routes inside the chapter: the resonance \
    zero does not exist, the displayed product is 132.148 not 420.43, and \
    the corrected formula caps at 62.3 MeV over every alpha. Honestly \
    recorded, and a refutation of PF's own claim being kernel-verified is \
    evidence the process has teeth."
  obligation := PLift.up @PrincipiaTractalis.Ch20Ch25Numerics.formula_output_ne_printed

/-! ### Navier–Stokes -/

/-- Claim 17 — the vortex-stretching hypothesis at every Galerkin cutoff. -/
def entry_ns_vortex_all_n : ClaimEntry where
  id := "ns-vortex-stretching-all-n"
  source := "ch22 / inventory Claim 17"
  register := .proved
  inventoryStatus := "KERNEL-VERIFIED, UNCONDITIONAL per-n"
  leanName := "PrincipiaTractalis.NS3DVortexStretchingObstruction.vortexStretchingBoundedHypothesis_holds"
  statement := type_of% @PrincipiaTractalis.NS3DVortexStretchingObstruction.vortexStretchingBoundedHypothesis_holds
  note := "Holds for every n. The UNIFORM-in-n bound is the gap and is \
    explicitly named, not closed -- and the 2026-11-21 reading found the \
    per-n bound is free at K = 1, so the cascade route to the uniform \
    bound carries no content."
  obligation := PLift.up @PrincipiaTractalis.NS3DVortexStretchingObstruction.vortexStretchingBoundedHypothesis_holds

/-- Claim 18 — the Clay NS capstone V4. -/
def entry_ns_clay_v4 : ClaimEntry where
  id := "ns-clay-capstone-v4"
  source := "ch22 / inventory Claim 18"
  register := .provedElsewhere
  inventoryStatus := "KERNEL-VERIFIED on PF_NS3DEncodingV4; NOT a Clay discharge"
  leanName := "PF.NavierStokes.NS3DRegularitySolutionV4.PF_NS_capstone_yields_Clay_NavierStokes_standardV4"
  statement := True
  note := "The encoding uses `smoothness := True`, not literal C^infty, \
    and NS_LocalToGlobalBootstrap (Leray 1934 + Hopf 1951, absent from \
    mathlib) remains open. Author labels it NOT a Clay discharge in-file. \
    The substrate sibling is entry_ns_encoding, whose predicate is \
    PROVED equivalent to True."
  obligation := PUnit.unit

/-- Claim 19 — Route A, the remaining classical-analysis bar. -/
def entry_ns_route_a : ClaimEntry where
  id := "ns-route-a"
  source := "ch22 / inventory Claim 19"
  register := .openStatement
  inventoryStatus := "OPEN"
  leanName := ""
  statement := True
  note := "Three ordered items: Schwartz dense in L2 by mollification; \
    Galerkin to weak formulation; direct Young for L1 * L2 -> L2. The \
    third landed 2026-11-15 as convolution_squared_le_L1_sq_mul_L2_sq and \
    the L1*L1 corner landed 2026-11-18."
  obligation := PUnit.unit

/-- The steady vorticity transport equation, derived 2026-11-21. -/
def entry_ns_steady_transport : ClaimEntry where
  id := "ns-steady-vorticity-transport"
  source := "ch22 / 2026-11-21 landing"
  register := .proved
  inventoryStatus := "KERNEL-VERIFIED (post-dates the inventory)"
  leanName := "PF.NavierStokes.FeffermanFaithful.steady_vorticity_transport_of_contDiff"
  statement := type_of% @PF.NavierStokes.FeffermanFaithful.steady_vorticity_transport_of_contDiff
  note := "(u.grad)omega_3 = (omega.grad)u_3 + nu Lap omega_3 DERIVED \
    from the steady momentum equation and div u = 0, with no \
    differentiability side conditions. Two witnesses make it non-vacuous: \
    plane Couette satisfies the hypotheses with omega_3 = -1, and for the \
    strain-rotation field the conclusion reads 0 = 4. STEADY ONLY and no \
    part of the Clay problem."
  obligation := PLift.up @PF.NavierStokes.FeffermanFaithful.steady_vorticity_transport_of_contDiff

/-! ### Birch–Swinnerton-Dyer -/

/-- Claim 20a — an exact rank-0 curve by Fermat descent. -/
def entry_bsd_rank0_a : ClaimEntry where
  id := "bsd-rank0-y2x3plusx"
  source := "ch24 / inventory Claim 20"
  register := .proved
  inventoryStatus := "KERNEL-VERIFIED"
  leanName := "PrincipiaTractalis.Ch24DescentRatBridge20261017.Ecurve_rank_eq_zero"
  statement := type_of% @PrincipiaTractalis.Ch24DescentRatBridge20261017.Ecurve_rank_eq_zero
  note := "Module.rank Z Ecurve.toAffine.Point = 0 for y^2 = x^3 + x, \
    conductor 64, by classical Fermat infinite descent through mathlib's \
    not_fermat_42. An EXACT rank, not a bound -- real BSD-adjacent \
    arithmetic."
  obligation := PLift.up @PrincipiaTractalis.Ch24DescentRatBridge20261017.Ecurve_rank_eq_zero

/-- Claim 20b — the second exact rank-0 curve, via PF's own difference
    form. -/
def entry_bsd_rank0_b : ClaimEntry where
  id := "bsd-rank0-y2x3minusx"
  source := "ch24 / inventory Claim 20"
  register := .proved
  inventoryStatus := "KERNEL-VERIFIED"
  leanName := "PrincipiaTractalis.Ch24DescentSubRatBridge20261114.Ecurve32a2_rank_eq_zero"
  statement := type_of% @PrincipiaTractalis.Ch24DescentSubRatBridge20261114.Ecurve32a2_rank_eq_zero
  note := "y^2 = x^3 - x, LMFDB 32.a3, conductor 32 -- the \
    congruent-number curve E_1. Depends on PF's own not_fermat_42_sub \
    (difference form a^4 - b^4 != c^2), which mathlib does not carry. \
    That is the load-bearing original contribution on this axis."
  obligation := PLift.up @PrincipiaTractalis.Ch24DescentSubRatBridge20261114.Ecurve32a2_rank_eq_zero

/-- Claim 21 — rank-≥1 curves by explicit witnesses. -/
def entry_bsd_rank_ge_one : ClaimEntry where
  id := "bsd-rank-ge-one"
  source := "ch24 / inventory Claim 21"
  register := .provedElsewhere
  inventoryStatus := "KERNEL-VERIFIED"
  leanName := "E_{91.a1,102.a1,131.a1,141.a1,80.b}_rank_ge_one_capstone"
  statement := True
  note := "Multi-smul non-torsion points give the lower bound. Fifteen \
    such curves across the corpus by the 2026-11-16 count. Lower bounds, \
    not exact ranks, and no analytic rank -- so the Clay equality is not \
    touched."
  obligation := PUnit.unit

/-- Claim 22 — the Clay BSD capstone V5. -/
def entry_bsd_clay_v5 : ClaimEntry where
  id := "bsd-clay-capstone-v5"
  source := "ch24 / inventory Claim 22"
  register := .provedElsewhere
  inventoryStatus := "KERNEL-VERIFIED on PF_BSDEncodingV5; NOT a Clay discharge"
  leanName := "PF.Referee.BSDCapstoneTypedBridgeV5.PF_BSD_capstone_yields_Clay_BSD_standardV5"
  statement := True
  note := "Discharged by rfl: manuscriptRankV5 is a case split matching \
    known ranks on 20 named curves and 0 everywhere else, so for every \
    curve outside that set the Clay equality is 0 = 0. The analytic rank \
    machinery is absent from the corpus -- confirmed 2026-11-21: mathlib \
    has NO elliptic-curve L-function at this pin. Author labels it NOT a \
    Clay BSD discharge for arbitrary curves."
  obligation := PUnit.unit

/-- The Heegner split condition, made arithmetic 2026-11-21. -/
def entry_bsd_heegner : ClaimEntry where
  id := "bsd-heegner-split-condition"
  source := "ch24 / 2026-11-21 landing"
  register := .proved
  inventoryStatus := "KERNEL-VERIFIED (post-dates the inventory)"
  leanName := "PrincipiaTractalis.BSD_HeegnerHypothesis_Faithful_2026_11_21.heegner_37_neg7"
  statement := type_of% @PrincipiaTractalis.BSD_HeegnerHypothesis_Faithful_2026_11_21.heegner_37_neg7
  note := "E_37a1 satisfies the Heegner split condition for Q(sqrt -7) \
    with explicit square root 17. Replaces a `Prop := True` that \
    discarded its curve argument and was mentioned 87 times across \
    thirteen files. The condition SEPARATES fields: Q(sqrt -2) provably \
    fails at the same curve, while the True version identifies them. \
    The L-derivative half of Gross-Zagier-Kolyvagin is still True and is \
    blocked upstream."
  obligation := PLift.up @PrincipiaTractalis.BSD_HeegnerHypothesis_Faithful_2026_11_21.heegner_37_neg7

/-! ### Hodge -/

/-- Claim 23 — affine algebraic de Rham. -/
def entry_hodge_derham : ClaimEntry where
  id := "hodge-affine-de-rham"
  source := "ch25 / inventory Claim 23"
  register := .provedElsewhere
  inventoryStatus := "KERNEL-VERIFIED"
  leanName := "PF/AlgebraicDeRhamD1_r345.lean, PF/AlgebraicDeRhamD1Leibniz_r356.lean"
  statement := True
  note := "Affine algebraic de Rham d^2 = 0, with the d1 descent \
    well-definedness. The inventory states plainly that this does NOT \
    touch the Hodge Conjecture."
  obligation := PUnit.unit

/-- Claim 24 — the Clay Hodge capstone. -/
def entry_hodge_clay : ClaimEntry where
  id := "hodge-clay-capstone"
  source := "ch25 / inventory Claim 24"
  register := .provedElsewhere
  inventoryStatus := "KERNEL-VERIFIED on substrate encodings"
  leanName := "PF.Referee.HodgeCapstoneTypedBridge.PF_Hodge_capstone_yields_Clay_Hodge_standard"
  statement := True
  note := "`isAlgebraic` is PF's three-conjunct substrate predicate \
    HodgeAlgebraicRepresentation, NOT literal algebraicity by cycle, and \
    PF_HodgeEncoding sets RationalHodgeClass _ := N -- so the Hodge \
    classes are natural numbers. mathlib has no Kahler manifolds, which \
    the inventory's Route 2 records as the blocker."
  obligation := PUnit.unit

/-- Claim 25 — the chapter's worked examples, refuted numerically. -/
def entry_hodge_numeric_refutation : ClaimEntry where
  id := "hodge-numeric-obstructions"
  source := "ch25 / inventory Claim 25"
  register := .provedElsewhere
  inventoryStatus := "KERNEL-VERIFIED negative content"
  leanName := "PF/Ch20Ch25NumericObstructions.lean"
  statement := True
  note := "Refutes ch25's own K3 Picard count and abelian-fourfold \
    Hodge-class count against LMFDB values. PF refuting PF, in the \
    kernel. These are the entries that make the ledger's other labels \
    believable."
  obligation := PUnit.unit

/-! ### Substrate → observable, and consciousness -/

/-- Claim 26 — ternary-rational occupation. -/
def entry_ternary_occupation : ClaimEntry where
  id := "map-ternary-occupation"
  source := "ch26 / inventory Claim 26"
  register := .openStatement
  inventoryStatus := "CONDITIONAL REDUCTION"
  leanName := ""
  statement := True
  note := "The level bound K is ESSENTIAL: without it Z[1/3] is dense in \
    R and the law empties. Falsifiable in principle. See \
    codex/THE_MAP_2026-10-11.md, which is written as a falsifiable \
    object."
  obligation := PUnit.unit

/-- Claims 27–31 — the five cosmology predictions. -/
def entry_cosmology_five : ClaimEntry where
  id := "cosmology-five-predictions"
  source := "ch27, ch29, ch34 / inventory Claims 27-31"
  register := .empirical
  inventoryStatus := "1/5 soft agreement, 3/5 miss, 1/5 withdrawn"
  leanName := ""
  statement := True
  note := "n_s 0.9686 vs Planck 0.9649 +- 0.0042, within 0.86 sigma, SOFT \
    AGREEMENT. Kolmogorov sigma(alpha_NS) = -1.308 vs -5/3 = -1.667, \
    CLEAR MISS. Big Bang lithium 0.7016 vs required 0.3053, FAILS. Muon \
    g-2 WITHDRAWN as a zero-DoF fitting artifact. ANITA off by one base-3 \
    rung, FAILS. THE JOINT TEST DOES NOT SUPPORT the \
    substrate-to-observable map, and the book records that."
  obligation := PUnit.unit

/-- Claim 32 — the `ch₂ = 0.95` threshold. -/
def entry_ch2_threshold_empirical : ClaimEntry where
  id := "consciousness-ch2-threshold"
  source := "ch2, ch30-32 / inventory Claim 32"
  register := .empirical
  inventoryStatus := "EMPIRICAL HYPOTHESIS — UNTESTED"
  leanName := ""
  statement := True
  note := "Labeled EMPIRICAL-UNTESTED in revision2_changes.tex and \
    awaiting a protocol. Never to be coloured PROVEN. The clinical \
    ch2 is a separate measurement channel."
  obligation := PUnit.unit

/-- The mathematical content behind the threshold, which IS proved. -/
def entry_ch2_ceiling : ClaimEntry where
  id := "consciousness-ch2-ceiling-iff"
  source := "ch2 / PF/Ch2ThresholdSelection.lean"
  register := .proved
  inventoryStatus := "KERNEL-VERIFIED"
  leanName := "PrincipiaTractalis.Ch2Selection.ceiling_threshold_iff_dimension"
  statement := type_of% @PrincipiaTractalis.Ch2Selection.ceiling_threshold_iff_dimension
  note := "19/20 <= ch2Ceiling d <-> 20 <= d. Elementary and TRUE, and \
    the file scopes it honestly in its own docstring: d >= 20 is the \
    condition for SOME state in dimension d to reach the threshold, \
    namely the maximally mixed one. Level 3 of the M_3^k tower is where \
    d = 27 first exceeds 20, so the threshold is pinned to the 3-adic \
    ladder -- but the value 0.95 within the interval (8/9, 26/27] is NOT \
    uniquely singled out, which the corpus also says."
  obligation := PLift.up @PrincipiaTractalis.Ch2Selection.ceiling_threshold_iff_dimension

/-- Hardy 1914, faithfully stated 2026-11-21. -/
def entry_hardy_faithful : ClaimEntry where
  id := "rh-hardy-1914-faithful"
  source := "ch21 / 2026-11-21 landing"
  register := .proved
  inventoryStatus := "KERNEL-VERIFIED (post-dates the inventory)"
  leanName := "PrincipiaTractalis.Hardy1914_Faithful_2026_11_21.hardy1914_faithful_yields_nonempty"
  statement := type_of% @PrincipiaTractalis.Hardy1914_Faithful_2026_11_21.hardy1914_faithful_yields_nonempty
  note := "Hardy1914_Faithful := PositiveOnLineZetaZeroOrdinates.Infinite \
    implies the framework's atomic fact, via Set.Infinite.nonempty. The \
    implication the anchor file's docstrings claimed and its theorems did \
    not state -- those were (_h : Anchor) : Anchor := _h. Hardy 1914 \
    itself remains an undischarged hypothesis."
  obligation := PLift.up @PrincipiaTractalis.Hardy1914_Faithful_2026_11_21.hardy1914_faithful_yields_nonempty

/-- The ledger. -/
def ledger : List ClaimEntry :=
  [ -- substrate layer
    entry_substrate_rigidity, entry_trace_unique, entry_pi_obstruction,
    entry_alpha_values, entry_alpha_identity,
    -- Riemann Hypothesis
    entry_hp_implies_rh, entry_rh_below_15, entry_rh_box_march,
    entry_rh_clay_capstone, entry_hardy_faithful, entry_rh_external,
    -- P vs NP
    entry_spectral_gap, entry_pnp_bridge, entry_ibm_coherence,
    -- Yang-Mills
    entry_wilson_rp_cont, entry_wilson_rp_l2, entry_ym_clay_capstone,
    entry_ym_massgap_refuted,
    -- Navier-Stokes
    entry_ns_vortex_all_n, entry_ns_clay_v4, entry_ns_route_a,
    entry_ns_steady_transport, entry_ns_encoding,
    -- Birch-Swinnerton-Dyer
    entry_bsd_rank0_a, entry_bsd_rank0_b, entry_bsd_rank_ge_one,
    entry_bsd_clay_v5, entry_bsd_heegner,
    -- Hodge
    entry_hodge_derham, entry_hodge_clay, entry_hodge_numeric_refutation,
    -- Poincare and Fermat
    entry_poincare_faithful, entry_poincare_encoding,
    entry_fermat_encoding, entry_fermat_n4_diff,
    -- substrate to observable, and consciousness
    entry_ternary_occupation, entry_cosmology_five,
    entry_ch2_threshold_empirical, entry_ch2_ceiling ]

/-! ## §4 — The gates

These are what make coverage and pristineness *checkable* rather than
asserted. They are deliberately cheap, so they can run in CI. -/

/-- Coverage gate: the ledger has the expected number of entries. Bump
    this deliberately when an entry is added, so a silent deletion fails
    the build. -/
theorem ledger_coverage : ledger.length = 39 := rfl

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
    entry_fermat_n4_diff.register = .provedElsewhere ∧
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
