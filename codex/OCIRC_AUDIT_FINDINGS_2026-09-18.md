# O-CIRC mechanical audit — first findings, 2026-09-18

Tool: `PF/Audit/PremiseAudit.lean`, command `#audit_premises`.
Obligation: `UNIFIED_THEORY_PROOF_PROGRAM.md` §3.1 — premise-vs-conclusion
containment must be checked **mechanically, not editorially**.

## Validation before use

| target | expected | reported |
|---|---|---|
| `T_infinity_rigidity`, pre-r337 | `trace_unique` dead | exactly that, 1 finding, cone 1753 |
| `T_infinity_rigidity`, post-r337 | clean | CLEAN, cone 1543 |

The four load-bearing fields (`tower`, `tower_matrix`, `tower_mono`,
`tower_dense`) are correctly reported live in both runs. No false positives.

## Finding 1 — `r301` assumes the Riemann Hypothesis, by four routes

Target: `principia_fractalis_millennium_supreme_capstone_universal_at_HEAD`,
the theorem presented as the total Millennium position of the framework.
Five distinct findings.

**Two premises are literally the conclusion.** Both fields have a type
definitionally equal to the RH conjunct
`∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1/2`:

- `ClayClosureBundleUniversal.aggregate.riemann1859_original_conjecture`
- `ClayClosureBundleUniversal.aggregate.bombieri2000_clay_official`

**Neither is named in §3.1.** The bundle hands the theorem RH and the theorem
hands RH back. This is the bluntest form the defect can take.

**Two further routes reach RH by one step of modus ponens:**

- `bulletproof.rh_hp_T3sym_positive` with `bulletproof.rh_hp_program_positive : A → RH`
  — the route §3.1 documented
- `bulletproof.rh_hp_T3sym_positive` with `mayer1991_cohen2025 : A → RH`
  — a second, independent route, also unnamed in §3.1

**One premise is definitionally its own advertised conclusion, the D2 pattern:**

- `hardy1914 : ∃ x, x ∈ PositiveOnLineZetaZeroOrdinates`

matching `UNIFICATION_COUNTERMODEL_LEDGER.md:57-62`, which recorded that the
Hardy citation returns one of its own inputs. Confirmed mechanically.

## What this changes

§3.1 called the circularity obligation the sharpest one and documented a single
route. There are four, and two of them require no reasoning at all to see once
the check is mechanical. The theorem remains **valid**; it carries no
information about RH. Any presentation of `r301` as a Millennium result must
carry that qualification, and the directive §12 prohibition on conditional
uniqueness whose premises encode the target applies to it directly.

## What was NOT found

`T_infinity_rigidity` is clean after r337. The central theorem does not have this
defect. That is the distinction that matters: the rigidity result and the Clay
capstone are not in the same evidential class, and this audit is the mechanical
demonstration of it.

## Limits

DEAD means no proof in the analysed cone mentions the field; removal is still a
human edit that must rebuild. Descent stops at the namespace boundary.
CONTAINED uses `isDefEq` at default transparency plus one modus-ponens step: it
finds `rfl`-identity and one-step circularity, not semantic circularity needing
real reasoning. Absence of findings is therefore not proof of non-circularity.

---

# Corpus sweep, 2026-09-18

## Finding 2 — the `MinimalRigidityForces*` family: 35 of 35 have findings, 0 clean

Every built member of the family was audited (35 of 37; two modules have no
olean in the ch2 worktree and were skipped).

| | count |
|---|---|
| targets audited | 35 |
| CLEAN | **0** |
| with findings | **35** |
| DEAD lines | 70 |
| CONTAINED lines | 15 |
| VACUOUS lines | 0 |

**70 DEAD lines is exactly two per theorem**, and they are the same two every
time:

- `UnifiedMinimalInvariants.sector1_minimal`
- `UnifiedMinimalInvariants.sector2_minimal`

These are the minimal-rigidity hypotheses — the thing the family is named after.
**In all 35 theorems, neither is consumed by the proof.** Whatever these results
establish, minimal rigidity is not what establishes it.

## Finding 3 — the α-skeleton identities are assumed, not forced

`cross_millennium_shared_invariants_substrate_capstone` concludes six identities
and takes all six as premise fields, each definitionally equal to a conjunct of
its own conclusion:

| premise field | = conclusion conjunct |
|---|---|
| `sector2_minimal.inv_P_sq_YM` | `a_P ^ 2 = a_YM` |
| `sector2_minimal.inv_QG_sq_two_pi` | `a_QG ^ 2 = 2 * π` |
| `sector2_minimal.inv_Hodge_quad` | `a_Hodge ^ 2 = a_Hodge + 1` |
| `sector1_minimal.inv_NS_BSD` | `a_NS = 2 * a_BSD` |
| `sector1_minimal.inv_YM_Poincare` | `a_YM = a_Poincare + 1` |
| `sector2_minimal.inv_NP_minus_Hodge` | `a_NP - a_Hodge = 1 / 4` |

Assume the six identities, conclude the six identities. This is the mechanical
confirmation of the standing editorial verdict in
`ALPHA_RIGIDITY_AUDIT_REPORT_2026-09-07.md:242-246` — that the α-skeleton is a
*presentation* of the values, not a derivation — now with declaration-level
precision.

## Finding 4 — the Poincaré anchor is a hypothesis

`perelman_anchored_cascade_substrate_capstone` reports

```
CONTAINED hypothesis is definitionally a conjunct of the conclusion:
          u.sector1.a_Poincare = 1
```

`α_Poincaré = 1` is assumed and then concluded. The Perelman "anchor" anchors
nothing: no property of Perelman`s theorem is used, and the value is an input.
Both minimal-rigidity fields are also dead here.

## Finding 5 — headline capstone sweep, 18 targets

5 CLEAN, 13 with findings; 24 DEAD and 18 CONTAINED lines in total.

CLEAN: `..._supreme_capstone_at_HEAD` (r256), `..._extended_at_HEAD` (r273),
`..._extended_v2_at_HEAD` (r299), `millennium_rh_substrate_position_at_HEAD`
(r255), `six_millennium_problems_via_fractal_resonance`,
`all_clay_via_soundness_and_capstones`.

With findings: the r301 universal capstone (§ Finding 1), the four
`SubstrateRigidity*Capstone` Referee theorems, `MinimalSubstrateRigidityUnified`,
the six-axis master capstone, `RHCapstoneTypedBridgeV3`,
`PNPCapstoneTypedBridge`, `principia_fractalis_millennium_capstone`,
`all_clay_typed_via_soundness_and_capstones`.

**Note on naming.** The Referee-tier `SubstrateRigidity*Capstone` theorems are
NOT the central theorem. `T_infinity_rigidity` in `PF/SubstrateRigidity.lean` is,
and it audits CLEAN. The two must not be conflated in any external presentation.

## Standing verdict

The kernel-verified rigidity result and the Referee-tier "rigidity forces X"
family are in different evidential classes, and that is now a mechanical fact
rather than a judgement call. Nothing in this sweep touches the validity of any
theorem: every one of them is true. What the sweep measures is how much they
say.

---

# Full corpus capstone sweep, 2026-09-18

Every built capstone-class theorem in the corpus: 169 of 177 candidate modules
have oleans in the ch2 worktree; the sweep imports all 169 and audits every
theorem whose name contains `apstone` and which takes at least one hypothesis.

| | count |
|---|---|
| targets audited | **213** |
| CLEAN | **99** |
| with findings | **114** |
| DEAD | 432 |
| CONTAINED | 138 |
| VACUOUS | 1 |

## Two measurement corrections made before these numbers were trusted

Both were caught by checking the tool against results already known, and both
would have misreported the corpus if left in.

1. **Mathlib noise inflated DEAD from 432 to 583.** The first full run audited
   the fields of *any* structure appearing as a hypothesis type, including
   `Real.cauchy` (30 hits), `Finset.val`/`Finset.nodup` (24), `Complex.im` (12),
   and `WeierstrassCurve.a₂…a₆` (55). Those are mathlib data structures, not
   premise bundles anyone authored. Now filtered to project structures only.
2. **The first filter was too aggressive and hid the sharpest finding.** The
   corpus uses *two* root namespaces, `PrincipiaTractalis` and `PF`. Filtering on
   the first alone dropped every `PF.Referee.*` bundle — including
   `UnifiedMinimalInvariants`, which carries the family result — and reported
   DEAD=142 instead of 432. Fixed to accept both roots.

Regression suite held across both changes: `T_infinity_rigidity` CLEAN, and the
`substrate_capstone` family still 28 targets / 0 clean / 56 DEAD.

## The single VACUOUS field in the corpus

`PrincipiaTractalis.HodgeMumfordAbelianFirstPrinciplesInventory.MumfordFirstPrinciplesPrerequisites.p8_mumford_capstone`
**reduces to `True`.** Its sibling fields `p4_pontryagin`, `p5_kunneth`,
`p6_cycle_class_map` and `p7_hodge_pontryagin` are all DEAD in the same bundle.
The "Mumford first principles prerequisites" bundle is largely inert and its
capstone field assumes nothing.

## Highest finding counts

| findings | declaration |
|---|---|
| 17 | `PF.Referee.BSDCapstoneTypedBridgeV4.v4_CM_batch_surfaced` |
| 16 | `…MumfordFirstPrinciplesPrerequisites.p8_mumford_capstone` |
| 15 | `HilbertPolyaIdentificationPreciseCapstone.{PF,C,BK,BC}_typed_prop` (four) |
| 12 | `PF_RH_V4_MasterCapstone.V4_via_{T3sym,Mayer1991,Connes,BostConnes,BerryKeating}` (six) |

The `RHCapstoneTypedBridgeV4` cluster is notable: six separately named "routes"
to RH, each carrying 12 findings, which is the same pattern r301 showed at the
top level — multiple advertised independent routes that are the same assumption
wearing different names.

## Reading the 99 clean

CLEAN means no premise of that theorem is dead, definitionally a conclusion
conjunct, one modus-ponens step from one, or reducible to `True`, within the
analysed cone. It is not a certificate of substance: a theorem can be clean and
still say very little. The number to weigh is the 114, not the 99.

---

# Triage 1 — the RH "five routes" are one modus ponens

`PF/Referee/RHCapstoneTypedBridgeV4.lean`, structure `PF_RH_V4_MasterCapstone`.
Highest-count cluster in the corpus sweep: six theorems at 12 findings each.

## What the bundle advertises

Five separately named routes to the Riemann Hypothesis, each with a citation:

| field | route |
|---|---|
| `V4_via_Mayer1991` | Mayer 1991, Bull. AMS 25:55-60 transfer operator |
| `V4_via_T3sym` | PF / T3sym |
| `V4_via_BerryKeating` | Berry–Keating Hamiltonian |
| `V4_via_Connes` | Connes trace formula |
| `V4_via_BostConnes` | Bost–Connes KMS phase transition |

## What they are

Every one has the same shape:

```lean
V4_via_X : X → HilbertPolyaProgramConjecture → Clay_RiemannHypothesis_Standard
```

and `HilbertPolyaIdentificationPrecise.lean:515-516` gives

```lean
def HilbertPolyaProgramConjecture : Prop :=
  PF_T3SymIsHilbertPolyaOperator → RiemannHypothesis
```

So `V4_via_T3sym` unfolds to

```
PF_T3Sym → (PF_T3Sym → RH) → RH
```

which is `fun h hp => hp h`. **Modus ponens. There is no mathematics in it.**

The other four differ only in the first hypothesis — and the bundle's own field
`V4_five_formulation_equivalence` asserts all five of those hypotheses are
*mutually equivalent*:

```
BerryKeating ↔ Connes ↔ BostConnes ↔ PF_T3Sym ↔ Mayer1991
```

So the structure itself states that the five routes are the same proposition
under five names. They are not five independent confirmations of anything.

## What the auditor saw, and why it was right

Each `V4_via_X` theorem reports 11 DEAD and 1 CONTAINED. The 11 dead fields are
the other routes, the equivalence, and the four partial-surjectivity fields —
carried in the bundle, consumed by nothing. The single CONTAINED is the modus
ponens that does all the work:

```
PF_T3SymIsHilbertPolyaOperator  with  HilbertPolyaProgramConjecture  yields
∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1/2
```

## Scope — what is NOT being claimed

The corpus does not conceal this. `PF/Referee/RHRouteScopeAccountability.lean:33`
records `(G3) HilbertPolyaProgramConjecture := PF_T3SymIsHilbertPolyaOperator → …`
in plain text. Every field of `PF_RH_V4_MasterCapstone` is a hypothesis, and the
structure is honestly typed as such. The theorems are **valid**.

The defect is at the presentation tier: a bundle of assumptions named after five
famous programmes reads, to anyone not unfolding definitions, as five
independent routes to RH. It is one assumption, asserted five ways, plus the
implication that discharges it.

## Consequence

Any external presentation that cites the V4 master capstone as evidence about RH
is citing `fun h hp => hp h`. This is the same defect as r301 (Finding 1), one
tier down, and it is the first thing an outside reader would reach for.

---

# Triage 2 — the four "formulations" are one definition, and it contains no operator

`PF/Analytic/HilbertPolyaIdentificationPrecise.lean`. Four theorems at 15
findings each — the second-largest cluster, and the root cause of Triage 1.

## Five famous names, one proposition

| name | file:line |
|---|---|
| `BerryKeatingHamiltonianHypothesis` | `HilbertPolyaIdentificationPrecise.lean:224` |
| `ConnesTraceFormulaHypothesis` | `:261` |
| `BostConnesKMSPhaseTransition` | `:300` |
| `PF_T3SymIsHilbertPolyaOperator` | `:340` |
| `Mayer1991_SymmetricQuotientHasZetaSpectrum` | `Mayer1991TransferOperatorFormalization.lean:303` |

All five have **the same body**, character for character apart from the bound
variable name:

```lean
∃ ev : ℕ → ℝ,
  ZetaZeroOrdinateValid ev ∧
  ZetaZeroOrdinateComplete ev ∧
  (∀ k, 0 < ev k)
```

The corpus proves the identification by `Iff.rfl`
(`Mayer1991TransferOperatorFormalization.lean:359-361`), and its own docstring
says "both encode the same spectrum-equals-oracle content."

## What the shared proposition actually says

Unfolding `ZetaZeroOrdinateValid` and `ZetaZeroOrdinateComplete`
(`OnLineSurjectivitySubDecomposition.lean:144-151`):

```
∃ ev : ℕ → ℝ,
  (∀ k, riemannZeta ⟨1/2, ev k⟩ = 0) ∧
  (∀ t, riemannZeta ⟨1/2, t⟩ = 0 → ∃ k, ev k = t) ∧
  (∀ k, 0 < ev k)
```

*There exists a positive sequence enumerating exactly the on-line zeta zeros.*

**There is no operator anywhere in it.** No Hamiltonian, no self-adjoint
operator, no trace formula, no KMS state, no transfer operator. It is an
enumeration existential about zeros on the critical line, and it says nothing
whatever about zeros off the line.

So `PF_T3SymIsHilbertPolyaOperator` does not state that `T₃^sym` is a
Hilbert–Pólya operator. `T₃^sym` does not occur in it. The "precise
identification" identifies nothing, because there is nothing on either side to
identify.

## What the four 15-finding theorems are

`HilbertPolyaIdentificationPreciseCapstone` fields K1–K4:

```lean
BK_typed_prop : BerryKeatingHamiltonianHypothesis → BerryKeatingHamiltonianHypothesis
C_typed_prop  : ConnesTraceFormulaHypothesis      → ConnesTraceFormulaHypothesis
BC_typed_prop : BostConnesKMSPhaseTransition      → BostConnesKMSPhaseTransition
PF_typed_prop : PF_T3SymIsHilbertPolyaOperator    → PF_T3SymIsHilbertPolyaOperator
```

Each is `P → P`, i.e. `fun x => x`. Provable for any proposition whatsoever.
Their docstrings say "X is a valid Lean Prop", which is true and carries no
information.

Field K5 `formulations_equivalent` is then a conjunction of four `Iff`s between
definitionally identical propositions — `Iff.rfl` four times.

The "routes" `PF_T3SymIsHilbertPolyaOperator_via_BerryKeating` / `_via_Connes` /
`_via_BostConnes` (`RHPvsNPPairedClosure.lean:147-162`) are `.mp` applications of
those `Iff.rfl` chains: the identity function, again.

## How this generates Triage 1

Triage 1 reported that the five V4 routes to RH are one modus ponens. This is
why: the five first-hypotheses are one definition, so
`V4_five_formulation_equivalence` is `rfl`, and the five routes are five spellings
of `fun h hp => hp h`.

## Scope — stated fairly

The corpus does not conceal any of this. `Mayer1991TransferOperatorFormalization.lean:359`
labels the identification "literally"; `RHPvsNPPairedClosure.lean:145-146` states
"NOT an unconditional RH discharge — the hypothesis IS the 1991-99 published
Hilbert-Pólya conjecture." Every theorem is valid. Nothing is mislabelled inside
Lean.

The defect is that five definitions named after Berry–Keating, Connes,
Bost–Connes, Mayer and the framework's own operator are one enumeration
existential, and no reader who does not unfold them can see that. Any external
claim that the framework "identifies its operator with the Hilbert–Pólya
operator", or that it has "four independent formulations", does not survive
unfolding.

---

# Triage 3 — the BSD multi-CM batch rests on four false hypotheses

`PF/Referee/BSDCapstoneTypedBridgeV4.lean`, `v4_CM_batch_surfaced` — the single
highest-scoring declaration in the corpus sweep at 17 findings.

## The predicate does not mean what it is named

`hasCM` (`PF/BSDCoatesWilesRankZeroAttempt.lean:125-130`):

```lean
noncomputable def hasCM : WeierstrassCurve ℚ → Prop :=
  fun E => E.a₁ = E_rank_zero.a₁ ∧ E.a₂ = E_rank_zero.a₂ ∧
           E.a₃ = E_rank_zero.a₃ ∧ E.a₄ = E_rank_zero.a₄ ∧
           E.a₆ = E_rank_zero.a₆
```

This is not complex multiplication. It is **coefficient-wise equality to one
fixed curve**. The corpus says so itself in the docstring immediately above:
"returns `True` for `E_rank_zero` … and `False` elsewhere … a one-curve
LMFDB-anchored encoding."

## The four hypotheses are therefore false

| curve | (a₁, a₂, a₃, a₄, a₆) |
|---|---|
| `E_rank_zero` | (0, 0, 0, **−1**, **0**) |
| `E_36a1` | (0, 0, 0, **0**, **1**) |
| `E_49a1` | (1, −1, 0, −2, −1) |
| `E_121b1` | (0, −1, 1, −7, 10) |
| `E_144a1` | (0, 0, 0, **0**, **−27**) |

None equals `E_rank_zero`. So `hasCM E_36a1` unfolds to a conjunction containing
`(0 : ℚ) = −1` and `(1 : ℚ) = 0`. **False.** Same for the other three.

`v4_CM_batch_surfaced` takes all four as hypotheses. Its statement is therefore
**vacuously true and permanently undischargeable**: no one can ever supply the
premises, because they are false propositions.

Confirmed by search: the only `hasCM` fact ever *proved* anywhere in the corpus
is `hasCM_E_rank_zero` (`:132`). `hasCM E_36a1` and its three siblings occur
only ever as hypotheses, and `v4_CM_batch_surfaced` is never instantiated by any
other declaration.

## What the conclusion measures

`manuscriptRankV4` (`BSDCapstoneTypedBridgeV4.lean:184-186`) is a lookup table —
`if E = E_rank_zero then 0 …`. So `manuscriptRankV4 E = 0` is settled by literal
curve equality, not by any rank computation. Nothing about Mordell–Weil rank is
computed on the four curves.

## Where this differs from Triages 1 and 2

Those were circular: true premises that contain the conclusion. This one is
**vacuous**: premises that cannot hold at all. A reader seeing "the typed
rank-zero Mordell–Weil Prop holds on each of the four additional CM curves"
would reasonably take it as a result about four curves with complex
multiplication. It is an implication whose antecedent is false, about a
five-coefficient equality test named `hasCM`.

## Scope — stated fairly

The file is named `…RankZeroAttempt.lean`, the docstring is explicit about the
one-curve encoding and marks the default "OPEN", and the theorem is valid Lean.
Nothing is concealed at the definition site. The defect is that a predicate
named `hasCM` is applied to four curves it is false on, four tiers away from the
docstring that says so, and the resulting theorem is presented as a batch result
about CM curves.

## Recommendation

Either rename `hasCM` to what it is (`isERankZeroCurve`, say) so the batch
statement reads as the tautology it is, or withdraw `v4_CM_batch_surfaced` and
the `BSD_MultiCMRankZeroBatch` results until a real CM predicate exists. Leaving
the name as `hasCM` guarantees the next reader makes the same misreading.
