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
