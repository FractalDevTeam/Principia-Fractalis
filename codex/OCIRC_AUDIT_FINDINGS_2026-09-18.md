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
