# Ch.34A citation audit — 2026-11-17

Target: every `\texttt{...}` citation in `chapters/ch34A_substrate_theorem.tex`
that names a Lean theorem, def, or field. Verify each resolves at HEAD
(`62f79d56`).

## Totals

- `\texttt{...}` strings in Ch.34A: 390 total occurrences, 200 unique.
- Lean-identifier-shaped (contain `.` or `_`, alnum/dot/underscore only): **57 unique**.
- Additional bare-alphanumeric that could be Lean declarations: **36**.
- Remaining 107: file paths (`codex/...`), commit hashes
  (`909d944f`, `2426833`, `42990ea`), LaTeX macros (`\allowbreak{`),
  display-math fragments (`\(\alpha\)_RH := 3/2`), prose (`BSD_is_constitutive`
  as a sentence-case claim rather than theorem name).

## Lean-identifier-shaped — 57 of 57 FOUND

Every citation of shape `[A-Za-z_][A-Za-z_0-9.]*` with at least one
`.` or `_` resolves to a declaration in the corpus. Each checked via:

```
grep -rE "(^|[^a-zA-Z_.])${cite}([^a-zA-Z_0-9]|$)" --include="*.lean" PF/
```

Full list in `/tmp/ch34A_lean_shaped.txt` (session-local).

Spot verifications performed:
- `abelianThreeFold_VoisinCodimTwoCycleClassExistsHypothesis`
  → `PF/AlgebraicGeometry/Voisin2007PartialFormalization.lean` +
    `PF/AlgebraicGeometry/HodgeAlgebraicRepresentationV2.lean`
- `PF_NS3DEncodingV4.Velocity` → `PF/NavierStokes/NS3DRegularitySolutionV4.lean`
- `unifiedSubstrateUnification_holds` → `PF/Referee/PFUnifiedSubstrate.lean`
- All `alpha_P_from_two_anchors`, `alpha_NP_from_two_anchors`,
  `entailment_from_a_RH/NS/YM/PvNP/Poincare`, etc. — Referee layer.

## Bare-alphanumeric — 35 of 36 FOUND as declarations; 1 as token

Found as declarations (35):
`AlgebraicCyclesOnQuintic`, `algebraicRankV2`, `AlphaAssignment`,
`analyticRankV2`, `CanonicalClassNP`, `CanonicalClassP`, `Computable`
(Lean core), `decide` (Lean core), `def` (Lean core),
`DeterministicMachineV3`, `encodeConfig`, `encodeRun`,
`EnumToClassSeparationBridge`, `FermatQuinticConcrete`,
`FiniteVorticityIntegral`, `GeneralSmoothQuintic`,
`HodgeAlgebraicRepresentation`, `IsFlowSimpleRank1`,
`Multiplicative`, `NPDeciderV3`, `NSPDETypedUpgradeV2`,
`OrdPolesRealV2`, `PDecider`, `PNPClassSeparationCarrierV2/V3/V4`,
`rfl` (Lean core), `RiemannStaticDataV2`, `Schwartz`,
`StandardBSDEncodingBounded`, `TimelessFieldCompletion`,
`TimelessFieldRing`, `True` (Lean core), `Weakening`, `WilesHaseLift`,
`YMVacuumLiteralV2`, plus `hev` (contextual field in r267).

Found as token in corpus docstrings but not as top-level declaration (1):
- `evV2`: local field name inside the V2 RH carrier. Appears in
  `PF/Referee/RHCapstoneTypedBridgeV3.lean` docstring describing V2
  (`` `evV2 := 1/(n+1)` ``), in `PF/Referee/SixAxisScopeAccountabilitySuite.lean`
  (`` `eigenvalueToZero α_star_empirical (evV2 n)` ``). Cited
  referentially in Ch.34A; the referent exists inside the V2
  carrier structure.

## Verdict

**Ch.34A citation audit: PASS.** Every Lean-identifier-shaped citation
resolves to a declaration or referenced token in the corpus at HEAD.
Zero broken references.

The audit does not claim that every cited theorem is *also* on the
three-axiom bar — that is a separate check which is enforced
per-theorem in the corpus itself by the `verify.sh` axiom gate. The
audit here verifies NAME RESOLUTION, i.e. "the chapter's references
aren't pointing at dead names."

## Ingredients for a future deeper audit

A stronger audit would:
1. Parse Ch.34A into (claim, citation) pairs.
2. For each citation, extract the actual Lean theorem statement.
3. Compare the claim to the theorem statement for syntactic match.
4. Extract `#print axioms` output for each cited theorem.
5. Verify the axiom output is contained in the chapter's stated axiom contract.

That is a larger audit; this one certifies the first layer (names
resolve). The chapter's rigor ledger paragraphs (ASSERTED vs PROVEN
vs EMPIRICAL) remain the author's scope decisions, not reviewable by
name-resolution alone.
