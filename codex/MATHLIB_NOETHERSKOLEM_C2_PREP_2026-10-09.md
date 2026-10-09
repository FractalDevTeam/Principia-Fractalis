# Mathlib Noether–Skolem / amplification candidate — prep record, 2026-10-09

Prepared to the **pre-push edge only. Nothing submitted, nothing built beyond one
single-file elaboration, nothing wired into PF.lean.**

## The decision this prep turned on
"Contribute the C2 arc to mathlib" → the file's own 2026-10-05 header said to
re-check against master first. Done (read master source via GitHub):

- Master **has** the automorphism case: `StarAlgEquiv.eq_linearIsometryEquivConjStarAlgEquiv`
  (PR #33017), `AlgEquiv.eq_linearEquivConjAlgEquiv` (PR #28100) — both require `f`
  bijective (an equivalence).
- Master does **not** reach the rectangular unital-*-hom case `Mₙ(ℂ) → M_{kn}(ℂ)`
  (`k>1`, injective-not-surjective). That is the novel delta and the genuine
  contribution: `unital_star_hom_inner_unique` + the block-diagonal amplification
  classification.

So the headline "Noether–Skolem" would have been a redundant PR; the real
contribution is the amplification/embedding rigidity.

## Measured this session (not relayed)
`lake env lean` (single file, `taskset -c 0,1`) on `PF/Upstream/NoetherSkolemC2.lean`
+ `#print axioms`: EXIT 0, 0 errors, 0 sorryAx. `unital_star_hom_inner_unique`,
`blockDiagonalStarAlgHom_unital`, `phiONB_family_orthonormal`,
`unitaryOfONBpair_isUnitary` each → `[propext, Classical.choice, Quot.sound]`.
**Against the pin `eed770a4` only** — not master.

## Artifacts staged
- `mathlib_candidates/NoetherSkolemAmplification.lean` — copy of the verified
  arc, proof region byte-identical (checked), new PR-oriented docstring. Keeps
  the `PrincipiaTractalis.SubstrateRigidity` namespace (rename is pending work).
- `mathlib_submission/body_noetherskolem.md` — PR draft, marked NOT SUBMITTED.
- Original `PF/Upstream/NoetherSkolemC2.lean` untouched.

## Remaining before this is a real PR (none done, none fakeable without a master build)
1. Rebuild + re-verify against mathlib **master**.
2. mathlib naming/placement; bundle conclusion via `unitary`/`conjStarAlgEquiv`.
3. Confirm master has no rectangular/amplification form anywhere.
4. CLA, fork, PR — external submission, author-gated + multi-model vetting per
   the standing mission rule. `mathlib_submission/submit_pr.sh` exists; it is
   NOT to be run without that gate.
