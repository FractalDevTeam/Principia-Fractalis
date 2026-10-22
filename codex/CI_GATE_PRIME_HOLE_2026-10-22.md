# The proposed CI axiom gate had a prime-name hole — found by measuring, 2026-10-22

**Status of the gate itself: UNCHANGED.** `verify.sh` and
`.github/workflows/verify.yml` are not touched by this note. Applying the gate
fix to CI remains Pablo's call, as recorded on 2026-10-17. What changed is the
*proposal* and its self-test, both of which were wrong in a way the self-test
could not see.

## The finding

`codex/CI_GATE_VACUOUS_2026-10-17.md` proposes replacing `verify.sh`'s
line-deleting allowlist with a structural, DOTALL parse of the axiom records.
The parser it proposes — also the one inside `codex/ci_gate_selftest.sh` — was:

```python
REC = re.compile(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", re.DOTALL)
```

Lean prints a declaration name inside single quotes. **When the name itself ends
in a prime, the printed form carries a doubled quote:**

```
info: PF/PointParallelogramUniversal_r199.lean:468:0:
  'PrincipiaTractalis.PointParallelogramUniversal.sub_ne_zero'' depends on axioms: [...]
```

`[^']+` stops at the prime *inside* the name, the required
`' depends on axioms:` does not follow, and the record **never matches**. It is
not reported as malformed — it is silently skipped. A `sorryAx` or project axiom
sitting in any `foo'` would pass the gate.

Primed names are ordinary Lean style, not a corner case.

## How it was found: measurement, not reading

The 10-17 note was written by reading the gate. This hole survived that reading
and survived the self-test. It surfaced only when the proposed logic was applied
to a **real** transcript — the 3421-job build of
`PF.E91a1RankOneCapstone_2026_10_22`:

```
records parsed, proposed parser : 551
lines selected, old line-grep   : 555
```

The proposal parsed FOUR FEWER records than the defective logic it replaces.
That discrepancy is what exposed the hole. The four:

| declaration | module |
|---|---|
| `DuplicationBezout37a1.reduced_height_bound'` | r131 |
| `E5077a1RankOne.reduced_height_bound'` | r144 |
| `QuasiParallelogramCerts5077a1.dvd_R6_of_dvd_forms'` | r157 |
| `PointParallelogramUniversal.sub_ne_zero'` | r199 |

## The fix

Anchor the name on the marker with a greedy `[^\n]+` rather than `[^']+`.
Newline-free keeps a name from swallowing its neighbours; `re.DOTALL` still lets
the axiom **list** wrap across lines, which was the original reason for DOTALL.

```python
REC = re.compile(r"'([^\n]+)' depends on axioms:\s*\[(.*?)\]", re.DOTALL)
```

With it, the same transcript parses **555 of 555** records — delta zero against
the old line-grep.

## The fixture, and why it needed five records

Fixture `F5_primed` in `codex/ci_gate_selftest.sh`: four clean records plus one
primed record carrying `sorryAx`, placed **last**.

The record count is load-bearing. A four-record fixture *including* the primed
one would be rejected by the `MIN_RECORDS` guard even with a broken parser —
passing for the wrong reason, which is the exact slip already recorded against
the first version of this self-test. With four clean records the guard is
satisfied, so the only thing that can fire is the axiom parser.

**Discrimination proved, not assumed** — same fixtures, only the parser changed:

| parser | F5 verdict | self-test |
|---|---|---|
| `[^']+` (as proposed 10-17) | `PASS` — wrong | FAILED, exit 1 |
| `[^\n]+` (fixed) | `FAIL(axiom)` | PASSED, exit 0 |

## What the measurement says about applying the fix

On the closure actually built (555 records, 3421 jobs) the fixed gate would go
**green**:

| count | axiom set |
|---|---|
| 522 | `[propext, Classical.choice, Quot.sound]` |
| 16 | `[propext]` |
| 16 | `[propext, Quot.sound]` |
| 1 | `[propext, Classical.choice]` |

Four distinct sets, every name inside the allowlist. The three smaller sets are
*subsets* of the bar, not violations — `decide`-closed arithmetic needs no
choice.

**Scope, stated honestly:** this is the import closure of one BSD capstone, not
the whole `PF` target. It does not license a claim about the entire tree; it does
show that the fixed gate is not sitting on a pile of violations in the part
measured.

## Still open in `verify.sh` — unchanged, Pablo's call

1. The allowlist is still applied as a **line deleter** (`grep -vE`), so
   `UNEXPECTED_AXIOMS` is unconditionally empty and `exit 2` is unreachable.
2. The transcript is still **empty**: `PF.lean` imports the three AxiomCheck
   modules (lines 1293, 1346, 1355–1357), so `lake build PF` has already built
   them and the three `lake build PF.AxiomCheck_*` calls are no-ops. `|| true`
   also swallows real failures.
3. `cancel-in-progress: true` (the 396 cancellations).
4. `github.sha` in the **primary** cache key, so it can never hit.

A gate that cannot fail issues a green badge for an unchecked claim. That is
still true today.
