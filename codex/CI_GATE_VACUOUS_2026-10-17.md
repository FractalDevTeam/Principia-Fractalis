# CI diagnosis: the axiom gate cannot fail on axiom content under ANY input — and that is a stronger defect than the one hypothesised

**Date:** 2026-10-17 (Legion, verification on Acer). Diagnosis + proposed patch.
**NOT APPLIED** — CI touches the public surface; this is a proposal.
Labels FACT / MEASURED / JUDGEMENT.

**Headline: DeepSeek's hypothesis is correct but incomplete.** The empty-log
path is real (CASE A below). But the verdict logic is *also* independently
broken: **a project axiom on a single line — the exact case the gate was written
to catch — passes too** (CASE B). The two defects are independent, and either
alone makes the gate unable to fail.

> **`UNEXPECTED_AXIOMS` is unconditionally empty. The gate has never been
> capable of failing on axiom content.**

---

## 1. Verified facts

**CI outcomes — measured independently of the report.** `gh run list
--workflow=verify.yml --limit 400`:

| conclusion | count |
|---|---|
| cancelled | **396** |
| failure | 3 |
| in_progress | 1 |
| **success** | **0** |

Corroborates the 697/690/5 figures in shape and confirms **0 successes**.

**The 3 failures are fast, not timeouts.** Run `36613793838`: created
`18:40:57`, updated `18:42:13` — **76 seconds**, in `Run ./verify.sh`. Its logs
have since expired, so **I am not claiming to know why it failed**; see §4.3 for
a latent defect found by reading, offered as a candidate rather than a cause.

## 2. Defect 1 — the transcript is empty. MEASURED

`PF.lean` imports all three axiom-check modules, at lines **1355–1357**, each
tagged `-- 2026-08-10 orphan sweep`:

```
import PF.AxiomCheck_2026_06_23        -- 2026-08-10 orphan sweep: ...
import PF.AxiomCheck_All_2026_06_25    -- 2026-08-10 orphan sweep: ...
import PF.AxiomCheck_Lambda_2026_06_24 -- 2026-08-10 orphan sweep: ...
```

So step `[2/4]`'s `lake build PF` builds them as dependencies, and step `[3/4]`'s
`lake build PF.AxiomCheck_*` finds them up to date.

**Demonstrated on Acer** against the already-built tree:

```
$ lake build PF.AxiomCheck_2026_06_23 | grep -c "depends on axioms"
0
```

(The olean dates from Oct 7; lake replays *some* modules' messages but not this
one's.) So `AXIOM_LOG` is empty, and the `|| true` on each of the three build
lines also swallows any genuine build failure.

> **JUDGEMENT — the provenance matters and should be recorded.** The gate
> *worked* until 2026-08-10. Before that sweep the AxiomCheck modules were
> orphans, so building them in step 3 actually elaborated them and emitted the
> transcript. **A well-intentioned tidy-up — importing orphans into `PF.lean` —
> silently disabled the gate.** Nothing announced it, because a gate that
> checks nothing reports PASS.

## 3. Defect 2 — the verdict logic can never produce output. MEASURED

The pipeline is an allowlist applied as a **line deleter**:

```bash
grep -E "depends on axioms:" "${AXIOM_LOG}" \
  | grep -vE "propext|Classical\.choice|Quot\.sound" \
  | grep -v "Hardy1914_..." | ... || true
```

`grep -v` deletes any line *containing* an allowed name. **Every real axiom line
contains `propext`. So every line is always deleted, whatever else is on it.**

Run against the script's exact pipeline (`codex/ci_gate_selftest.sh`):

| case | transcript | gate verdict |
|---|---|---|
| **A** | empty (what CI actually produces, §2) | **PASS** |
| **B** | `'PF.headline' depends on axioms: [propext, Classical.choice, myProjectAxiom, Quot.sound]` | **PASS** ← the case it was built to catch |
| **C** | same, but Lean wrapped the list across 4 lines | **PASS** |
| **D** | `sorryAx` on a wrapped continuation line | **PASS** |
| **B4** | 4 records, one carrying `myProjectAxiom`, single line | **PASS** |
| **C4** | 4 records, one carrying `myProjectAxiom`, wrapped | **PASS** |
| **D4** | 4 records, one carrying `sorryAx`, wrapped | **PASS** |

**B4/C4/D4 are the sharpest form.** Those transcripts are *well formed and
adequately populated* — four records each, no empty-log excuse — and one record
in each carries a genuine violation. The old logic passes all three. So the
defect is not about the transcript being empty; it is about the verdict logic
being unable to reject anything.

**B is the finding.** A genuine project axiom, on one line, in a non-empty
transcript, is not detected — because its line also mentions `propext` and is
therefore discarded whole.

**C and D compound it:** Lean *does* wrap long axiom lists (every
`#print axioms` I ran this week wrapped), and continuation lines do not contain
`depends on axioms:`, so the first `grep` never selects them. The offending
axiom is examined by no filter at all.

**Consequence:** `exit 2` is unreachable. The script's only reachable exits are
`0` (always, on axioms) and `1` (build failure).

## 4. Three further defects, found by reading

### 4.1 `cancel-in-progress: true` explains 396/400 cancellations — FACT

```yaml
concurrency:
  group: verify-${{ github.ref }}
  cancel-in-progress: true
```

Every push to `master` cancels the running job. With a ~10–60-minute build and
today's push cadence (this session alone pushed ~12 commits to master), runs
never survive to completion. **This is the direct cause of the cancellation
rate, and it is independent of the vacuity.**

### 4.2 The cache is never populated — FACT, and it is a vicious cycle

```yaml
key: lake-${{ runner.os }}-${{ hashFiles(...) }}-${{ github.sha }}
```

`github.sha` is unique per commit, so **the primary key can never hit** — every
run falls through to `restore-keys`. Worse: a cache is only *saved* at
successful job end. Cancelled jobs don't save, and the failed run's step list
shows `Post Cache mathlib + project build: skipped`.

> **So: no run completes → no cache is saved → every run builds mathlib cold →
> no run completes.** The cancel-in-progress setting and the cache design keep
> each other broken.

### 4.3 `PATH` is exported only on the install path — latent, offered as a candidate

```bash
ELAN_BIN="${HOME}/.elan/bin/lake"
if [[ ! -x "${ELAN_BIN}" ]]; then
  ... install elan ...
  export PATH="${HOME}/.elan/bin:${PATH}"   # <-- only inside this branch
fi
...
"${HOME}/.elan/bin/lake" env lake build PF   # inner `lake` resolved via PATH
```

When the elan cache restores (so `ELAN_BIN` exists), the branch is skipped and
`PATH` is never exported. The outer `lake` is absolute, but the **inner** `lake`
in `lake env lake build` resolves via `PATH`. `lake env` does prepend the
toolchain bin, so this may well work — **I could not confirm it either way
because the failed run's logs have expired, and I am not asserting it caused the
76-second failure.** It is a real asymmetry regardless and the patch removes it
(along with the redundant `lake env lake` doubling).

## 5. Would the proposed gates pass today? Yes — checked. MEASURED

A proposal that instantly reds the build is not actionable, so I checked:

* **`native_decide`**: 353 files mention it, **0 use it in tactic position**.
  All 353 are prose ("no `native_decide`").
* **`sorry` / `admit`**: 264 grep hits, essentially all prose — "ZERO `sorry`s",
  "No sorry", and the English verb ("whether they *admit* a bounded residual").

> **So the gates below go green on today's tree — provided they are
> comment-aware.** A naive source grep would fire on the project's own honesty
> statements, which is why §6 catches `sorry` *semantically* via `sorryAx` in the
> axiom transcript and treats the source grep as belt-and-braces only.

## 6. Proposed patch — `verify.sh`

Replace steps `[3/4]` and `[4/4]` with the following. Four changes:
**force elaboration**, **parse structurally**, **fail if nothing was checked**,
**keep the transcript**.

```bash
# --- Axiom check on the headline theorems ------------------------------
echo "[3/4] Running #print axioms on the headline theorems..."
AXIOM_LOG="${REPO_ROOT}/axiom-transcript-${GITHUB_SHA:-local}.txt"
: > "${AXIOM_LOG}"

# `lake build` is a NO-OP when the module is already built (PF.lean imports
# all three), which is what made this gate vacuous. `lake env lean` always
# elaborates and always emits. No `|| true`: a failure here is a failure.
AXIOM_MODULES=(
  "PF/AxiomCheck_2026_06_23.lean"
  "PF/AxiomCheck_Lambda_2026_06_24.lean"
  "PF/AxiomCheck_All_2026_06_25.lean"
)
for M in "${AXIOM_MODULES[@]}"; do
  echo "        elaborating ${M}"
  if ! "${HOME}/.elan/bin/lake" env lean "${M}" >>"${AXIOM_LOG}" 2>&1; then
    echo "FATAL: ${M} failed to elaborate. Transcript: ${AXIOM_LOG}" >&2
    exit 1
  fi
done

# --- Verdict -----------------------------------------------------------
echo "[4/4] Verdict:"
MIN_RECORDS=4   # fewer than this means the gate checked (almost) nothing

python3 - "${AXIOM_LOG}" "${MIN_RECORDS}" <<'PYEOF'
import re, sys

log_path, min_records = sys.argv[1], int(sys.argv[2])
text = open(log_path, encoding="utf-8", errors="replace").read()

ALLOWED = {
    "propext", "Classical.choice", "Quot.sound",
    # the four named conditional hypotheses, per paper section 5
    "Hardy1914_published_theorem_substrate_citation",
    "Mayer1991_Cohen2025_substrate_HP_program_citation",
    "Mayer1991_Cohen2025_T3_sym_HP_program_citation",
    "framework_substrate_pins_bulletproof_bundle",
}

# DOTALL so a WRAPPED axiom list is captured as one record.
REC = re.compile(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", re.DOTALL)

records = REC.findall(text)
violations = []
for name, body in records:
    axioms = [a.strip() for a in body.split(",")]
    axioms = [a for a in axioms if a]
    bad = sorted(set(a for a in axioms if a not in ALLOWED))
    if bad:
        violations.append((name, bad))

print("  records parsed: %d (minimum required: %d)" % (len(records), min_records))

# THE LINE THAT WAS MISSING: a check that checks nothing must FAIL.
if len(records) < min_records:
    print("  FAIL: the axiom transcript contains %d records, fewer than the %d"
          % (len(records), min_records))
    print("        required. The gate did not check what it claims to check.")
    print("        (Historically this happened because PF.lean imports the")
    print("         AxiomCheck modules, making `lake build` on them a no-op.)")
    sys.exit(3)

if violations:
    print("  FAIL: unexpected axiom dependencies:")
    for name, bad in violations:
        print("    %s  ->  %s" % (name, ", ".join(bad)))
    sys.exit(2)

print("  PASS: %d theorems checked; every axiom is in the allowlist." % len(records))
PYEOF
PY_STATUS=$?

# Belt-and-braces source scan. `sorryAx` is already caught semantically above;
# this catches a `sorry` in a module that no AxiomCheck file references.
# Comment-aware: the project's own headers say "ZERO `sorry`s" in prose.
echo "        scanning non-archive sources for sorry / admit / native_decide..."
STRAY=$(find PF -name '*.lean' -not -path '*/ARCHIVE/*' -print0 \
        | xargs -0 awk '
            { line = $0
              sub(/--.*/, "", line)                    # strip line comments
              if (line ~ /(^|[^A-Za-z_])sorry([^A-Za-z_]|$)/ ||
                  line ~ /(^|[^A-Za-z_])admit([^A-Za-z_]|$)/ ||
                  line ~ /native_decide/)
                printf "%s:%d: %s\n", FILENAME, FNR, $0 }' \
        | grep -vE '/- |^\s*\*' || true)
if [[ -n "${STRAY}" ]]; then
  echo "  FAIL: stray sorry / admit / native_decide in non-archive sources:"
  echo "${STRAY}" | sed 's/^/    /'
  exit 4
fi

echo ""
echo "  Transcript (keep this): ${AXIOM_LOG}"
exit ${PY_STATUS}
```

**Exit codes become meaningful:** `0` pass, `1` build/elaboration failure,
`2` unexpected axiom, **`3` gate checked nothing**, `4` stray `sorry`/`admit`/
`native_decide`.

## 7. Proposed patch — `verify.yml`

```diff
 concurrency:
   group: verify-${{ github.ref }}
-  cancel-in-progress: true
+  # Was `true`: every push to master cancelled the running job, which is why
+  # 396 of the last 400 runs are `cancelled` and none ever saved a cache.
+  cancel-in-progress: false

 jobs:
   verify:
     runs-on: ubuntu-latest
-    timeout-minutes: 60
+    timeout-minutes: 180

       - name: Cache mathlib + project build
         uses: actions/cache@v4
         with:
           path: |
             PF_Lean4_Code/.lake
-          key: lake-${{ runner.os }}-${{ hashFiles('PF_Lean4_Code/lean-toolchain', 'PF_Lean4_Code/lake-manifest.json') }}-${{ github.sha }}
+          # `github.sha` in the primary key made it unhittable by construction.
+          key: lake-${{ runner.os }}-${{ hashFiles('PF_Lean4_Code/lean-toolchain', 'PF_Lean4_Code/lake-manifest.json') }}
           restore-keys: |
             lake-${{ runner.os }}-${{ hashFiles('PF_Lean4_Code/lean-toolchain', 'PF_Lean4_Code/lake-manifest.json') }}-
             lake-${{ runner.os }}-

       - name: Run ./verify.sh
         run: |
           bash ./verify.sh
         shell: bash
+
+      - name: Upload axiom transcript
+        if: always()
+        uses: actions/upload-artifact@v4
+        with:
+          name: axiom-transcript-${{ github.sha }}
+          path: axiom-transcript-*.txt
+          if-no-files-found: error
+          retention-days: 90
+
+      - name: Self-test the gate's own failure paths
+        run: bash ./codex/ci_gate_selftest.sh --expect-fail
+        shell: bash
```

`if-no-files-found: error` is deliberate: no transcript means the gate did not
run, and that should be red.

## 8. One structural recommendation beyond the patch — JUDGEMENT

**Add a meta-test that the gate can fail.** The whole defect class here is "a
check that silently stops checking". The patch's `MIN_RECORDS` guard addresses
this run-to-run, but the durable fix is a test that feeds the verdict logic a
known-bad transcript and asserts it exits non-zero. `codex/ci_gate_selftest.sh`
(written for §3, extend with `--expect-fail`) is that test, and the workflow step
above runs it. **Without it, the next refactor can re-break the gate exactly as
the 2026-08-10 orphan sweep did, and nothing will say so.**

## 9. Scope and what is NOT claimed

* **Not applied.** Proposal only, per the order.
* The `[2/4]` build step is unchanged except for removing the `lake env lake`
  doubling; I have not re-timed a cold mathlib build to confirm 180 minutes is
  sufficient — **that number is a judgement, not a measurement.**
* **I do not know why the 3 runs failed in 76 seconds** (logs expired). §4.3 is a
  latent defect found by reading, not an attribution.
* The `awk` source scan strips `--` line comments but not nested `/- -/` blocks;
  it is deliberately the weaker, secondary check, with `sorryAx` in the axiom
  transcript as the authoritative one. If it proves noisy on block comments, the
  right fix is to drop the source scan, not to weaken the transcript parse.
* Noted in passing, not acted on: the build emits
  `PF/TransferOperator.lean:2397:17: Try this: ring_nf — The ring tactic failed
  to close the goal`. A live diagnostic, unrelated to this task.

---

## Label summary

* **FACT:** `PF.lean:1355–1357` imports with the `2026-08-10 orphan sweep` tags;
  the `concurrency`/cache/`PATH` configurations as quoted; 353 `native_decide`
  mentions with 0 tactic-position uses.
* **MEASURED (this session):** 396/3/1/**0** run conclusions over 400;
  the 76-second failure window; `grep -c "depends on axioms" = 0` on a built
  tree; the four-case self-test verdicts, all PASS.
* **JUDGEMENT (mine):** that CASE B is the headline and makes the defect
  unconditional rather than path-dependent; that the 2026-08-10 orphan sweep is
  the provenance; that the cancel-in-progress/cache pair is self-sustaining;
  that a gate needs a test that it can fail; the 180-minute figure.
* **NOT established:** the cause of the 3 fast failures; whether 180 minutes
  suffices for a cold build; whether the `awk` scan is quiet on block comments
  across all 1,200+ files.
