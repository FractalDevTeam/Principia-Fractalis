# Producer runner repair verification — 2026-10-21

Private engineering evidence for Pablo. This does not establish RH or a Clay result.

## Inputs and regeneration

- Concurrent session's input commit: `ab2a4586e48f6cbe226f20d6b7b19b2374ba2374`.
- All nine actual committed template files match the deployed `/tmp/prod` input MD5 manifest. See `committed-input-verification.json`.
- Repository producer regenerated c=7, r=1/16, D=1: **16/16 Lean files byte-identical to the landed pack**, with individual SHA-256 values in `c7-regression.json`. Generated run metadata is excluded explicitly. This is a source comparison, not a fresh c=7 kernel build.
- Explicit test invocation: `python3 codex/gen_box.py --c 81/8 --r 1/16 --density 2 --out <isolated-directory> --work <isolated-directory>`; no `--extend-midpoint` or automatic radius selection.
- D=2 box criterion: Mc lower bound ≈0.02315941, L0*r ≈0.00624767, raw ratio ≈3.7. No 1.25 safety factor was applied. The superseded fixed-3/4 target fails; the current parameterized box criterion passes.
- The D=2 test source pack was **not landed** in the shared Lean tree or this commit. The tested CoreDefs/Seg01 source hashes are attached.

## Runner and acceptance gate

`march_box.sh` now uses the repository producer, with `/tmp/prod` retained as a commented fallback. `check_march_axioms.py` checks assemble, gate-pilot and unconditional-pilot logs independently. Each source `#print axioms` directive must have a matching output record, in order, with exactly `{propext, Classical.choice, Quot.sound}`. Missing/malformed/extra prints, wrong declarations and unexpected axioms fail.

The checker regression tests passed (valid wrapped output; rejection cases for empty, missing, extra, malformed, wrong-name, forbidden, unknown, missing-axiom and duplicate-axiom evidence). `bash -n` passed for the runner. Actual pre-existing c=75/8 logs passed: assemble 7, gate 4, unconditional 25 declarations. Those logs were replayed, not newly built.

The existing Acer c=19/2 shell retained its original script inode/content; the repaired runner was atomically published on a new inode for subsequent invocations. That c=19/2 run completed with the original unconditional-only axiom gate. Expanded-gate acceptance must not be retroactively attributed to it.

## Native D=2 Seg01 test

Host: Legion Ubuntu WSL. Lean `v4.24.0-rc1`; mathlib `eed770a434957369c6262aa3fb1d6426419016d4`. `lake exe cache get` exited 0 (7,199 files unpacked). Source checkout exported from Acer HEAD `08637e085608fc86a06170ecdd5cbcab665f6cdd`; nine repaired template inputs are as above. Existing non-target dependency oleans were transferred from Acer, while the generated test target oleans were excluded. This is not a rebuild of every dependency or the PF.lean closure.

Builds ran serially under the Legion's local `/tmp/pf_lean_build.lock`, using `taskset -c 0,1 lake env lean -o ...`. No Acer build was launched by this session. Each result includes `/usr/bin/time -v` output in its attached log.

| Target | Exit | Elapsed | Peak RSS | Printed axiom checks |
|---|---:|---:|---:|---|
| CoreDefs_c81_8 | 0 | 11.99 s | 2,838,048 KiB | No separate headline axiom claim |
| Seg01Range_c81_8 | 0 | 8m11.36s | 13,069,216 KiB (12.46 GiB) | 54/54 exactly the three-axiom set |
| Seg01Midpoint_c81_8 | 0 | 8m20.98s | 13,826,896 KiB (13.19 GiB) | 4/4 exactly the three-axiom set |

**Result:** requested Seg01 pack passed, with 58 source-matched axiom records on exactly `[propext, Classical.choice, Quot.sound]`. This does not validate the remaining D=2 modules, assemble, gate or unconditional pilot. It is not a complete D=2 box acceptance. The measured memory does not establish the old 7.6 GB/module planning assumption at D=2; these are Legion measurements, not Acer measurements, and density causation is not isolated without a same-host comparison.

## Remaining

- Full native c=7 validation has not run; cache setup succeeded. Its waiting queue was cancelled before compilation to avoid duplicating work while shared-session routing is unresolved.
- No Acer-odd/Legion-even allocation or D=2 band launch has occurred in this session.
- Coordinate that allocation with Pablo/the existing session before launching a competing band runner. Other session's producer changes and unrelated dirty work were preserved.
- No public comment or push was made by this session.
