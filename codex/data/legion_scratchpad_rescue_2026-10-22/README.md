# Legion scratchpad rescue, 2026-10-22

Session-scratchpad files that existed **only** in
`C:\Users\psolo\AppData\Local\Temp\claude\...\scratchpad` — a session-scoped
temp directory. "Trivially rewritten" is not a protection strategy, so they are
here.

## How the set was chosen — measured, not guessed

Every `.py`/`.sh`/`.lean`/`.md` file in the scratchpad was md5-hashed (223
files) and compared against the md5 of **all 9942 tracked files** in this repo.
**114 had no content match anywhere in the repo** and are preserved here.

The other 109 are byte-identical to something already committed — the
scratchpad is largely a staging mirror — so they need no rescue.

## What is here

* `unmatched_scratchpad_2026-10-22.tar.gz` — **all 114** unmatched files, one
  archive, 164 KB. Nothing from the measured set is omitted.
* `MANIFEST.txt` — md5, size and name of all 114, so the archive's contents are
  inspectable without unpacking it.
* `tools/` — the ten files with ongoing reuse value, kept **readable** rather
  than only archived:

  | tool | what it is for |
  |---|---|
  | `chain91.py` | the 91a1 doubling orbit in exact rationals; computes `x(2ⁿP)` and the heights that pick the threshold shift. Produced the orbit quoted in `E91a1RankOneCapstone_2026_10_22` |
  | `check_mkall.py` | finds every ordering inversion in a mathlib `Mathlib.lean` — i.e. what `mk_all --check` objects to — with no Lean build. Found #42100's single inversion |
  | `check_comments.py` | Lean block-comment **nesting** checker. Lean comments nest, so prose quoting a comment opener swallows its own terminator; this cost one build lock cycle |
  | `scan_bs.py` | LaTeX doubled-backslash scanner. Found the build-breaking `\\subsection` in ch24 |
  | `bstest.py` | runs `pdflatex` on minimal documents to *measure* what that doubled backslash does, instead of asserting it |
  | `probe_buggy.py` | reverts the CI gate parser to its buggy form to prove fixture F5 actually discriminates |
  | `verify_rank0.py`, `curveA_bezout.py`, `e11a1_check.py`, `nodal_check.py` | BSD-side arithmetic probes (rank-0 checks, the Bézout cofactors for curve A, an 11a1 check, a nodal-sector check) |

## On "the BSD falsification script"

The sweep instruction named a "BSD falsification script" and a "91a1 constant
probe". The 91a1 constant probe is `chain91.py` — that one exists under that
description. **There is no single file by the name "BSD falsification
script"**; the BSD-side checking was spread across the four arithmetic probes
listed above plus two *Lean* artifacts that are already committed
(`NonTorsionFromOrbitCheck_2026_10_21.lean`, which re-derives E43a1's landed
capstone through the universal route as a faithfulness test, and
`BSD_RANKSIGN_REFUTED`-related notes). Naming this rather than quietly shipping
something and calling it that.

## What was deliberately NOT surfaced as readable files

Superseded intermediates, kept in the archive only: nine successive drafts of
the status board (`legion.md` … `legion8.md`), script iterations
(`mb.sh`/`mb2.sh`, `build55*.sh`, `build_c7*.sh`, `price4/5/6.py`), one-shot
patch appliers whose effects are already committed and whose logic is quoted in
the relevant commit messages (`fix_42093.py`, `fix_42100.py`,
`fix_ch24_bs.py`, `fix_commit_box.py`, `fix_selftest.py`, `patch_*.py`), and
`bad_probe.lean` (a deliberately broken file used to prove a checker fails on
known-bad input).

Also note `gen_box.py`, `gen_box_part2.py`, `march_box.sh` and `commit_box.sh`
appear in the unmatched set only because the **repo copies are newer** — they
were edited in place on the Acer. The repo versions are authoritative; the
archived copies are the older scratchpad staging versions.

Verify with `sha256sum -c SHA256SUMS`.
