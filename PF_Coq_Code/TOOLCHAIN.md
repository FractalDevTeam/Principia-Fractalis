# `PF_Coq_Code` — Toolchain

Operational reference for building the Coq/Rocq tree. Verified 2026-10-07 on `acer`.

## Required compiler: Rocq 9.1.0 (opam `default` switch)

```
$ eval $(opam env) && coqc --version
The Rocq Prover, version 9.1.0
compiled with OCaml 4.14.1
```

**`coqc --version` must print `9.1.0`. If it prints `8.18.0`, stop — nothing you build
will be usable.**

## `eval $(opam env)` is mandatory, not a convenience

The machine has a **second, wrong** Coq ahead of the opam switch on `PATH`:

```
$ which coqc
/usr/bin/coqc
$ /usr/bin/coqc --version
The Coq Proof Assistant, version 8.18.0
```

`/usr/bin/coqc` (the distro package, Coq 8.18.0) **shadows** the opam `default` switch.
Without `eval $(opam env)` every `coqc` / `coqq_makefile` / `coqdep` call silently uses
8.18.0. There is no error and no warning — you only find out later, because:

- 8.18.0 has **no mathcomp**, so `PF_Real/` cannot build at all under it; and
- the `.vo` files it writes are **binary-incompatible** with 9.1.0 and vice versa.

So: prefix **every** Coq command in this tree with `eval $(opam env) &&`.

## `.vo` files are not portable between the two toolchains

A `.vo` carries its compiler's version number in its header. The two are mutually
unreadable. This is exactly how the shadowing was discovered — asking 8.18.0 to load a
`.vo` that 9.1.0 had written:

```
$ /usr/bin/coqc -Q .../PF_Coq_Code/PF_Real PFReal t.v
File "./t.v", line 1, characters 0-38:
Error:
File .../PF_Coq_Code/PF_Real/Base3Tower.vo
has bad version number 90100 (expected 81800). It is corrupted or was
compiled with another version of Coq.
```

`90100` = Rocq 9.1.0, `81800` = Coq 8.18.0. The failure is loud **only** at load time.
Consequence: **never mix**. If you suspect a mixed tree, delete all
`*.vo *.vok *.vos *.glob .*.aux` under `PF/` and `PF_Real/` and rebuild under one
toolchain. (`.vo` are gitignored and fully regenerable, but archive before deleting:
`tar czf /tmp/pf_coq_vo_$(date +%F).tgz` the set you are about to remove.)

## Installed library set (opam `default` switch)

| Package | Version |
| --- | --- |
| `rocq-core` / `coq-core` / `coq` / `coqide-server` | 9.1.0 |
| `rocq-stdlib` / `coq-stdlib` | 9.0.0 |
| `rocq-mathcomp-{boot,ssreflect,order,fingroup,algebra,solvable,field}` | 2.5.0 |
| `rocq-hierarchy-builder` | 1.10.1 |
| `rocq-elpi` | 3.2.0 |
| `coq-coquelicot` | 3.4.4 |
| `coq-flocq` | 4.2.1 |
| `coq-interval` | 4.11.3 |
| `rocq-bignums` / `coq-bignums` | 9.0.0+rocq9.1 |

`PF_Real/` needs mathcomp (`From mathcomp Require Import all_ssreflect all_algebra`),
which exists **only** in this switch.

## Build

```sh
eval $(opam env) && \
cd '/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Coq_Code' && \
make -f Makefile.coq -j 8 -k
```

`Makefile.coq` is generated, not hand-written. After editing `_CoqProject`, regenerate it:

```sh
eval $(opam env) && coq_makefile -f _CoqProject -o Makefile.coq
```

`_CoqProject` declares two logical roots — keep `PF` first:

```
-Q PF PrincipiaTractalis
-Q PF_Real PFReal
```

683 `.v` files: 679 under `PF/` (the shape-index tree — see `PF/README.md`) and 4 under
`PF_Real/` (the real proofs). `coq_makefile` emits a harmless
`Warning: No common logical root. ... -docroot` because of the two roots; it affects only
the unused `install-doc` target.

## Known toolchain-specific failure modes

The two compilers have **complementary** failures. Neither builds the whole tree.

**1. Under 8.18.0 — `PF_Real/` cannot build at all.** No mathcomp in that installation
(`/usr/lib/ocaml/coq/user-contrib/` contains only `Ltac2`). All four real-proof files fail
at their `From mathcomp Require Import` line:

```
Error: Cannot find a physical path bound to logical path
all_ssreflect with prefix mathcomp.
```

Unfixable in 8.18.0, and the primary reason 9.1.0 is the required toolchain.

**2. Under 9.1.0 — the Stdlib reorganisation moved names out of transitive scope.**
Observed in `PF/Analytic/LogZBookNeZero.v`:

```
The variable Z_lt_le_dec was not found in the current environment.
```

`Z_lt_le_dec` was **not** removed; it still lives in `ZArith_dec`
(`Stdlib.ZArith.ZArith_dec`). In 8.18.0 `Require Import Coq.Reals.Reals` dragged it in
transitively; in 9.1.0 it does not. Fix: name the module explicitly.

```coq
Require Import Coq.ZArith.ZArith_dec.
```

The `Coq.*` prefix is a deprecation-warning-only compatibility alias for `Stdlib.*` in
9.x, and is the real path in 8.18.0 — so this spelling compiles under **both**.
If another file in this tree reports "variable X was not found" under 9.1.0, suspect the
same cause before suspecting the proof:
`grep -rl 'X' $(coqc -where)/user-contrib/Stdlib --include='*.v'`.

**3. Expected noise under 9.1.0 (not failures).** `From Coq` →
`From Stdlib` deprecation warnings across `PF/`, and mathcomp 2.5.0
`notation-overridden` / `ambiguous-paths` / `comRingType is deprecated` warnings in
`PF_Real/`. All are warnings; the build exits 0.

## Checking the real proofs are axiom-free

Each `PF_Real/` file ends with `Print Assumptions` calls, so a normal build prints the
evidence. To re-check a specific result out of band:

```sh
eval $(opam env) && mkdir -p /tmp/chk && cd /tmp/chk && \
printf 'From PFReal Require Import Base3Tower MatrixTracialUnique WeylAveraging.\nPrint Assumptions base3_tower_step_capstone.\nPrint Assumptions normalized_trace_is_unique_tracial_functional.\nPrint Assumptions weyl_average.\n' > CheckAssumptions.v && \
coqc -Q '/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Coq_Code/PF_Real' PFReal CheckAssumptions.v
```

Each must report `Closed under the global context`.
