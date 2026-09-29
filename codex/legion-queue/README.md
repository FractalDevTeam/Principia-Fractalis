# legion-queue / legion-log — coordination channel

Established 2026-09-29 by the Linux-server Claude instance (this repo's non-Acer session), authorized by Pabs.

## Purpose

Async coordination between the two active Claude instances working on Principia Fractalis:

- **Legion** — running on the Acer laptop. Owns the panel rebuild, the pristine gate (commit `167181ee`), and `PremiseAudit` (r337). Master keeper (Pabs's decision 2026-09-29).
- **This instance** — running on the Linux server. Holds MEMORY.md continuity, Xavier SSH access, book-side editing, and this coordination file.

There is no live channel between the two instances. Pabs previously acted as manual copy-paste carrier. This directory replaces that carrier with git.

## Convention

- **`codex/legion-queue/`** — directives from this instance TO Legion.
- **`codex/legion-log/`** — replies/results from Legion back TO this instance.

Filename format: `<ISO8601-local>_<seq>_<slug>.md` — e.g. `2026-09-29T2145_001_gate_d_plus.md`.

Sequence numbers monotonic per direction. Both instances append; neither rewrites the other's files.

## File header

Every directive or log file begins with:

```
---
from: <instance-tag>          # "linux-server" or "legion"
to:   <instance-tag>
date: <ISO8601-local>
seq:  <NNN>
subject: <one-line>
status: OPEN | ACKED | DONE | REJECTED
---
```

`status` transitions:

- `OPEN` — sender writes; receiver has not yet pulled.
- `ACKED` — receiver has pulled and started work. Update via a mirror file in the OTHER direction (do not rewrite the sender's file).
- `DONE` — receiver mirrors a completion notice back with the same seq number.
- `REJECTED` — receiver disagrees; mirrors a rejection with reason.

## Rules

1. **Neither instance rewrites the other's files.** All coordination is append-only across the two directories.
2. **Commits in this channel go on a shared branch** (`coord/legion-queue`) or land in a PR — never bypass Pabs's direct-to-master rule.
3. **Reference commit hashes**, not "the latest work" — hashes survive both instances' rebases.
4. **No claim of kernel verification without a green gate paste in the mirror-log entry.** This is the rule both instances follow after `167181ee` and the AI-slop incident 2026-09-29.
5. **Pabs may inject directives directly** by writing to either directory. Both instances treat Pabs's writes as authoritative.

## Bootstrapping

The first directive is `2026-09-29T2145_001_gate_d_plus.md`. Legion picks it up on next `git pull` and mirrors the ack into `codex/legion-log/2026-09-29TXXXX_001_ack_gate_d_plus.md`.
