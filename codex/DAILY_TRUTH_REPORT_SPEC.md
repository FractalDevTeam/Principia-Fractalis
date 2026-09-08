# DAILY TRUTH REPORT — SPEC

**Opened 2026-09-07.** Dispatched by Pablo: *"add a gateway-health line to the
daily truth report spec."*

**No such spec existed.** I searched the repo, `D:\CLAUDE-i9`, the local mirror
and the gateway's own config and found nothing. Rather than skip the
instruction, this file opens the spec with the mandated line in it. **The scope
below is my proposal, not Pablo's — correct it freely.** Only §2 is his.

---

## 1. PURPOSE

One report per day whose only job is to say **what is actually true right now**,
including the things nobody asked about. Its value is not in confirming health;
it is in surfacing **silent failure** — a component that is down, doing nothing,
and generating no error anyone reads.

The governing case is the one that created this spec (§3).

---

## 2. MANDATORY LINES

### 2.1 Gateway health — REQUIRED

Every daily truth report carries a gateway-health line reporting, per component,
**up/down and how long**:

| component | probe | silent-failure risk |
|---|---|---|
| OpenClaw gateway | `127.0.0.1:18789` listening | **not a system service** — runs in a `systemd --user` session; nothing supervises it |
| GPU Ollama (fallback) | `127.0.0.1:11435` `/api/tags` | **the documented case** — a fallback nobody probes |
| snap Ollama | `127.0.0.1:11434` `/api/tags` | fallback-of-fallback |
| gateway crons | `openclaw cron list` — **status column, not existence** | a job can exist, fire on schedule, fail every time, and look scheduled |
| anthropic auth | key present? | absent by design; must not be reported as a fault, but its absence makes the local fallback load-bearing |

**The cron line reports consecutive-error counts, not just presence.** The
morning brief sat at `error (10x)` while `cron list` showed it correctly
scheduled with a sane next-run time. Existence is not health.

---

## 3. THE CASE THIS SPEC EXISTS FOR

**GPU Ollama was down from 2026-08-30 to 2026-09-07 — eight days — and nothing
reported it.**

- The Startup `.vbs` launched `start.sh` with `bWaitOnReturn=False`. `start.sh`
  backgrounds `ollama serve` via `setsid`; the transient `wsl.exe` session tore
  down and killed the not-yet-established child.
- `serve.log` is opened with `>`, which truncates on open. Because the child
  died before opening it, **the log was never even touched** — its mtime stayed
  at Aug 30. There was no error anywhere. The script appeared to succeed.
- The gateway's model chain is `anthropic/claude-sonnet-4-6` (no API key, by
  design) → `ollama/mistral:7b` → `ollama/llama3.2:3b`, both at `:11435`. With
  11435 dead, **every** link failed:
  `All models failed (3): … ECONNREFUSED 127.0.0.1:11435`.
- Morning brief reached `error (10x)`, night earnings check-in `error (11x)` —
  roughly one per day for eight days. Both kept their schedules and looked fine
  in any listing that did not read the status column.
- It surfaced only because a full-machine reboot prompted a manual sweep.

**Generalised failure class: a fallback that fails silently is worse than no
fallback**, because the system is designed to lean on it precisely when the
primary is unavailable — which here was *always*, the anthropic key being absent
by design. The whole chain was load-bearing on a dead port.

**What the truth report must therefore do:** probe *fallbacks* as first-class
components, and read *status*, not existence.

---

## 4. PROPOSED FURTHER LINES (not mandated — for Pablo's review)

- **Build halves** — `pf-c1`/`pf-c1-sup` per machine, driver version, last
  ledger event, escalation markers, OOM count since last driver change.
- **Box tally** — from `scripts/ledger_tally.py`, unique closure events only.
- **Kernel gate** — any theorem outside `[propext, Classical.choice, Quot.sound]`.
- **Toolchain** — active vs pinned per build root (`a1_v4` asserts this, so the
  report only needs to confirm the assert has not been bypassed).
- **Durability** — that ledgers and logs are on durable paths, and that the
  latest archive is no older than the last closure.
- **Public HEAD** — still `96c71da7`; any drift is an incident.

---

## 5. TONE RULE

The report states what is true, including when that is dull. "No change" is a
valid and useful daily report. What is not acceptable is a green line for a
component that was never probed — that is how eight days were lost.

---

*Opened 2026-09-07. §2 is mandated; the rest is a proposal awaiting Pablo's
correction. Public HEAD `96c71da7`. NO PUSH.*
