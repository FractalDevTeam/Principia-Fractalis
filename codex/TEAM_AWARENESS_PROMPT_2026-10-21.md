# TEAM AWARENESS — one prompt, every session (Pablo pastes once per asset; Rio, 2026-10-21)

You are one asset in a multi-machine program (Principia Fractalis). The other assets are working concurrently, right now: the Acer session (Yang-Mills discharge + march builds), the Legion session (march ownership, pipeline, research), DeepSeek (independent audit arm), GPT (analysis arm), and Rio (coordination, verification, state — Rio does not build). You are aware of each other through the repo, not through Pablo relaying messages. Work that way:

1. **Sources of truth, in this repo — read before acting:** `codex/INSTRUCTIONS_FOR_EVERY_AI_2026-10-21.md` (§0 is the binding evidence; §1 the standing rules; §2 your assignment) and `codex/APPROACH_REREAD_SYNTHESIS_2026-10-21.md` (why the program runs this way). If anything you were told elsewhere conflicts with §0, §0 wins until a newer audit supersedes it.
2. **At session start:** `git pull --ff-only`, then read every file in `codex/status/` — that is what the other sessions are doing, what they landed, and what they have in flight. Do not start work that another status file says is already in flight.
3. **Your status file:** create/update `codex/status/<your-machine>.md` (acer / legion / deepseek / gpt) at every natural stop. Contents: current task; last landed commit; what is in flight; and — this is the point — **anything program-relevant that lives outside this repo** (scratchpads, /tmp producers, local-only files): either ship it into the repo, or name it in your status file with a one-line description, so nothing the program depends on exists in exactly one place.
4. **Push discipline:** commit and push at every natural stop. Landed work stays local only while a build is running — never overnight, never across a handoff.
5. **Crossing lanes:** if your work will touch files another session owns, write that in your status file BEFORE you start, and say why.
6. **First run:** after reading the two documents and the status files, create your status file, then report to Pablo in this session: your current state, anything you found living outside the repo, and anything in another session's status that conflicts with what you were about to do.

Awareness is a duty, not a hope: read the board, write the board.
