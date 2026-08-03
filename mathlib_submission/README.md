# Mathlib submission package — run from your laptop

Prerequisites (once): `gh auth login` with your GitHub account.

Then, from this directory:

```bash
./submit_pr.sh pr5    # Gram determinant => linear independence
```
wait for CI / review, then:
```bash
./submit_pr.sh pr7    # Hilbert-Schmidt operators on l^2
./submit_pr.sh pr8    # compact transfer operators (rides on pr7 if unmerged)
```

pr6 (TateLimit) is deliberately NOT here: its placement question is open on
Zulip ("Tate's telescoping limit — placement?"). Submit it after a maintainer
replies; tell Claude the reply and the script gets generated to match.

What the script does per PR: fork mathlib4 (idempotent), branch from master,
copy the candidate file to its target path, register the module in
Mathlib.lean (sorted), commit, push to your fork, open the PR with the
prepared body (which includes the standard AI-disclosure sentence in the form
grunweg accepted on #42093).

The script does NOT build mathlib locally (hours); mathlib CI builds the PR.
If CI reports a lint (e.g. maxHeartbeats policy), paste the log to Claude.
