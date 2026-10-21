#!/bin/bash
# Build the 10 modules missing from Seg01Midpoint_c7's 428-module closure on
# Legion, each under a hard 7 GB cap, STRICTLY ONE AT A TIME.
#
# Memory discipline, from the 2026-10-01 incident recorded in
# infrastructure_legion_lean_verify_tree: a backgrounded bash loop that the
# harness reports as killed KEEPS RUNNING on Windows. On that date a batch
# script survived 31 minutes invoking `lake build` on a loop, each invocation
# spawning ~29 lean workers at ~1.5 GB, against 31.4 GB of RAM -- available
# memory reached 51 MB.
#
# So this script:
#   * never calls `lake build` (which parallelises); only `lake env lean`, one
#     process per module, so a surviving loop can hold at most ONE lean;
#   * caps every invocation with -M 7000, so that one process is bounded;
#   * ABORTS if available memory falls below 4 GB, so a surviving loop stops
#     itself instead of competing with Pablo's working set;
#   * writes a pidfile so it can be killed by pid rather than by `pkill -f`,
#     which has killed my own ssh session three times.
set -u
T=/d/CLAUDE-i9/_tmp/pf-ocirc-verify-20261001/PF_Lean4_Code
LOG=/d/CLAUDE-i9/_tmp/legion_build10.log
ST=/d/CLAUDE-i9/_tmp/legion_build10_status
echo $$ > /d/CLAUDE-i9/_tmp/legion_build10.pid
cd "$T" || exit 1
export PATH="$HOME/.elan/bin:$PATH"
B=.lake/build/lib/lean
: > "$LOG"
echo RUNNING > "$ST"

MODS="
PF.Analytic.FourierPanels.FourierTermC2_2026_10_16
PF.Analytic.FourierPanels.FourierTermC2Minus_2026_10_17
PF.Analytic.R1Neighborhood_2026_10_09
PF.Analytic.EdgeSignNeighborhoods_2026_10_13
PF.Analytic.CenteredFormBridge_2026_10_13
PF.Analytic.PilotBoxes.R1_c0_5_r0_05_2026_10_13
PF.Analytic.Lambda0UniformBound_2026_10_14
PF.Analytic.Lambda0PrimeUniformBound_2026_10_14
PF.Analytic.Lambda0TightestBoundsMellin_2026_10_14
PF.Analytic.FourierPanels.Seg01Midpoint_c7_2026_10_20
"

avail_gb() {
  powershell.exe -NoProfile -Command \
    "[math]::Round((Get-Counter '\Memory\Available MBytes').CounterSamples[0].CookedValue/1024,1)" \
    2>/dev/null | tr -d '\r'
}

for m in $MODS; do
  a=$(avail_gb)
  case "$a" in ''|*[!0-9.]*) a=99 ;; esac
  if [ "${a%%.*}" -lt 4 ] 2>/dev/null; then
    echo "ABORT: only ${a} GB available, refusing to start $m" | tee -a "$LOG"
    echo "ABORTED low memory at $m" > "$ST"; exit 1
  fi
  src="PF/$(echo "$m" | sed 's/^PF\.//; s/\./\//g').lean"
  out="$B/$(echo "$m" | sed 's/\./\//g').olean"
  mkdir -p "$(dirname "$out")"
  s=$(date +%s)
  lake env lean -M 7000 -o "$out" "$src" > "/d/CLAUDE-i9/_tmp/lb_$(basename "$m").log" 2>&1
  rc=$?
  e=$(date +%s)
  echo "$m rc=$rc $((e-s))s avail_before=${a}GB" >> "$LOG"
  if [ $rc -ne 0 ]; then
    echo "FAILED $m" > "$ST"
    head -20 "/d/CLAUDE-i9/_tmp/lb_$(basename "$m").log" >> "$LOG"
    exit 1
  fi
done
echo DONE > "$ST"
