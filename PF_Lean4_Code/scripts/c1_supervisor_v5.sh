#!/bin/bash
# c1_supervisor_v5.sh <scope> <root> <label> <boxk...>
#
#   scope: --user   systemd user units (Acer)
#          --system systemd system units
#          --plain  NO systemd: supervise a plain background process (WSL/Legion)
#
# Keeps the C1 rebuild alive. Three idle incidents in this campaign came from a
# worker dying or never being launched and nobody noticing for hours. A watcher
# that only reports is not enough - this one RESUMES.
#
# ===========================================================================
# v4 AMENDMENT (2026-09-07) — SAME FAILURE TWICE => ESCALATE, DO NOT RETRY
# ===========================================================================
#
# The 2026-09-07 Legion fan-out incident: the v2 supervisor restarted the driver
# SIX times between 04:55 and 05:55, each restart re-walking box 108's cached
# panels in ~4 minutes, logging "40/40 green", then hitting the same unbuilt
# box-0 closure and dying the same way. It exhausted MAXTRY=6 and exited as
# designed. Six restarts, zero progress, and the ledger gained six duplicate
# rows that would have corrupted the gate tally.
#
# The supervisor did its job and still could not help, because RESTARTING
# CANNOT FIX A DEFECT THAT RECURS ON EVERY START. Retrying is only correct for
# a transient death; for a deterministic one it burns the retry budget and
# hides the defect behind identical-looking log churn.
#
# Therefore: capture a SIGNATURE of each death (the last elaboration target the
# driver reported, plus the tail of its output). If two consecutive deaths carry
# the same signature, STOP and escalate - write an ESCALATION marker naming the
# repeated signature and exit non-zero. A human, or the orchestrator, then looks
# at a defect instead of at a retry count.
#
# This is strictly stronger than the MAXTRY cap, which only bounds how long the
# pointless retrying lasts. Both are kept: MAXTRY bounds transient churn,
# the signature rule catches determinism immediately.
# ===========================================================================
#
# lake skips already-built oleans, so a restart resumes rather than repeats.
set -u
SCOPE="$1"; shift
W="$1"; shift
LABEL="$1"; shift
BOXES="$*"
MAXTRY=6
DRIVER="$W/a1_v4.sh"
LEANROOT="$W/PF_Lean4_Code"
DURABLE="${PF_DURABLE:-$HOME/pf-rebuild}"
LEDGER="$DURABLE/a1_ledger.md"

mkdir -p "${PF_DURABLE:-$HOME/pf-rebuild}/r331b_logs"
LOG="$DURABLE/r331b_logs/c1_supervisor_${LABEL}.log"
OUTLOG="$DURABLE/r331b_logs/c1_$(echo "$LABEL" | cut -d- -f1).log"
PIDFILE="$DURABLE/pf_c1_${LABEL}.pid"
ESCALATION="$DURABLE/r331b_logs/ESCALATION_${LABEL}.md"

sc () {
  case "$SCOPE" in
    --user)   systemctl --user "$@" ;;
    --system) systemctl "$@" ;;
  esac
}

driver_alive () {
  if [ "$SCOPE" = "--plain" ]; then
    # Primary: the pidfile. Fallback: match the driver's own command line.
    # The fallback matters - a pidfile written by an outer wrapper shell can be
    # empty or stale, and a supervisor that then declares the driver dead will
    # happily start a SECOND one on top of the first. Two drivers on one tree
    # is worse than none.
    local p=""
    [ -f "$PIDFILE" ] && p=$(tr -dc '0-9' < "$PIDFILE")
    if [ -n "$p" ] && kill -0 "$p" 2>/dev/null; then return 0; fi
    p=$(pgrep -f "a1_v4.sh $LEANROOT" | head -1)
    if [ -n "$p" ] && kill -0 "$p" 2>/dev/null; then
      echo "$p" > "$PIDFILE"          # re-adopt and repair the pidfile
      return 0
    fi
    return 1
  else
    sc is-active --quiet pf-c1
  fi
}

# Signature of a death: the last target the driver was working on, plus a
# normalised tail of its output. Timestamps and durations are stripped so that
# "the same failure" compares equal across restarts.
death_signature () {
  { grep -oE 'RC [A-Za-z0-9_.]+ = [0-9]+' "$OUTLOG" 2>/dev/null | tail -1
    grep -oE '(QUEUE_FAIL|BRIDGE_FAIL|PREBUILD_FAIL|BOX0_[A-Z_]+FAIL)[^|]*' \
         "$OUTLOG" 2>/dev/null | tail -1
    tail -5 "$OUTLOG" 2>/dev/null | sed -E 's/[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9:+-]+//g; s/[0-9]+\.[0-9]+ s//g; s/maxRSS [0-9]+ kB//g'
  } | md5sum | cut -d' ' -f1
}

start_driver () {
  if [ "$SCOPE" = "--plain" ]; then
    setsid nohup /bin/bash "$DRIVER" "$LEANROOT" "$LEDGER" $BOXES \
      >> "$OUTLOG" 2>&1 &
    echo $! > "$PIDFILE"
    echo "SUPERVISOR: started driver pid $(cat "$PIDFILE") (plain) $(date -Is)" >> "$LOG"
  elif [ "$SCOPE" = "--user" ]; then
    systemd-run --user --unit=pf-c1 --collect --property=Type=simple \
      --property=CPUAffinity=0 \
      --property=StandardOutput=append:"$OUTLOG" \
      --property=StandardError=append:"$OUTLOG" \
      /bin/bash "$DRIVER" "$LEANROOT" "$LEDGER" $BOXES >> "$LOG" 2>&1
  else
    systemd-run --unit=pf-c1 --collect --property=Type=simple --property=User=xluxx \
      --property=WorkingDirectory="$W" \
      --property=CPUAffinity=0 \
      --property=StandardOutput=append:"$OUTLOG" \
      --property=StandardError=append:"$OUTLOG" \
      /bin/bash "$DRIVER" "$LEANROOT" "$LEDGER" $BOXES >> "$LOG" 2>&1
  fi
}

escalate () {
  local sig="$1" n="$2"
  cat > "$ESCALATION" <<EOF
# C1 SUPERVISOR ESCALATION — $LABEL — $(date -Is)

The driver died **$n times in a row with the same failure signature**:

    $sig

Restarting was stopped rather than continued. A death that reproduces exactly is
a defect, not a transient: retrying it burns the retry budget, makes no progress,
and adds duplicate rows to the ledger that corrupt the box tally.

This is the v4 amendment, adopted after the 2026-09-07 Legion fan-out incident,
where six identical restarts produced zero oleans.

## What to look at

    tail -80 $OUTLOG

Boxes: $BOXES
Driver: $DRIVER
Ledger: $LEDGER

**The supervisor has exited. Nothing is running for this half.**
EOF
  echo "SUPERVISOR: ESCALATED — same signature $n times ($sig) $(date -Is)" >> "$LOG"
}

echo "SUPERVISOR_START $(date -Is) label=$LABEL scope=$SCOPE driver=a1_v4 boxes=$BOXES cap=$MAXTRY policy=escalate-on-repeat" >> "$LOG"

tries=0
last_sig=""
repeat=0
while true; do
  sleep 120
  if grep -q "C1_BOXES_DONE" "$OUTLOG" 2>/dev/null; then
    echo "SUPERVISOR: $LABEL finished cleanly $(date -Is)" >> "$LOG"; exit 0
  fi
  if grep -q "C1_ABORT" "$OUTLOG" 2>/dev/null; then
    echo "SUPERVISOR: $LABEL aborted on a real build failure - NOT restarting $(date -Is)" >> "$LOG"; exit 1
  fi
  driver_alive && continue

  sig=$(death_signature)
  if [ "$sig" = "$last_sig" ]; then
    repeat=$((repeat+1))
  else
    repeat=1
  fi
  last_sig="$sig"

  # v4: a death that reproduces exactly is a defect. Escalate, do not retry.
  if [ "$repeat" -ge 2 ]; then
    escalate "$sig" "$repeat"
    exit 1
  fi

  tries=$((tries+1))
  echo "SUPERVISOR: driver down (sig $sig), resume $tries/$MAXTRY $(date -Is)" >> "$LOG"
  if [ "$tries" -gt "$MAXTRY" ]; then
    echo "SUPERVISOR: giving up after $MAXTRY resumes - needs a human $(date -Is)" >> "$LOG"; exit 1
  fi
  sleep 10
  start_driver
done
