#!/bin/bash
# c1_supervisor_v3.sh <scope> <root> <label> <boxk...>
#
#   scope: --user   systemd user units (Acer)
#          --system systemd system units
#          --plain  NO systemd: supervise a plain background process (WSL/Legion)
#
# Keeps the C1 rebuild alive. Three idle incidents in this campaign came from a
# worker dying or never being launched and nobody noticing for hours. A watcher
# that only reports is not enough - this one RESUMES.
#
# v3 change (2026-09-07). v2 hardcoded systemd-run for both halves. WSL has no
# systemd, so on the Legion `systemctl is-active` always failed AND the
# systemd-run restart path could not work: the supervisor could neither observe
# nor resume its driver, and - worse - the CPUAffinity=0 property it passed was
# silently never applied, leaving lake at nproc=24. That is the direct cause of
# the 2026-09-07 parallel fan-out incident. --plain supervises by PID instead.
#
# lake skips already-built oleans, so a restart resumes rather than repeats.
# Retries are capped: if the same OOM recurs, the module genuinely does not fit
# and that must be reported, not looped on.
set -u
SCOPE="$1"; shift
W="$1"; shift
LABEL="$1"; shift
BOXES="$*"
MAXTRY=6
DRIVER="$W/a1_v3.sh"
LEANROOT="$W/PF_Lean4_Code"
LEDGER=/tmp/a1_ledger.md

mkdir -p /tmp/r331b_logs
LOG=/tmp/r331b_logs/c1_supervisor_${LABEL}.log
OUTLOG=/tmp/r331b_logs/c1_$(echo "$LABEL" | cut -d- -f1).log
PIDFILE=/tmp/pf_c1_${LABEL}.pid

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
    p=$(pgrep -f "a1_v3.sh $LEANROOT" | head -1)
    if [ -n "$p" ] && kill -0 "$p" 2>/dev/null; then
      echo "$p" > "$PIDFILE"          # re-adopt and repair the pidfile
      return 0
    fi
    return 1
  else
    sc is-active --quiet pf-c1
  fi
}

start_driver () {
  if [ "$SCOPE" = "--plain" ]; then
    # No systemd. setsid detaches so the driver survives this supervisor.
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

echo "SUPERVISOR_START $(date -Is) label=$LABEL scope=$SCOPE driver=a1_v3 boxes=$BOXES cap=$MAXTRY" >> "$LOG"

tries=0
while true; do
  sleep 120
  if grep -q "C1_BOXES_DONE" "$OUTLOG" 2>/dev/null; then
    echo "SUPERVISOR: $LABEL finished cleanly $(date -Is)" >> "$LOG"; exit 0
  fi
  if grep -q "C1_ABORT" "$OUTLOG" 2>/dev/null; then
    echo "SUPERVISOR: $LABEL aborted on a real build failure - NOT restarting $(date -Is)" >> "$LOG"; exit 1
  fi
  driver_alive && continue

  tries=$((tries+1))
  echo "SUPERVISOR: driver down, resume $tries/$MAXTRY $(date -Is)" >> "$LOG"
  if [ "$tries" -gt "$MAXTRY" ]; then
    echo "SUPERVISOR: giving up after $MAXTRY resumes - needs a human $(date -Is)" >> "$LOG"; exit 1
  fi
  sleep 10
  start_driver
done
