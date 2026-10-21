#!/bin/bash
# Peak-RSS sampler for the march. Additive and read-only: it samples `ps` and
# appends one line per completed Lean module, so it can be started and stopped
# at any time without touching the running march_box.sh (editing that file
# mid-invocation can corrupt bash's incremental read of it).
#
# WHY. Per-module peak RSS is not logged anywhere. The march_box.sh progress
# lines record `free` AFTER each module exits, which is flat at 8-9 GB of 15
# across every box so far -- that shows there is no leak, but says nothing
# about the peak, and the peak is what OOMs. A live sample during box c = 35/4
# showed 10.4 GB, against the 7.6 GB recorded for c = 27/4. If per-module peak
# grows with c, the march could OOM before c = 13, and the dense bands keep
# module SIZE fixed at 8 panels so the trend is purely in c.
#
# Output: /tmp/rss_peaks.log   "<module> <peakRSS_GB> <seconds> <finished>"
set -u
OUT=/tmp/rss_peaks.log
touch "$OUT"
cur=""
peak=0
t0=0
while true; do
  line=$(ps -eo rss,args --sort=-rss 2>/dev/null \
         | grep -E "^ *[0-9]+ lean -o " | head -1)
  if [ -n "$line" ]; then
    rss=$(echo "$line" | awk '{print $1}')
    mod=$(echo "$line" | grep -oE "[A-Za-z0-9_]+\.lean" | tail -1)
    if [ "$mod" != "$cur" ]; then
      if [ -n "$cur" ] && [ "$peak" -gt 0 ]; then
        printf "%s %.2f %s %s\n" "$cur" \
          "$(echo "$peak" | awk '{printf "%.2f", $1/1048576}')" \
          "$(( $(date +%s) - t0 ))" "$(date +%H:%M:%S)" >> "$OUT"
      fi
      cur="$mod"; peak=0; t0=$(date +%s)
    fi
    [ "$rss" -gt "$peak" ] && peak=$rss
  elif [ -n "$cur" ]; then
    if [ "$peak" -gt 0 ]; then
      printf "%s %.2f %s %s\n" "$cur" \
        "$(echo "$peak" | awk '{printf "%.2f", $1/1048576}')" \
        "$(( $(date +%s) - t0 ))" "$(date +%H:%M:%S)" >> "$OUT"
    fi
    cur=""; peak=0
  fi
  sleep 10
done
