#!/usr/bin/env bash
# Give Legion the Box900 panels (11.9 GiB peak needs its 20 GiB). First: is
# anything already building here? Notes say never run duplicate builds.
set -uo pipefail
export PATH="/home/xluxx/.elan/bin:$PATH"
export LC_ALL=C
LD=/home/xluxx/pf-legion-20261120/PF_Lean4_Code
B="$LD/.lake/build/lib/lean/PF"

echo "################ 1. is Legion already building?"
ps -eo pid,etimes,pcpu,rss,args --sort=-pcpu 2>/dev/null | grep -E 'lean|lake' | grep -v grep | head -6 | cut -c1-130 | sed 's/^/   /'
echo "   lean/lake procs: $(pgrep -c -f 'bin/(lean|lake)' 2>/dev/null || echo 0)"
free -g | awk '/^Mem:/{print "   mem total "$2"G avail "$7"G"}'
echo "   load: $(cut -d' ' -f1-3 /proc/loadavg)"

echo
echo "################ 2. Legion's Box900 work list"
cd "$LD" || exit 9
find PF/Analytic -path '*Box900*' -name '*.lean' | sed 's|^PF/||;s|\.lean$||' | LC_ALL=C sort -u > /tmp/b9src
find "$B/Analytic" -path '*Box900*' -name '*.olean' 2>/dev/null | sed "s|^$B/||;s|\.olean$||" | LC_ALL=C sort -u > /tmp/b9obj
comm -23 /tmp/b9src /tmp/b9obj > /tmp/b9need
printf '   Box900 sources : %s\n' "$(wc -l < /tmp/b9src)"
printf '   Box900 built   : %s\n' "$(wc -l < /tmp/b9obj)"
printf '   TO BUILD       : %s\n' "$(wc -l < /tmp/b9need)"
head -3 /tmp/b9need | sed 's/^/      /'

echo
echo "################ 3. launch, if clear"
if [ "$(pgrep -c -f 'bin/(lean|lake)' 2>/dev/null || echo 0)" -gt 0 ]; then
  echo "   SKIPPING: a lean/lake process is already running. Not starting a duplicate."
  exit 0
fi
if [ ! -s /tmp/b9need ]; then echo "   nothing to build"; exit 0; fi

sed 's|/|.|g;s|^|PF.|' /tmp/b9need > /home/xluxx/legion_b9_mods.txt
cat > /home/xluxx/legion_b9_grind.sh <<'RUNNER'
#!/usr/bin/env bash
set -uo pipefail
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1
cd /home/xluxx/pf-legion-20261120/PF_Lean4_Code || exit 9
LOG="$HOME/pflogs/legion_b9_$(date +%Y%m%d_%H%M%S).log"
mkdir -p "$HOME/pflogs"
echo "start $(date)" > "$LOG"
for m in $(cat "$HOME/legion_b9_mods.txt"); do
  AVAIL=$(free -g | awk '/^Mem:/{print $7}')
  if [ "$AVAIL" -lt 6 ]; then echo "HALT: avail ${AVAIL}G < 6G at $m" >> "$LOG"; break; fi
  echo "--- $m  (avail ${AVAIL}G)  $(date +%H:%M:%S)" >> "$LOG"
  timeout 2400 lake build "$m" >> "$LOG" 2>&1
  echo "    rc=$?" >> "$LOG"
done
echo "done $(date)" >> "$LOG"
RUNNER
chmod +x /home/xluxx/legion_b9_grind.sh
setsid nohup /home/xluxx/legion_b9_grind.sh >/dev/null 2>&1 < /dev/null &
echo "   launched Legion Box900 grind, $(wc -l < /home/xluxx/legion_b9_mods.txt) modules"
echo "   (6 GiB floor guard; Box900 panels peak ~11.9 GiB so one at a time)"
