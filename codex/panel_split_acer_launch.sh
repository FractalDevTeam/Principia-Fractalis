#!/usr/bin/env bash
# (a) Transfer the 27 Acer-only panel oleans, but ONLY where the .lean source
#     is byte-identical -- an olean built against a different source is
#     corruption, not a shortcut.
# (b) Launch Acer on the Fourier panels. Split by MEMORY not cores: Box900
#     peaks at 11.9 GiB and Acer has ~12 GiB available, so Box900 stays on
#     Legion's 20 GiB. LEAN_NUM_THREADS=1 is the OOM control, not taskset.
set -uo pipefail
export LC_ALL=C
AD="/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Lean4_Code"
LD=/home/xluxx/pf-legion-20261120/PF_Lean4_Code
OUT=/c/Users/psolo

echo "################ 1. source-hash check on the 27 transfer candidates"
: > "$OUT/xfer_ok.txt"; : > "$OUT/xfer_bad.txt"
while read -r m; do
  [ -z "$m" ] && continue
  AH=$(ssh acer "sha256sum \"$AD/PF/$m.lean\" 2>/dev/null | cut -d' ' -f1" | tr -d '\r')
  LH=$(MSYS_NO_PATHCONV=1 wsl -d Ubuntu sha256sum "$LD/PF/$m.lean" 2>/dev/null | cut -d' ' -f1 | tr -d '\r')
  if [ -n "$AH" ] && [ "$AH" = "$LH" ]; then echo "$m" >> "$OUT/xfer_ok.txt"
  else printf '   MISMATCH %-58s acer=%s legion=%s\n' "$m" "${AH:0:8}" "${LH:0:8}"; echo "$m" >> "$OUT/xfer_bad.txt"; fi
done < "$OUT/transferable.txt"
printf '   source-identical : %s\n' "$(wc -l < "$OUT/xfer_ok.txt")"
printf '   source-differs   : %s  (NOT transferred)\n' "$(wc -l < "$OUT/xfer_bad.txt")"

echo
echo "################ 2. transfer the verified oleans"
N=0
while read -r m; do
  [ -z "$m" ] && continue
  d=$(dirname "$m")
  MSYS_NO_PATHCONV=1 wsl -d Ubuntu mkdir -p "$LD/.lake/build/lib/lean/PF/$d" 2>/dev/null
  for ext in olean ilean; do
    ssh acer "cat \"$AD/.lake/build/lib/lean/PF/$m.$ext\"" 2>/dev/null \
      | MSYS_NO_PATHCONV=1 wsl -d Ubuntu tee "$LD/.lake/build/lib/lean/PF/$m.$ext" >/dev/null 2>&1 || true
  done
  N=$((N+1))
done < "$OUT/xfer_ok.txt"
echo "   transferred: $N module(s)"
echo "   legion panel oleans now: $(MSYS_NO_PATHCONV=1 wsl -d Ubuntu bash -lc 'find /home/xluxx/pf-legion-20261120/PF_Lean4_Code/.lake/build/lib/lean/PF/Analytic -name "*.olean" | wc -l' 2>/dev/null | tr -d '\r')"

echo
echo "################ 3. build Acer's work list: Fourier panels it still lacks"
ssh acer "cd \"$AD\" && find PF/Analytic/FourierPanels -name '*.lean' | sed 's|^PF/||;s|\.lean\$||'" 2>/dev/null \
  | tr -d '\r' | LC_ALL=C sort -u > "$OUT/acer_fourier_srcs.txt"
ssh acer "cd \"$AD/.lake/build/lib/lean/PF\" && find Analytic/FourierPanels -name '*.olean' | sed 's|\.olean\$||'" 2>/dev/null \
  | tr -d '\r' | LC_ALL=C sort -u > "$OUT/acer_fourier_obj.txt"
comm -23 "$OUT/acer_fourier_srcs.txt" "$OUT/acer_fourier_obj.txt" > "$OUT/acer_todo.txt"
printf '   acer fourier srcs  : %s\n' "$(wc -l < "$OUT/acer_fourier_srcs.txt")"
printf '   acer fourier built : %s\n' "$(wc -l < "$OUT/acer_fourier_obj.txt")"
printf '   ACER TO BUILD      : %s\n' "$(wc -l < "$OUT/acer_todo.txt")"

echo
echo "################ 4. write the runner onto Acer and launch it detached"
MOD=$(sed 's|/|.|g;s|^|PF.|' "$OUT/acer_todo.txt" | tr '\n' ' ')
cat > "$OUT/acer_grind.sh" <<RUNNER
#!/usr/bin/env bash
# Acer panel grind. LEAN_NUM_THREADS=1 is the OOM control. Memory guard: stop
# if available RAM drops below 4 GiB so the box stays usable.
set -uo pipefail
export PATH="\$HOME/.elan/bin:\$PATH"
export LEAN_NUM_THREADS=1
cd "$AD" || exit 9
LOG="\$HOME/acer_grind_\$(date +%Y%m%d_%H%M%S).log"
echo "start \$(date)" > "\$LOG"
for m in \$(cat "\$HOME/acer_todo_mods.txt"); do
  AVAIL=\$(free -g | awk '/^Mem:/{print \$7}')
  if [ "\$AVAIL" -lt 4 ]; then echo "HALT: avail \${AVAIL}G < 4G at \$m" >> "\$LOG"; break; fi
  echo "--- \$m  (avail \${AVAIL}G)  \$(date +%H:%M:%S)" >> "\$LOG"
  timeout 1800 lake build "\$m" >> "\$LOG" 2>&1
  echo "    rc=\$?" >> "\$LOG"
done
echo "done \$(date)" >> "\$LOG"
echo "built now: \$(find .lake/build/lib/lean/PF/Analytic/FourierPanels -name '*.olean' | wc -l)" >> "\$LOG"
RUNNER
sed 's|/|.|g;s|^|PF.|' "$OUT/acer_todo.txt" > "$OUT/acer_todo_mods.txt"
echo "   module list lines: $(wc -l < "$OUT/acer_todo_mods.txt")"
scp -q "$OUT/acer_grind.sh" "$OUT/acer_todo_mods.txt" acer:~/ && echo "   runner + list copied to Acer"
ssh acer 'chmod +x ~/acer_grind.sh && setsid nohup ~/acer_grind.sh >/dev/null 2>&1 < /dev/null & echo "   launched, pid $!"'
sleep 8
ssh acer 'echo "   log: $(ls -t ~/acer_grind_*.log 2>/dev/null | head -1)"; tail -4 $(ls -t ~/acer_grind_*.log 2>/dev/null | head -1) 2>/dev/null | sed "s/^/      /"'
