#!/bin/bash
# ensure.sh — start GPU Ollama on 11435 and DO NOT RETURN until it is listening.
#
# Why the wait matters (2026-09-07): start.sh backgrounds `ollama serve` with
# setsid. When it is invoked through a transient `wsl.exe -d Ubuntu -- ...`
# session, that session tears down as soon as the command returns, and the
# not-yet-established child dies with it. serve.log is never even truncated,
# so the failure leaves no trace. That is why the Startup .vbs has been failing
# silently since 2026-08-30 while appearing to run.
#
# Holding this script open until the socket is bound keeps the session alive
# through the vulnerable window.
#
# exit 0 = listening, exit 1 = did not come up.

if ss -ltn 2>/dev/null | grep -q '127.0.0.1:11435'; then
  echo "ensure: already listening"
  exit 0
fi

bash /home/xluxx/ollama-gpu/start.sh

for i in $(seq 1 40); do
  if ss -ltn 2>/dev/null | grep -q '127.0.0.1:11435'; then
    echo "ensure: 11435 up after ~${i}s"
    sleep 3          # let it finish settling before we release the session
    exit 0
  fi
  sleep 1
done

echo "ensure: FAILED - 11435 not listening after 40s"
tail -5 /home/xluxx/ollama-gpu/serve.log 2>/dev/null
exit 1
