' OpenClaw local-model support: keeps Ubuntu WSL alive and runs GPU Ollama on 127.0.0.1:11435.
'
' FIXED 2026-09-07. The previous line was:
'
'     sh.Run "wsl.exe -d Ubuntu -- bash -lc ""bash .../start.sh""", 0, False
'
' start.sh backgrounds `ollama serve` with setsid. Because bWaitOnReturn was False,
' the wsl.exe session tore down immediately and killed the not-yet-established
' child. serve.log was never even truncated, so the failure left NO TRACE - the
' script appeared to run fine. GPU Ollama was consequently DOWN FROM 2026-08-30
' TO 2026-09-07, and the OpenClaw gateway's morning-brief and earnings check-in
' crons silently accumulated 10x and 11x "All models failed" errors against a
' dead port for eight days.
'
' The fix: ensure.sh does not return until 127.0.0.1:11435 is listening, so the
' session stays alive through the vulnerable window; and bWaitOnReturn is True so
' we actually wait for it.
Set sh = CreateObject("WScript.Shell")
sh.Run "wsl.exe -d Ubuntu -- sleep infinity", 0, False
WScript.Sleep 8000
sh.Run "wsl.exe -d Ubuntu -- bash /home/xluxx/ollama-gpu/ensure.sh", 0, True
