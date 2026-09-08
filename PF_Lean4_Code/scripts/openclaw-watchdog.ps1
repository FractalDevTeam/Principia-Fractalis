# OpenClaw gateway + GPU-Ollama watchdog
#
# Why this exists (2026-09-07):
#   The Legion rebooted. The gateway came back, but it is NOT a system service -
#   it runs inside a `systemd --user` session in the OpenClawGateway distro, so
#   nothing supervises it. Separately, GPU Ollama on 127.0.0.1:11435 had been
#   DOWN SINCE AUG 30 - eight days - and nobody noticed, because it is a
#   *fallback*. Its failure was silent: the gateway's morning-brief and
#   earnings check-in crons simply logged "All models failed" and moved on,
#   accumulating 10x and 11x consecutive errors against a dead port.
#
#   A fallback that fails silently is worse than no fallback. This probes both
#   and repairs both.
#
# Exit codes: 0 all healthy or repaired, 1 a repair was attempted and failed.

$ErrorActionPreference = 'SilentlyContinue'
$log = Join-Path $PSScriptRoot 'watchdog.log'

function Say($m) {
  $line = "{0}  {1}" -f (Get-Date -Format 'yyyy-MM-ddTHH:mm:ss'), $m
  Add-Content -Path $log -Value $line
}

function Test-Port([int]$port) {
  $c = New-Object Net.Sockets.TcpClient
  try   { $c.Connect('127.0.0.1', $port); return $c.Connected }
  catch { return $false }
  finally { $c.Close() }
}

$rc = 0

# ---- 1. gateway on 18789 -----------------------------------------------
if (Test-Port 18789) {
  # healthy: stay quiet, so the log records only events
} else {
  Say 'GATEWAY DOWN on 18789 - starting scheduled task "OpenClaw Gateway"'
  Start-ScheduledTask -TaskName 'OpenClaw Gateway'
  Start-Sleep -Seconds 25
  if (Test-Port 18789) { Say 'GATEWAY RECOVERED' }
  else { Say 'GATEWAY STILL DOWN after relaunch - NEEDS A HUMAN'; $rc = 1 }
}

# ---- 2. GPU Ollama on 11435 (the fallback that died silently) ----------
if (Test-Port 11435) {
  # healthy
} else {
  Say 'GPU OLLAMA DOWN on 11435 - running ollama-gpu/ensure.sh in Ubuntu'
  # ensure.sh blocks until the socket is bound. That wait is load-bearing: a
  # transient wsl.exe session kills the not-yet-established child on teardown,
  # which is the defect that left 11435 dead from 2026-08-30 to 09-07.
  Start-Process -FilePath wsl.exe `
    -ArgumentList '-d','Ubuntu','--','bash','/home/xluxx/ollama-gpu/ensure.sh' `
    -NoNewWindow -Wait
  if (Test-Port 11435) { Say 'GPU OLLAMA RECOVERED' }
  else { Say 'GPU OLLAMA STILL DOWN after start.sh - NEEDS A HUMAN'; $rc = 1 }
}

exit $rc
