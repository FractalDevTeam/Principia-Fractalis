#!/usr/bin/env bash
# pf_dispatch_fix.sh — bring a Claude Code dispatch node back online.
#
# Diagnosed on the .94 Linux server 2026-09-10 after the 2026-09-05 OAuth
# revocation cascade. Applies the five fixes that were jamming dispatch:
#   1. install uv/uvx (needed by the Serena MCP plugin)
#   2. symlink lowercase and capital-P Principia-Fractalis paths to the
#      canonical working tree on this host
#   3. fix the pablo MCP path in ~/.claude/settings.json
#   4. remove the broken xluxx-trust MCP entry from ~/.claude.json
#   5. kill any orphaned dispatch daemon (leaving a clean slate for the
#      next `claude` invocation to spawn a fresh one)
#
# Does NOT touch OAuth — that still requires a browser at a human via
# `claude auth login` (device-code flow), a hard limit of the auth protocol.
#
# Safe to re-run: every mutation is idempotent, and .json edits back up
# the file with a timestamped .bak before writing.

set -euo pipefail

log() { printf '[pf-fix] %s\n' "$*"; }
warn() { printf '[pf-fix][WARN] %s\n' "$*" >&2; }

if [ "$(id -u)" -eq 0 ]; then
  warn "running as root; will chown edits to \$SUDO_USER (${SUDO_USER:-xluxx}) at the end"
fi

TARGET_USER="${SUDO_USER:-$USER}"
HOME_DIR="$(getent passwd "$TARGET_USER" | cut -d: -f6)"
[ -d "$HOME_DIR" ] || { warn "no home dir for $TARGET_USER"; exit 2; }

# --- 1. Ensure uv/uvx are on PATH ------------------------------------------
log "step 1: uv/uvx"
if command -v uv >/dev/null && command -v uvx >/dev/null; then
  log "  already present: $(command -v uv) ($(uv --version 2>&1))"
else
  # Install system-wide so dispatch subprocesses find it regardless of shell rc.
  if [ "$(id -u)" -eq 0 ]; then
    curl -LsSf https://astral.sh/uv/install.sh | env INSTALLER_NO_MODIFY_PATH=1 UV_INSTALL_DIR=/usr/local/bin sh
  else
    curl -LsSf https://astral.sh/uv/install.sh | sh
    log "  installed to \$HOME/.local/bin — ensure that's on dispatch daemon's PATH"
  fi
fi

# --- 2. Symlink Principia-Fractalis paths ---------------------------------
log "step 2: PF path symlinks"
# Locate the canonical working tree. Try common locations in order.
CANDIDATES=(
  "/Storage 2TB/home/$TARGET_USER/Principia-Fractalis-ACTIVE"
  "/mnt/d/Principia-Fractalis-ACTIVE"
  "/mnt/c/Users/$TARGET_USER/Principia-Fractalis-ACTIVE"
  "$HOME_DIR/.openclaw/workspace/Principia-Fractalis"
  "$HOME_DIR/pablo_context/Principia_Fractalis_CLEAN_DELIVERABLE_2025-11-11"
)
CANONICAL=""
for c in "${CANDIDATES[@]}"; do
  if [ -d "$c" ]; then CANONICAL="$c"; break; fi
done
if [ -z "$CANONICAL" ]; then
  warn "  no canonical PF tree found in known locations; skipping symlinks"
else
  log "  canonical: $CANONICAL"
  for name in Principia-Fractalis principia-fractalis; do
    dest="$HOME_DIR/$name"
    if [ -L "$dest" ] || [ ! -e "$dest" ]; then
      ln -sfn "$CANONICAL" "$dest"
      log "  symlinked $dest -> $CANONICAL"
    else
      log "  $dest exists as non-symlink; leaving alone"
    fi
  done
fi

# --- 3. Fix pablo MCP path in settings.json --------------------------------
log "step 3: pablo MCP path"
SETTINGS="$HOME_DIR/.claude/settings.json"
if [ -f "$SETTINGS" ]; then
  cp -a "$SETTINGS" "${SETTINGS}.bak.$(date +%Y%m%d-%H%M%S)"
  python3 - "$SETTINGS" <<'PY'
import json, sys
p = sys.argv[1]
c = json.load(open(p))
mcp = c.get("mcpServers", {}) or {}
changed = False
if "pablo" in mcp:
    args = mcp["pablo"].get("args", []) or []
    fixed = [a.replace("/pablo-mcp/", "/pablo-mcp-server/") for a in args]
    if fixed != args:
        mcp["pablo"]["args"] = fixed
        changed = True
        print("  updated pablo MCP args to:", fixed)
if changed:
    json.dump(c, open(p, "w"), indent=2)
else:
    print("  no change needed")
PY
else
  log "  no ~/.claude/settings.json — skipping"
fi

# --- 4. Remove broken xluxx-trust MCP from .claude.json -------------------
log "step 4: prune broken xluxx-trust MCP"
CLAUDEJSON="$HOME_DIR/.claude.json"
if [ -f "$CLAUDEJSON" ]; then
  cp -a "$CLAUDEJSON" "${CLAUDEJSON}.bak.$(date +%Y%m%d-%H%M%S)"
  python3 - "$CLAUDEJSON" <<'PY'
import json, sys, os
p = sys.argv[1]
c = json.load(open(p))
mcp = c.get("mcpServers", {}) or {}
removed = []
xt = mcp.get("xluxx-trust")
if xt:
    args = xt.get("args", []) or []
    path = args[0] if args else ""
    if path and not os.path.exists(path):
        del mcp["xluxx-trust"]
        removed.append(("xluxx-trust", path))
    else:
        print(f"  xluxx-trust points at {path} which exists; leaving alone")
if removed:
    print("  removed:", removed)
    json.dump(c, open(p, "w"), indent=2)
else:
    print("  no change needed")
PY
else
  log "  no ~/.claude.json — skipping"
fi

# --- 5. Kill orphaned dispatch daemon -------------------------------------
log "step 5: orphaned dispatch daemons"
# Match server binaries under ~/.claude/remote/srv/*/server --serve
mapfile -t PIDS < <(pgrep -af 'remote/srv/.*/server --serve' | awk '{print $1}')
if [ ${#PIDS[@]} -eq 0 ]; then
  log "  none running"
else
  for pid in "${PIDS[@]}"; do
    log "  killing PID $pid"
    kill "$pid" 2>/dev/null || true
  done
  sleep 1
  # SIGKILL any survivors
  for pid in "${PIDS[@]}"; do
    if kill -0 "$pid" 2>/dev/null; then
      log "  SIGKILL PID $pid"
      kill -9 "$pid" 2>/dev/null || true
    fi
  done
fi

# --- 6. Ownership sweep ---------------------------------------------------
if [ "$(id -u)" -eq 0 ]; then
  log "step 6: chown edits back to $TARGET_USER"
  for f in "$SETTINGS" "$CLAUDEJSON" "$HOME_DIR/Principia-Fractalis" "$HOME_DIR/principia-fractalis"; do
    [ -e "$f" ] && chown -h "$TARGET_USER":"$TARGET_USER" "$f" 2>/dev/null || true
  done
fi

log "done. Next step for the user (protocol-level, cannot be automated):"
log "  \`claude auth login --claudeai\`  # completes OAuth device-code flow in a browser"
log "  then \`claude\` will spawn a fresh dispatch daemon with valid credentials."
