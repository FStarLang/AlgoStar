#!/usr/bin/env bash
# Launch N tmux sessions, each running copilot in autopilot mode
# to review and improve a specific chapter.
#
# Usage:
#   ./launch_improve.sh <prompt-file> [--dry-run] [ch02 ch07 ...]
#
# The prompt file contains the prompt template. Every occurrence of
# <CHAPTER> in it will be replaced with the actual chapter name (e.g. ch02).
# A copy with substitutions applied is written into each chapter directory
# as prompt_instructions.md, and copilot is directed to read that file.
# If no chapters are listed, all chapters are launched.

set -euo pipefail

WORKDIR="$(cd "$(dirname "$0")" && pwd)"

# All chapters with review.md files
ALL_CHAPTERS=(
  ch02 ch04 ch06 ch07 ch08 ch09 ch10 ch11 ch12 ch13
  ch15 ch16 ch21 ch22 ch24 ch25 ch26 ch31 ch32 ch33 ch35
)

DRY_RUN=false
PROMPT_FILE=""
CHAPTERS=()

# Parse arguments
for arg in "$@"; do
  if [[ "$arg" == "--dry-run" ]]; then
    DRY_RUN=true
  elif [[ -z "$PROMPT_FILE" && -f "$arg" ]]; then
    PROMPT_FILE="$arg"
  else
    CHAPTERS+=("$arg")
  fi
done

if [[ -z "$PROMPT_FILE" ]]; then
  echo "Usage: $0 <prompt-file> [--dry-run] [ch02 ch07 ...]" >&2
  echo "  The prompt file should contain <CHAPTER> as a placeholder." >&2
  exit 1
fi

PROMPT_TEMPLATE="$(cat "$PROMPT_FILE")"

# Default to all chapters if none specified
if [[ ${#CHAPTERS[@]} -eq 0 ]]; then
  CHAPTERS=("${ALL_CHAPTERS[@]}")
fi

DELAY_SECS=5  # stagger launches to avoid resource spikes
PROMPT_FILENAME="prompt_instructions.md"

for i in "${!CHAPTERS[@]}"; do
  ch="${CHAPTERS[$i]}"
  session_name="autoclrs_improve_${ch}"

  # Find the chapter directory (e.g., autoclrs/ch02-getting-started)
  chapter_dir=$(find "${WORKDIR}/autoclrs" -maxdepth 1 -type d -name "${ch}-*" | head -1)
  if [[ -z "$chapter_dir" ]]; then
    echo "WARNING: No directory found for ${ch} under autoclrs/, skipping." >&2
    continue
  fi

  # Write the substituted prompt into the chapter directory
  prompt_path="${chapter_dir}/${PROMPT_FILENAME}"
  echo "${PROMPT_TEMPLATE//<CHAPTER>/$ch}" > "$prompt_path"

  # Build a short instruction pointing copilot at the prompt file
  rel_prompt="${prompt_path#${WORKDIR}/}"
  short_prompt="Read the file ${rel_prompt} for your detailed prompt instructions and follow them."

  # Source .bashrc for interactive-shell setup (PATH, dotnet, etc.),
  # then add project-local FStar/bin to PATH.
  cmd="source ~/.bashrc 2>/dev/null; export PATH=\"${WORKDIR}/FStar/bin:\${PATH}\"; cd ${WORKDIR} && copilot --allow-all --alt-screen --autopilot -i \"${short_prompt}\""

  if $DRY_RUN; then
    echo "[DRY-RUN] Wrote ${prompt_path}"
    echo "[DRY-RUN] tmux new-session -d -s ${session_name} bash -ic '${cmd}'"
  else
    # Kill existing session with this name, if any
    tmux kill-session -t "${session_name}" 2>/dev/null || true

    echo "Wrote ${prompt_path}"
    echo "Launching ${session_name} for ${ch} ..."
    # Use bash -i so .bashrc's interactive guard doesn't bail out
    tmux new-session -d -s "${session_name}" "bash -ic '${cmd}'"

    # Stagger launches
    if [[ $i -lt $((${#CHAPTERS[@]} - 1)) ]]; then
      sleep "${DELAY_SECS}"
    fi
  fi
done

echo ""
echo "=== Launched ${#CHAPTERS[@]} sessions ==="
echo ""
echo "Useful commands:"
echo "  tmux ls                              # list all sessions"
echo "  tmux attach -t autoclrs_improve_01   # attach to a session"
echo "  Ctrl-b d                             # detach from a session"
echo "  tmux kill-session -t autoclrs_improve_01  # kill one session"
echo "  tmux kill-server                     # kill ALL tmux sessions"
