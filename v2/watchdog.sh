#!/bin/sh
# Hard Proof v2: memory watchdog. Logs free memory. Below 15 percent free it stops the heavy jobs of the lab.
LOG="$HOME/Projects/hp-work/guard/mem.log"
mkdir -p "$(dirname "$LOG")"
while true; do
  F=$(memory_pressure 2>/dev/null | awk -F': ' '/free percentage/ {gsub("%","",$2); print $2}')
  echo "$(date '+%H:%M:%S') free=${F}% claude=$(pgrep -f 'claude .*stream-json' | wc -l | tr -d ' ') node=$(pgrep -x node | wc -l | tr -d ' ') lean=$(pgrep -f 'lake|lean' | wc -l | tr -d ' ')" >> "$LOG"
  # A `codegraph explore` process with parent 1 has no reader: its caller timed out and ended.
  # Puppetmaster 1.51.0 leaves one for each worker start, and each can grow past 2 GB.
  for P in $(pgrep -f "codegraph.js explore"); do
    if [ "$(ps -o ppid= -p "$P" | tr -d ' ')" = "1" ]; then kill "$P" 2>/dev/null && echo "$(date '+%H:%M:%S') killed orphan codegraph explore $P" >> "$LOG"; fi
  done
  if [ -n "$F" ] && [ "$F" -lt 15 ]; then
    echo "$(date '+%H:%M:%S') EMERGENCY free=${F}%: stopping lab drivers, test runs and Lean kernels" >> "$LOG"
    pkill -f "fix.py run"; pkill -f "retro.py run"; pkill -f "build_flow.py"
    pkill -f "venv/bin/python -m pytest"; pkill -x con-leche; pkill -x con-ron; pkill -x nanoda_bin
    pkill -f leanchecker; pkill -x lean4lean; pkill -x lean; pkill -x lake
  fi
  sleep 20
done
