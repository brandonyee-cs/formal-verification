#!/bin/sh
# Run a Lean file inside the lean/ project, report wall time and peak RSS (sampled).
# Usage: scripts/peakrun.sh FILE.lean LOGFILE [timeout_s]   (FILE.lean relative to lean/,
# LOGFILE an absolute path). Aborts the run if the Lean process exceeds 16 GB.
cd "$(dirname "$0")/../lean"
export PATH=$HOME/.elan/bin:$PATH
T=${3:-3000}
start=$(date +%s); echo "START $(date) file=$1" > "$2.meta"
timeout $T lake env lean "$1" > "$2" 2>&1 &
peak=0
while kill -0 $! 2>/dev/null; do
  for p in $(pgrep -f "^lean $1"); do r=$(ps -o rss= -p $p 2>/dev/null); [ -n "$r" ] && [ "$r" -gt "$peak" ] && peak=$r; done
  # safety: abort if over 16 GB
  if [ "$peak" -gt 16000000 ]; then pkill -f "^lean $1"; echo "ABORTED_MEM" >> "$2"; fi
  sleep 1
done
wait $!; ec=$?
echo "EXIT=$ec wall=$(( $(date +%s) - start ))s peakRSS_kB=$peak" >> "$2.meta"
