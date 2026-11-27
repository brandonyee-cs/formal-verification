#!/bin/bash
# Exact moments of S for all reachable (n, m). Usage (from project root): scripts/run_exact.sh
# Set FULL=1 to include the slow balanced case (5,5).
# Writes logs/exact_raw.txt (n m N1 N2 D) and logs/exact_moments.txt (fractions, ratio).
set -e
B=${BIN:-/tmp/moments_bin}
gcc -O2 -o $B scripts/moments.c
: > logs/exact_raw.txt
for nm in "1 1" "1 2" "1 3" "2 2" "2 3" "2 4" "2 5" "2 6" "2 7" "2 8" "3 3" "3 4" "3 5" "3 6" "3 7" "4 4" "4 5" "4 6" ${FULL:+"5 5"}; do
  $B ${nm} >> logs/exact_raw.txt
done
python3 -I scripts/exact_table.py logs/exact_raw.txt > logs/exact_moments.txt
