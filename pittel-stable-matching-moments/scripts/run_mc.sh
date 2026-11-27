#!/bin/bash
# Supplementary Monte Carlo sweep (NOT exact). Usage: scripts/run_mc.sh  (from project root)
# Each line of the job list: n m samples seed ; 3 jobs in parallel. Output: logs/mc_raw.txt
set -e
B=${BIN:-/tmp/mc_bin}
gcc -O2 -o $B scripts/mc.c -lm
for c in "3 4" "4 5" "5 6" "6 7" "6 6"; do $B check $c 2000 7; done > logs/mc_check.txt
jobs=()
for seed in 1 2 3 4; do
  jobs+=("10 11 500000 $seed" "25 26 250000 $seed" "50 51 100000 $seed" "100 101 25000 $seed" "200 201 6000 $seed" "400 401 1500 $seed")
  jobs+=("25 25 50000 $seed" "50 50 25000 $seed" "100 100 5000 $seed" "200 200 1000 $seed")
  jobs+=("100 102 25000 $seed" "100 105 25000 $seed" "400 402 1500 $seed" "200 214 6000 $seed")
done
jobs+=("800 801 120 11" "800 801 120 12" "800 801 120 13" "800 801 120 14" "800 801 120 15" "800 801 120 16")
printf '%s\n' "${jobs[@]}" | xargs -P 3 -I{} sh -c "$B {} " > logs/mc_raw.txt
# second batch (run separately after a session restart killed the n=800 jobs above)
printf '%s\n' "800 801 400 21" "800 801 400 22" "800 801 400 23" "800 801 400 24" "400 401 3000 31" "400 401 3000 32" | xargs -P 3 -I{} sh -c "$B {}" > logs/mc_raw2.txt
cat logs/mc_raw.txt logs/mc_raw2.txt > logs/mc_all.txt
python3 -I scripts/pool_mc.py logs/mc_all.txt > logs/mc_summary.txt
