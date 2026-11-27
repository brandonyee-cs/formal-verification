#!/bin/sh
# Exhaustive N=6: k=2 (expect counterexamples) and k=3 (expect none), 120 shards on agent 1's list, 4 parallel.
cd "$(dirname "$0")" && gcc -O3 -o search search.c
for k in 2 3; do
  seq 0 119 | xargs -P 4 -I{} ./search 6 $k 0 {} 120 | grep '^N=' > ../logs/n6_k$k.shards
  awk -v k=$k '{split($5,a,"=");split($4,b,"=");s+=a[2];l+=b[2]} END{print "N=6 k=" k " leaves=" l " no_k_stable_profiles=" s}' ../logs/n6_k$k.shards | tee ../logs/n6_k$k.summary
done
