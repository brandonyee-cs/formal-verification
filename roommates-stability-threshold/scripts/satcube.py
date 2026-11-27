"""Cube-and-conquer for 'profile with no k-stable matching' (SAT <=> K(N) > k):
split on agent 1's preference list ((N-1)! cubes), run CaDiCaL per cube in parallel.
Usage: python3 satcube.py N k jobs [first_cube last_cube]"""
import sys, os, subprocess, itertools, tempfile, time
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import satgen

CADICAL = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/cadical")
N, k, jobs = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
nv, cls, x = satgen.build(N, k)
base = "p cnf %d %d\n" % (nv, len(cls) + N - 1) + "".join(" ".join(map(str, c)) + " 0\n" for c in cls)
others = [j for j in range(N) if j != 1]
cubes = list(itertools.permutations(others))
lo = int(sys.argv[4]) if len(sys.argv) > 4 else 0
hi = int(sys.argv[5]) if len(sys.argv) > 5 else len(cubes)
tmpd = tempfile.mkdtemp(prefix="cube", dir=os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "logs"))

def solve(ci):
    order = cubes[ci]
    fn = os.path.join(tmpd, "c%d.cnf" % ci)
    with open(fn, "w") as f:
        f.write(base)
        for r, j in enumerate(order): f.write("%d 0\n" % x[1, j, r + 1])
    r = subprocess.run([CADICAL, "-q", fn], capture_output=True, text=True)
    os.remove(fn)
    st = [l for l in r.stdout.splitlines() if l.startswith("s ")][0]
    return ci, st

t0 = time.time(); sat = []; done = 0
with ThreadPoolExecutor(jobs) as ex:
    for ci, st in ex.map(solve, range(lo, hi)):
        done += 1
        if st != "s UNSATISFIABLE":
            sat.append(ci); print("CUBE", ci, cubes[ci], st, flush=True)
        if done % 100 == 0: print("done", done, "elapsed %.0fs" % (time.time() - t0), flush=True)
os.rmdir(tmpd)
print("N=%d k=%d cubes %d..%d : %d non-UNSAT cubes %s, time %.0fs" % (N, k, lo, hi, len(sat), sat, time.time() - t0))
