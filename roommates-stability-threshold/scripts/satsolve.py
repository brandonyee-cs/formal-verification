"""Generate CNF, run CaDiCaL (bundled with the Lean toolchain), decode + independently re-verify any model.
Usage: python3 satsolve.py N k [timeout_s]"""
import sys, os, subprocess, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import satgen, kstable

CADICAL = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/cadical")
N, k = int(sys.argv[1]), int(sys.argv[2])
to = int(sys.argv[3]) if len(sys.argv) > 3 else 3600
here = os.path.dirname(os.path.abspath(__file__))
cnf = os.path.join(here, "..", "logs", "nostable_N%d_k%d.cnf" % (N, k))
nv, cls, x = satgen.build(N, k)
with open(cnf, "w") as f:
    f.write("p cnf %d %d\n" % (nv, len(cls)))
    for c in cls: f.write(" ".join(map(str, c)) + " 0\n")
t = time.time()
r = subprocess.run([CADICAL, "-q", "-t", str(to), cnf], capture_output=True, text=True)
dt = time.time() - t
lines = r.stdout.splitlines()
status = [l for l in lines if l.startswith("s ")]
print("N=%d k=%d vars=%d clauses=%d status=%s time=%.1fs" % (N, k, nv, len(cls), status, dt))
if status and status[0] == "s SATISFIABLE":
    true = set()
    for l in lines:
        if l.startswith("v "):
            true.update(int(a) for a in l.split()[1:] if int(a) > 0)
    prefs = [[None]*(N-1) for _ in range(N)]
    for (i, j, rr), v in x.items():
        if v in true: prefs[i][rr-1] = j
    print("PROFILE", prefs)
    R = kstable.ranks(prefs)
    print("independent check: k-stable matching exists?", kstable.kstable_matching(R, k),
          " threshold =", kstable.threshold(R))
os.remove(cnf)
