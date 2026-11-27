"""Emit a Lean benchmark file: CNF + first K LRAT addition steps (deletions dropped) as list literals.
Literal encoding: 2*var + (1 if negative)."""
import sys
cnf, prf, K, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
enc = lambda l: 2*abs(l) + (1 if l < 0 else 0)
cls = [list(map(int, l.split()))[:-1] for l in open(cnf) if not l.startswith(('p','c'))]
steps = []
for line in open(prf):
    t = line.split()
    if t[1] == 'd': continue
    z = t.index('0', 1)
    steps.append((int(t[0]), [enc(int(a)) for a in t[1:z]], [int(a) for a in t[z+1:-1]]))
    if len(steps) >= K: break
L = lambda xs: "[" + ",".join(map(str, xs)) + "]"
with open(out, "w") as f:
    f.write("import Mathlib.Data.List.Basic\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LratBench\n\n")
    f.write(open(sys.argv[5]).read())
    f.write("\ndef cnf : List (List Nat) := [" + ",\n ".join(L([enc(a) for a in c]) for c in cls) + "]\n\n")
    f.write("def steps : List (Nat × List Nat × List Nat) := [" + ",\n ".join("(%d,%s,%s)" % (i, L(c), L(h)) for i, c, h in steps) + "]\n\n")
    f.write("set_option maxRecDepth 100000 in\ntheorem bench : checkAll cnf steps = true := by decide +kernel\n\nend LratBench\n")
print("steps", len(steps), "hints", sum(len(h) for _,_,h in steps))
