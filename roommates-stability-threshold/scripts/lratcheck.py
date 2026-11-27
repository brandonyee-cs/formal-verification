"""Minimal independent LRAT checker (RUP hints only; rejects RAT steps) for textual LRAT.
Usage: python3 lratcheck.py formula.cnf proof.lrat   -> prints VERIFIED iff the empty clause is derived."""
import sys

def main(cnf, prf):
    clauses = {}
    cid = 0
    with open(cnf) as f:
        for line in f:
            if line.startswith(('c', 'p')) or not line.strip(): continue
            lits = list(map(int, line.split()))
            assert lits[-1] == 0
            cid += 1; clauses[cid] = lits[:-1]
    with open(prf) as f:
        for ln, line in enumerate(f):
            t = line.split()
            if not t: continue
            if t[1] == 'd':
                for c in t[2:-1]: clauses.pop(int(c), None)
                continue
            new = int(t[0])
            z = t.index('0', 1)
            lits = list(map(int, t[1:z]))
            hints = list(map(int, t[z+1:-1]))
            assert t[-1] == '0'
            assign = set(-l for l in lits)
            ok = False
            for h in hints:
                if h < 0: raise SystemExit("RAT step not supported at line %d" % ln)
                c = clauses[h]
                unassigned = [l for l in c if l not in assign and -l not in assign]
                if any(l in assign for l in c): raise SystemExit("hint satisfied, line %d" % ln)
                if len(unassigned) == 0: ok = True; break
                if len(unassigned) != 1: raise SystemExit("hint not unit, line %d" % ln)
                assign.add(unassigned[0])
            if not ok: raise SystemExit("no conflict at line %d" % ln)
            clauses[new] = lits
            if not lits:
                print("VERIFIED: empty clause derived (id %d)" % new); return
    raise SystemExit("empty clause not derived")

main(sys.argv[1], sys.argv[2])
