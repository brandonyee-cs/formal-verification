# Generate a Lean file: checker library (lean/CertLib.lean.part) + chunked certificates.
# Usage: python3 scripts/gen_cert_lean.py OUT.lean CHUNK N1 N2 ...
# Needs the compiled emitter (g++ -O2 -o scripts/cert scripts/cert.cpp; override with CERT_BIN).
# The raw claim lists are written to CERT_DIR (default: certs/ at the repository root).
# Each certificate is split into chunk subtrees (checked in separate declarations, to bound
# kernel memory) joined by separator claims in a balanced skeleton.
import sys, subprocess, os
here=os.path.dirname(os.path.abspath(__file__))
out=sys.argv[1]; C=int(sys.argv[2]); Ns=[int(x) for x in sys.argv[3:]]
sys.setrecursionlimit(100000)
certbin=os.environ.get('CERT_BIN',os.path.join(here,'cert'))
certdir=os.environ.get('CERT_DIR',os.path.join(here,'..','certs'))
os.makedirs(certdir,exist_ok=True)
lib=open(os.path.join(here,'..','lean','CertLib.lean.part')).read()
parts=[lib]
B=lambda v: 'true' if v else 'false'
for N in Ns:
    tmp=os.path.join(certdir,f'cert_{N}.txt')
    subprocess.run([certbin,str(N),tmp],check=True)
    claims=[]
    for line in open(tmp):
        e=int(line); v=e&1; w=(e>>1)&1; g=(e>>2)&1023; m=e>>12
        claims.append((((m<<1)*1024+g)*2+w, v))
    claims.sort()
    # split: chunk, sep, chunk, sep, ..., chunk
    chunks=[]; seps=[]; i=0
    while True:
        chunks.append(claims[i:i+C]); i+=C
        if i>=len(claims): break
        seps.append(claims[i]); i+=1
    def tree(cl,lo,hi):
        if lo>=hi: return '.nil'
        mid=(lo+hi)//2; k,v=cl[mid]
        return f'(.node {tree(cl,lo,mid)} {k} {B(v)} {tree(cl,mid+1,hi)})'
    for j,ch in enumerate(chunks):
        parts.append(f'def c{N}_{j} : Tr :=\n  {tree(ch,0,len(ch))}\n\n')
    def skel(i,j):
        if i==j: return f'c{N}_{i}'
        mid=(i+j)//2; k,v=seps[mid]
        return f'(.node {skel(i,mid)} {k} {B(v)} {skel(mid+1,j)})'
    def proof(i,j):
        if i==j: return f'hc{N}_{i}'
        mid=(i+j)//2
        return f'(Tr.all_node_intro hs{N}_{mid} {proof(i,mid)} {proof(mid+1,j)})'
    parts.append(f'/-- Certificate for N = {N}: {len(claims)} claims, emitted by scripts/cert.cpp. -/\n'
                 f'def cert{N} : Tr :=\n  {skel(0,len(chunks)-1)}\n\n')
    for j in range(len(chunks)):
        parts.append(f'theorem hc{N}_{j} : Tr.all (checkNode {N} cert{N}) c{N}_{j} = true := by decide +kernel\n')
    for j,(k,v) in enumerate(seps):
        parts.append(f'theorem hs{N}_{j} : checkNode {N} cert{N} {k} {B(v)} = true := by decide +kernel\n')
    parts.append(f'''
theorem all{N} : Tr.all (checkNode {N} cert{N}) cert{N} = true :=
  {proof(0,len(chunks)-1)}

theorem value_Icc_{N} : value (Finset.Icc 1 {N}) = .draw :=
  value_eq_draw_of_cert {N} cert{N} all{N} (by decide +kernel) (by decide +kernel)

''')
M=max(Ns)
alts=' | '.join(f'exact value_Icc_{n}' for n in Ns)
parts.append(f'''/-- The conjecture holds for every `N ≤ {M}`. -/
theorem conj_le_{M} (N : ℕ) (hN : N ≤ {M}) (h_even : Even (N * (N + 1) / 2)) :
    value (.Icc 1 N) = .draw := by
  interval_cases N
  all_goals first
    | {alts}
    | (exfalso; revert h_even; decide)

''')
parts.append('end CatchUpCert\n')
open(out,'w').write(''.join(parts))
print('wrote',out,file=sys.stderr)
