import sys, subprocess, os
C=os.environ.get("CADICAL", os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/cadical"))
cnf, mp, lim = sys.argv[1], sys.argv[2], int(sys.argv[3])
lines=open(cnf).read().splitlines(); hdr=lines[0].split(); nv=int(hdr[2]); cls=lines[1:]
xv=[int(l.split()[0]) for l in open(mp)]
extra=[]; n=0
while n<=lim:
    with open('cnt.cnf','w') as f:
        f.write("p cnf %d %d\n"%(nv,len(cls)+len(extra))); f.write("\n".join(cls)+"\n")
        for e in extra: f.write(e+"\n")
    out=subprocess.run([C,'-q','cnt.cnf'],capture_output=True,text=True).stdout
    if 's SATISFIABLE' not in out: break
    true=set()
    for l in out.splitlines():
        if l.startswith('v '): true.update(int(a) for a in l.split()[1:] if int(a)>0)
    extra.append(" ".join(str(-v) for v in xv if v in true)+" 0"); n+=1
print("projected models:",n)
