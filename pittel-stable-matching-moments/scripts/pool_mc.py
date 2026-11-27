"""Pool Monte Carlo chunks (same n, m) from mc output lines; print mean, E[S^2], ratio with
delta-method standard error, and the spread of per-chunk ratios. Usage: python3 -I pool_mc.py file"""
import sys, math
from collections import defaultdict
acc = defaultdict(lambda: [0, 0.0, 0.0, 0.0, 0.0, []])
for line in open(sys.argv[1]):
    t = line.split()
    if 'sums' not in t:
        continue
    n, m, T = int(t[0]), int(t[1]), int(t[2])
    s = list(map(float, t[t.index('sums') + 1:]))
    a = acc[(n, m)]
    a[0] += T
    for k in range(4):
        a[k + 1] += s[k]
    a[5].append(float(t[5]))
print('n m d samples E[S] E[S^2] ratio se(ratio) chunk_ratios  [pred E[S] (Pittel Thm 1.3)]')
for (n, m), a in sorted(acc.items(), key=lambda x: (x[0][1] - x[0][0], x[0][0])):
    T = a[0]
    e1, e2, e3, e4 = (x / T for x in a[1:5])
    r = e2 / e1 ** 2
    va, vb, cab = e2 - e1 ** 2, e4 - e2 ** 2, e3 - e1 * e2
    ga, gb = -2 * e2 / e1 ** 3, 1 / e1 ** 2
    se = math.sqrt(max(0, (ga * ga * va + gb * gb * vb + 2 * ga * gb * cab) / T))
    if m > n:
        sv = math.log(m / (m - n))
        pred = n * math.exp(-(math.exp(sv) - 1 - sv) / (math.exp(sv) - 1)) / ((m - n) * sv)
    else:
        pred = math.exp(-1) * n * math.log(n)
    print(n, m, m - n, T, '%.4f %.3f %.4f %.4f' % (e1, e2, r, se), ' '.join('%.3f' % x for x in a[5]), ' [%.3f]' % pred)
