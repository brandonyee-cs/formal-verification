"""Format exact moments: E[S], E[S^2], ratio E[S^2]/E[S]^2 as reduced fractions + decimals,
and Pittel's Thm 1.3 first-moment asymptotic for comparison. Usage: python3 -I exact_table.py raw"""
import sys, math
from fractions import Fraction as F
print('n m d | E[S] | E[S^2] | ratio=E[S^2]/E[S]^2 | decimals (E, E2, ratio) | Pittel asymptotic E (Thm 1.3)')
for line in open(sys.argv[1]):
    n, m, a, b, d = map(int, line.split())
    e1, e2 = F(a, d), F(b, d)
    r = e2 / e1 ** 2
    if m > n:
        s = math.log(m / (m - n))
        pred = n * math.exp(-(math.exp(s) - 1 - s) / (math.exp(s) - 1)) / ((m - n) * s)
    else:
        pred = math.exp(-1) * n * math.log(n) if n > 1 else float('nan')
    print(f'{n} {m} {m-n} | {e1} | {e2} | {r} | {float(e1):.6f} {float(e2):.6f} {float(r):.6f} | {pred:.4f}')
