# Independent checks

These programs were written by a separate reviewing session (a fresh Claude session asked to audit
the results; see [CHECKS.md](../CHECKS.md)), working only from the upstream Lean definitions. They
share no code with `scripts/`.

- `bf.c`: brute force from the Lean definitions. For each N it enumerates **all** complete
  profiles (no normalization) and all matchings, computes each profile's threshold, and prints the
  histogram and K(N). Feasible for N ≤ 5.

  ```bash
  gcc -O3 -o bf bf.c && ./bf 5        # K(5)=3, 120 profiles with threshold 3 (~2 s)
  ```

- `myenc.py`: a second SAT encoding of "some complete profile on N agents has no k-stable
  matching", using pairwise-order variables and no symmetry breaking. SAT ⇔ K(N) > k.

  ```bash
  python3 myenc.py 7 3 e.cnf && cadical -q e.cnf     # UNSAT as reported by the reviewer; > 20 min
  ```

- `count.py`: counts the models of a `scripts/satgen.py` CNF projected onto its preference
  variables (blocking each model in turn), to compare with the histogram from `bf.c`. It uses
  CaDiCaL from `$CADICAL` or the Lean toolchain, and writes a scratch file `cnt.cnf`.

  ```bash
  python3 ../scripts/satgen.py 5 2 c52.cnf nobreak && python3 count.py c52.cnf c52.cnf.map 1000   # 120
  ```

Outputs from rerunning them are in `logs/independent_bf.log`, `logs/independent_myenc.log` and
`logs/independent_count.log`.
