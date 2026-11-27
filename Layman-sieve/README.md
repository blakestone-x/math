# Triangular stabilization of Layman's sieve

For any nonempty deletion mask with infinite complement, the first $k$ entries of the iterated $L$-sieve equal $1,3,6,\ldots,k(k+1)/2$ at every iteration $t\ge 2k-1$. This proves Layman's 2008 convergence conjecture for every admissible input. It also gives uniqueness of the triangular fixed point and excludes other periodic orbits.

[Manuscript (PDF)](sieve.pdf) · [LaTeX source](sieve.tex) · [Lean stabilization and jumps](Proof.lean) · [Lean residue arithmetic](Residues.lean)

| Question | Result |
| --- | --- |
| [A152009](https://oeis.org/A152009) | Coordinatewise convergence with a uniform time bound, and the proposed recurrence for the residue class $1\bmod 3$. |
| [A214972](https://oeis.org/A214972) | Equals the counting function of A152009, so the conjectured jump set is exact. |
| [A006999](https://oeis.org/A006999) and [A061419](https://oeis.org/A061419) | The other two residue classes modulo three give the proposed sieve identifications. A006999 includes an initial zero. |
| [A155167](https://oeis.org/A155167) | The recurrence recorded from initial terms holds for every term. |
| [A279075](https://oeis.org/A279075) through [A279080](https://oeis.org/A279080) | The shared question about stopping-time maxima has an affirmative answer for every modulus $d\ge2$. The positive tail gives the sieve output. |

The proof derives a rank recurrence from literal list deletion. A correct triangular prefix persists after one transform. The next output can only overshoot the next triangular number, and a second transform fixes it. The general one-residue formula follows by numbering the surviving positions within a single block.

## Verification

Lean 4.19.0 with its standard library checks preservation of valid ranks, the uniform stabilization theorem, the A214972 threshold and jump identities, the survivor-index formula in block coordinates, and the inverse endpoint for stopping times. The manuscript derives the rank model from the list operation and identifies each OEIS sequence. The Python verifier separately applies the literal deletion rule.

```sh
lake build
python3 verify.py
sha256sum -c SHA256SUMS
```

[Build and check output](verification.txt). The problem statements were checked against the [OEIS source snapshot](https://github.com/oeis/oeisdata/tree/976b0c73e00453b1c1e6f16d83108cb9bb744c3b/seq). The theorem gives $2k-1$ as a sufficient bound.
