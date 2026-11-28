# Three generalized square pyramidal numbers (A000330)

For any integer index t, write P(t) = t(t+1)(2t+1)/6. Every integer z in the inclusive interval [−2048,2048] is a sum of three such values. The indices may be negative, as allowed by the conjecture. The claim for all integer targets and all polygonal orders remains open.

The certified table supplies a triple of indices for each target from 0 through 2048. The identity P(−t−1) = −P(t) gives the negative targets. For example,

    P(258003) + P(−264282) + P(108702) = 128.

The individual summands are 5,724,736,977,139,014, −6,152,888,351,367,541 and 428,151,374,228,655. The table also includes these targets identified in the Left to Solve desk notes.

| Target | First index | Second index | Third index |
|---:|---:|---:|---:|
| 977 | 831141 | −828138 | −183739 |
| 1032 | 2350841 | −2350799 | −89333 |
| 1047 | 174096 | −174008 | −20074 |
| 1167 | 2907041 | −3509705 | 2652651 |
| 1412 | 65995 | −71664 | 43196 |
| 1593 | 357768 | −360305 | 99353 |
| 2042 | 908646 | −1338895 | 1181651 |

The notes list seven further positive targets in addition to 128. The negative of each representation follows by reflecting the indices.

## Reproduction

Run `lake exe cache get` and `lake build` in this directory. The main theorem is `PyramidWitnesses.interval_witness`. The source contains the complete witness table.

To search for further witnesses, set u = x+y+1, v = x−y and Z = 2c+1. Then 6uv² = 24z + Z − Z³ − 2u³ + 2u. For each positive |u|, the search builds the roots of the necessary cubic congruence modulo |u| by lifting roots at prime powers and combining coprime factors. An integer square test reconstructs candidate indices. The fourth argument bounds the prime factors allowed in |u|. A search ending without a witness gives no conclusion beyond its search range.

    c++ -O3 -std=c++17 search.cpp -o search
    ./search 128 7000 220000 7000

[OEIS A000330](https://oeis.org/A000330) · [Left to Solve](https://lefttosolve.com/p/oeis-a000330)
