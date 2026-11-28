# A288668: sources, scope, and prior-proof checks

Checked November 27, 2026 (America/Chicago). These checks document the
retrieved sources and search scope; they do not establish exhaustive
historical priority.

## Exact target

Clark Kimberling's entries A288665 and A288668, both introduced June 15,
2017, conjecture the same connection: the successive lengths of the
left-to-right, nonoverlapping replacement `00 -> 0110`, `10 -> 000`,
starting from `00`, are A288668.

The coherent A288668 reference is fixed by its data, generating function,
and Mathematica command:

```text
LinearRecurrence[{0, 1, 2}, {2, 4, 5}, 40]
```

Thus L(0)=2, L(1)=4, L(2)=5 and L(n+3)=L(n+1)+2L(n).
The proof derives this recurrence from the actual lists and scan.
It proves the stronger literal equality w(n+3)=w(n)w(n)w(n+1).
The contribution count is one assertion, shared by two entries.

## Preserved primary exports

The snapshots were read from the official `oeis/oeisdata` repository.
Their complete bytes were checked against the Git blob hashes below.

| File | Revision | Git blob SHA |
|---|---|---|
| [A288665.seq](sources/A288665.seq) | 21, July 27, 2024 | `cb425d3b56b238dc4b4cc4816c9f3a9f09ad5947` |
| [A288668.seq](sources/A288668.seq) | 6, April 7, 2020 | `ac859c6bd1f2248370eeb20b11c3939df104a584` |
| [A288670.seq](sources/A288670.seq) | 10, April 6, 2020 | `437113ca436953b1a13cf91897ec083bdcdf772c` |
| [A288673.seq](sources/A288673.seq) | 9, April 6, 2020 | `a211a83316b2b19e18808c90c7ff4f04e029bd1c` |
| [A288468.seq](sources/A288468.seq) | 8, June 15, 2017 | `00d05bd92ffa63af983755a4fc74a53004cb561f` |

Primary entry and export URLs:

- https://oeis.org/A288665
- https://oeis.org/A288668
- https://github.com/oeis/oeisdata/blob/main/seq/A288/A288665.seq
- https://github.com/oeis/oeisdata/blob/main/seq/A288/A288668.seq
- https://oeis.org/A288670
- https://oeis.org/A288673
- https://oeis.org/A288468

Indexed public entry pages and internal pages were also inspected. Direct
fetches of some OEIS pages returned 403 responses; the official repository
exports supplied the complete maintained records.

## Source ambiguities resolved explicitly

1. **A288668 initial-index labels.** Its title and repeated formula say
   a(0)=2, a(2)=4, a(3)=5. The displayed data start 2,4,5,8 at offset zero,
   the Mathematica program uses the initial list {2,4,5}, and the given
   generating function is (2+4x+3x²)/(1-x²-2x³). All three independently
   specify initial indices 0,1,2. The literal first words also have lengths
   2,4,5. The formal reference uses these coherent bases and labels the
   prose index error in its definition.
2. **A288670 and A288673 length links.** These companions use the same
   replacement but name A288468 as the length sequence. A288468 instead
   counts positions of ones in the different rule `00 -> 0101`,
   `1 -> 010`, and begins 2,4,6,9,... at offset one. The correct length
   reference is A288668, as recorded in A288665. These are cross-reference
   errors, not additional independent conjectures solved or refuted.
3. **Other companion links.** A288665's preserved cross-reference line
   contains A299670/A299673 where its same-rule companion entries are
   A288670/A288673. This bibliographic issue does not enter any theorem.

The README does not claim to prove the inconsistent initial labels
literally. It proves the conjectured replacement-to-sequence connection
with the exact indexing fixed by the actual data and executable source.

## Prior mathematics and repository overlap

The source entries have no paper link for a proof of the length
connection. The finite-state and substitution methods used in the proof
are standard; no general new substitution theorem is claimed.

The latest repository README was read at commit
`a2a6825a315f3c1b2d54dacf81960eb6ce4faa50`, whose README blob was
`790a2ba76c76163d17d24d76453829301d0a6a31`. It contains no A288668 or
A288665 package. The related `Kimberling-pair-rules` package was read:
it treats `00 -> 001` with one of two single-letter rules, and concerns
A285665, A285666, A285667, A286058, A285432, and A285564. Its assertions
are different and are not counted again.

## Resolution searches

Both web search engines were used, including these exact and semantic
queries:

- `"A288668" proof`;
- `"A288665" recurrence proof`;
- `"A288670" proof`;
- `"00" "0110" "10" "000" "Kimberling"`.

Results located the primary OEIS entries and sequence mirrors. Sequence
Machine records the numerical recurrence and equivalent generating
function for A288668; that is not a proof of the replacement connection.
No earlier proof of this exact connection was located.

The live https://www.trureturing.org/conjectures index was searched for
A288665, A288668, A288670, and A288468; none appeared in the retrieved
index text. The checked *Low-Hanging Fruit* I-V target enumerations
concern other entries, as recorded in the preceding repository batch.
No claim is made about unpublished work or about every possible source.

A further semantic search located trureturing's
[Kimberling replacement-iterate length result](https://www.trureturing.org/research/oeis-a288476-replacement-iterate-length/).
Its full statement and proof outline were read. It treats A288476, with
the repeated assertion in A288473 and A288551: the rule is
`00 -> 0101`, `1 -> 011`, and the length recurrence is
L(n+3)=L(n+2)+4L(n+1)-2L(n), with initial values 2,4,8.
That record explicitly leaves other replacement rules outside its scope.
It is relevant prior use of the standard boundary-safe recoding method,
but it does not settle the distinct A288668 rule or its recurrence.

The supported conclusion is a complete proof and formal verification
of the particular conjectural connection after these bounded checks.
The correction of clerical labels, weighted consequences, and three
prefix-limit consequences do not increase the assertion count.

OEIS snapshots are reproduced with attribution to their contributors
and the OEIS Foundation. See
https://oeis.org/wiki/The_OEIS_End-User_License_Agreement .
