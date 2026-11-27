# Source and prior-work checks for A016789

Checked November 26, 2026 (America/Chicago).

## Primary records

- **A016789**: <https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A016/A016789.seq>
  - Snapshot: `source.seq`.
  - Record header: `%I A016789 #305 Jul 11 2026 09:25:00`.
  - SHA-256: `f4da187ad7ee0be44d2ea3e383a745bda68e5b1cc0275971c24d288f37376e9d`.
- **A005351**: <https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A005/A005351.seq>
  - Snapshot: `A005351.seq`.
  - Record header: `%I A005351 M4059 #81 Jun 28 2026 15:47:49`.
  - SHA-256: `a67aee677215958696b58b5fe5a3fca0dac5e4cec733fcfd98053b0565f1e7d6`.
- **A005352**: <https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A005/A005352.seq>
  - Snapshot: `A005352.seq`.
  - Record header: `%I A005352 M2259 #66 Jun 27 2025 17:25:59`.
  - SHA-256: `b65ccfd0a2db07447ebd8774169f7299fd9ac9b36c0c0adda05466c7cc2ad3af`.

The A016789 formula credits Gilian Breysens, July 21, 2017. It remains
explicitly labeled conjectural in this exact primary snapshot. The
A005351 and A005352 name fields define the two negabinary reinterpretation
sequences. A005351 starts at index zero; A005352 starts at index one.
The formal helper extends the latter to zero, and the conjecture uses
only its original positive-index domain.

## Related material inspected

1. Jörg Arndt, *Matters Computational*, section 1.22, printed pages 58–60:
   <https://www.jjj.de/fxt/fxtbook.pdf>.
   This primary author source defines negabinary representations and gives
   conversion, increment, and decrement algorithms. It explicitly identifies
   the positive and negative sequences as A005351 and A005352. No statement
   or proof of Breysens's triple-XOR identity was located in the section.
   These standard representation algorithms are acknowledged as prior work.
2. The public compendium “Matt C Anderson contributions to OEIS March 20”:
   <https://img1.wsimg.com/blobby/go/aca8a20e-9f7c-45d0-89cc-a8d63c43f4a3/downloads/fe5d6d12-21d5-425d-89c0-72aabb65bf21/Matt%20C%20Anderson%20contributions%20to%20OEIS%20March%2020.pdf>.
   An independent agent inspected the actual nine-page document. Page 6
   repeats the identity with the label “conjectured” and its attribution;
   it provides no proof. A contradictory search snippet reading “not
   conjectured” was not supported by the actual passage.

## Bounded searches

Searches included exact combinations of `A016789`, `A005351`, `A005352`,
`Breysens`, `XOR`, `negabinary`, `proof`, and `theorem`, plus searches for
negabinary XOR expressions involving multiplication by three. Checks of
the publicly indexed trureturing, Fabian Arevalo, and Eppie proof
collections found no exact resolution. Exact-expression results included
the OEIS record and reproductions, without a proof of the target identity.

This is a bounded prior-work search. It supports reporting the assertion
as still conjectural in the checked OEIS record, with no previous proof
located by these searches. It does not establish that all mathematical
literature has been examined or certify absolute priority. The known
facts about base −2 representations are not claimed as new.

## Additional collection check

The indexed abstracts and author listing for 林拾's *Low-Hanging Fruit*
volumes I–V were checked after the initial search. Their enumerated
assertions concern A000071, A038396, A237930, A055246; A000085, A028886;
A153440, A266651, A007489, A114705, A000670, A000225; A049803, A334511,
A071307; and A334513, A198632, A121320, A113249. None is the A016789
negabinary XOR assertion. This was an abstract/target-list check, not
independent verification of those papers' proofs.

- Volume I: <https://aixiv.online/abs/2610.02669>
- Volume II: <https://aixiv.online/abs/2610.02670>
- Volume III: <https://aixiv.online/abs/2610.02785>
- Volume IV: <https://aixiv.online/abs/2611.00009>
- Volume V: <https://aixiv.online/abs/2611.00099>
