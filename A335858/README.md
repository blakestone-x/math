# Lexicographic order of binary run lengths in A335858

Blake Stone · Proof developed with OpenAI Codex

A335858 orders the nonnegative integers by binary length and then by the list of their run lengths read from right to left. Its author, Rémy Sigrist, observed that the analogous left-to-right order appears to be A180200 and gave an empirical formula for A335858 using the permutation A056539. [A335858](https://oeis.org/A335858)

**Theorem.** Let $F(n)=\mathrm{A180200}(n)$ and $R(n)=\mathrm{A056539}(n)$. In the order using run lengths read from most to least significant, the term at index $n$ is $F(n)$. In the order using run lengths read from least to most significant, it is $R(F(n))$. Both sequences have index and first term zero.

## Proof

A binary run is a maximal consecutive block of equal digits. Consider an $L$-bit positive integer, so its binary word starts with $1$. Its run lengths from left to right give a composition of $L$, that is, an ordered list of positive parts summing to $L$. The correspondence is bijective: reconstruct the word by writing the indicated lengths of alternating ones and zeros, starting with ones.

Encode a composition of $L$ by a word of $L-1$ bits, one for each gap between successive positions. Write $0$ if the gap ends a run, and $1$ if the run continues. All such encodings are possible. Their lexicographic order is the lexicographic order of the compositions. Indeed, at the first gap where two encodings differ, the earlier run lengths and the current run so far are equal. The encoding with a zero at that gap ends the current run, giving it a strictly smaller length than the other encoding. The comparison therefore agrees in both orders.

At the indices from $2^{L-1}$ through $2^L-1$, the binary forms are $1u$, with the tails $u$ running through all $(L-1)$-bit words in lexicographic order. Decode $u$ as the gap encoding just described. The output starts with $1$. Each input zero appends the opposite of the last output bit, and each input one appends a copy of that bit.

This decoding is the defining recurrence of $F$. Specifically, $F(0)=0$, $F(1)=1$, and if $m=F(t)$ for $t\ge1$, then the appended bit in $F(2t+b)$ is $1-((b+(m\bmod 2))\bmod 2)$. For $b=0$ this flips the last bit of $m$, and for $b=1$ it copies it. The remaining bits are exactly $m$. Thus $F$ lists all $L$-bit words in left-to-right run-length order for every $L\ge1$. [A180200](https://oeis.org/A180200)

The permutation $R$ reverses the bits of a positive integer, then complements all of them if the original had an even number of runs. A positive binary word starts with one, so it ends in zero exactly when its number of runs is even. The complement in that case restores a leading one. In both cases $R$ preserves length and reverses the list of run lengths. Applying it twice restores the original word. Consequently, as $F(n)$ lists the words by their left-to-right lengths, $R(F(n))$ lists them by their right-to-left lengths in the same order. Both maps fix zero separately. This proves both assertions. [A056539](https://oeis.org/A056539)

For example, at index $9=(1001)_2$ the gap code is $001$. It gives the left-to-right run lengths $(1,1,2)$ and hence the word $1011$, or $11$. Reversing the order of its runs gives $1101$, or $13$, which has $(1,1,2)$ as its lengths read from right to left.

The same argument yields a direct evaluation using a single run decoder. For a positive index with binary form $1u$, reverse the tail $u$ while preserving its width, then decode it. Reversing the gap code reverses the order of the runs, so this gives A335858 at the original index.

## Earlier evidence

The two identities above are stated as observations in the OEIS entry. Sequence Machine also lists the composition formula with 8,192 checked terms. The proof derives the identities from the definitions for every index. [A335858](https://oeis.org/A335858) · [Sequence Machine](https://sequencedb.net/index.html?p=1131&s=irregular)
