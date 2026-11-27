# The unique largest remainder on division by smaller primes

Form a row of remainders by dividing an integer $N\ge3$ by each smaller prime in turn. Every row has a unique maximum. Its modulus is the first prime above $N/2$, with the sole exception $N=14$. For $N\ge4$ the immediately preceding remainder has the parity of $N$ except at $9$ and $21$. This proves Mike Jones's A207409 conjecture for every prime dividend. Independent mathematical review is pending. [Manuscript (PDF)](prime-remainders.pdf) · [LaTeX](prime-remainders.tex) · [A207409](https://oeis.org/A207409)

Charles R. Greathouse IV previously gave the maximum-value formula for prime dividends via Nagura's theorem. The neighboring primes around half the dividend yield the predecessor, uniqueness, and the complete exception list for arbitrary dividends. [Greathouse's argument](https://oeis.org/A039731)

`lean Remainders.lean` with Lean 4.19 checks the universal remainder inequalities given the prime gap and exhausts the dividends 3 through 21. The manuscript supplies the prime gap from Nagura's theorem. `python3 verify.py` tests every row through 1000. [Lean](Remainders.lean) · [Python](verify.py)
