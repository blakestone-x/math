import Std

/- Kernel certificates for the finite prime-power tables in periods.pdf.
   The note proves that 18 consecutive tests certify a shift: all tested
   moduli divide 18!, hence the 18 bases 0,...,17 suffice. -/
namespace ModularPeriods

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib (n+1) + fib n

def central : Nat → Nat
  | 0 => 1
  | n+1 => 2 * (2*n+1) * central n / (n+1)

def weightA (j : Nat) := fib (j+1)
def weightB (j : Nat) := fib (j+2)
def weightC (j : Nat) := central j
def weightD (j : Nat) := 2^j * central j

/-- Horner's rule for g + (X-1)P(X), using nonnegative residues. -/
def hornerStep (q g : Nat) (cs : List Nat) : List Nat :=
  let shifted := ((0 :: cs).zip (cs ++ [0])).map (fun (x,y) => (x+q-y)%q)
  match shifted with
  | [] => [g%q]
  | x :: xs => (x+g)%q :: xs

def coefficients (g : Nat → Nat) (q : Nat) : List Nat :=
  ((List.range 18).map g).foldr (hornerStep q) []

def hasShift (cs : List Nat) (q e t : Nat) : Bool :=
  let amplitudes := cs.zipIdx.map (fun (w,u) =>
    w * (u^e % q) * (u^t % q + q - 1) % q)
  (List.range 18).all (fun k =>
    (amplitudes.zipIdx.map (fun (a,u) => a * (u^k % q))).sum % q == 0)

/-- Only 2, 3 and 5 divide the candidate periods in these finite tables. -/
def certify (g : Nat → Nat) (p e t : Nat) : Bool :=
  let q := p^e
  let cs := coefficients g q
  hasShift cs q e t &&
    [2,3,5].all (fun factor => t % factor != 0 || !hasShift cs q e (t/factor))

def table (g : Nat → Nat) (p : Nat) (terms : List Nat) : Bool :=
  terms.zipIdx.all (fun (v,i) => certify g p (i+1) v)

set_option maxRecDepth 12000
set_option maxHeartbeats 20000000

theorem fibonacciA :
    table weightA 2 [1,2,2,4,8] &&
    table weightA 3 [2,6] &&
    table weightA 5 [4,20] := by decide +kernel

theorem fibonacciB :
    table weightB 2 [1,2,2,2,4] &&
    table weightB 3 [1,6] &&
    table weightB 5 [4,20] := by decide +kernel

theorem binomialC :
    table weightC 2 [1,1,1,2,2,2,4,8,16] &&
    table weightC 3 [1,6] &&
    table weightC 5 [4,20] := by decide +kernel

theorem binomialD :
    table weightD 2 [1,1,1,1,1,1,2,2,4,8,16,32,64] &&
    table weightD 3 [1,3,9,27,81,486] &&
    table weightD 5 [4,20] := by decide +kernel

end ModularPeriods
