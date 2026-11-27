import Std

namespace PeriodicSymmetric

def productN : List Nat → Nat
  | [] => 1
  | a :: t => a * productN t

theorem product_append (s t : List Nat) : productN (s ++ t) = productN s * productN t := by
  induction s with
  | nil => simp [productN]
  | cons a s ih => simp [productN, ih, Nat.mul_assoc]

/-- Sum of the products obtained by omitting one indexed entry.
Omitting the head contributes the full product of the tail. -/
def oneOmitted : List Nat → Nat
  | [] => 0
  | a :: t => (productN t) + a * oneOmitted t

theorem omit_append (s t : List Nat) :
    oneOmitted (s ++ t) = oneOmitted s * (productN t) + (productN s) * oneOmitted t := by
  induction s with
  | nil => simp [oneOmitted, productN]
  | cons a s ih =>
    simp only [List.cons_append, oneOmitted, productN, product_append, ih,
      Nat.mul_add, Nat.add_mul]
    ac_rfl

/-- Any prefix followed by two copies of a block satisfies the recurrence.
A cyclic shift of a period has the same product. -/
theorem two_blocks (prefixList block : List Nat) :
    oneOmitted ((prefixList ++ block) ++ block) + (productN block) ^ 2 * oneOmitted prefixList =
      2 * (productN block) * oneOmitted (prefixList ++ block) := by
  rw [show 2 * productN block = productN block + productN block by omega]
  simp only [omit_append, product_append, Nat.pow_succ, Nat.pow_zero,
    Nat.one_mul, Nat.mul_one, Nat.add_mul, Nat.mul_add]
  ac_rfl

def periodicPrefix (block : List Nat) (n : Nat) : List Nat :=
  (List.range n).map fun i => block[i % block.length]!

/-- Coefficients of x through x^(2d) in (1-P*x^d)^2 times the series. -/
def numerator (block : List Nat) : List Int :=
  let d := block.length
  let p : Int := (productN block)
  let a := fun n => (oneOmitted (periodicPrefix block n) : Int)
  (List.range (2*d)).map fun i =>
    let n := i+1
    a n - (if d ≤ n then 2*p*a (n-d) else 0) +
      (if 2*d ≤ n then p^2*a (n-2*d) else 0)

theorem table :
    ([ [4,1,2,3], [3,4,1,2], [1,2,3,4,5], [2,2,1],
       [1,3], [3,1], [2,3], [3,2], [1,1,1,2], [1,1,1,3] ].map numerator) =
    [ [1,5,14,50,176,80,64,0], [1,7,19,50,126,432,144,0],
      [1,3,11,50,274,154,188,324,576,0], [1,4,8,12,16,0],
      [1,4,1,0], [1,4,9,0], [1,5,4,0], [1,5,9,0],
      [1,2,3,7,5,3,1,0], [1,2,3,10,7,4,1,0] ] := by decide +kernel

#print axioms two_blocks
#print axioms table

end PeriodicSymmetric
