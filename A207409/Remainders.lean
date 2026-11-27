import Std

namespace PrimeRemainders

theorem once {n p : Nat} (hp : p ≤ n) (h : n < 2 * p) : n % p = n - p := by
  rw [Nat.mod_eq_sub_mod hp, Nat.mod_eq_of_lt (show n - p < p by omega)]

theorem twice {n p : Nat} (hp : 2 * p ≤ n) (h : n < 3 * p) : n % p = n - 2 * p := by
  have step : p ≤ n := by omega
  rw [Nat.mod_eq_sub_mod step, once (show p ≤ n-p by omega) (show n-p < 2*p by omega)]
  omega

theorem small {n p : Nat} (hp : 0 < p) (h : 2*p ≤ n) : 3*(n%p) ≤ n := by
  by_cases hs : 3*p ≤ n
  · have := Nat.mod_lt n hp
    omega
  · rw [twice h (by omega)]
    omega

/-- Only the prime gap across n/2 is needed. Every other modulus is small or above q. -/
theorem winner {n p q : Nat} (hp : 0 < p) (hle : p ≤ n) (hql : q ≤ n)
    (half : n < 2*q) (bound : 3*q < 2*n) (other : 2*p ≤ n ∨ q < p) :
    n % p < n % q := by
  rw [once hql half]
  rcases other with h | h
  · have := small hp h
    omega
  · rw [once hle (by omega)]
    omega

def primesBelow (n : Nat) : List Nat :=
  (List.range n).filter fun p =>
    2 ≤ p && ((List.range p).drop 2).all (fun d => p % d != 0)

def smallRow (n : Nat) : Bool := Id.run do
  let ps := primesBelow n
  let high := (ps.map (n % ·)).foldl max 0
  let winners := ps.filter (fun p => n % p == high)
  let w := winners.head!
  let expected := if n == 14 then some 5 else ps.find? (fun p => n < 2*p)
  let parity := match (ps.takeWhile (· < w)).getLast? with
    | none => n == 3
    | some r => ((n % r) % 2 == n % 2) == (n != 9 && n != 21)
  return winners.length == 1 && some w == expected && parity

theorem finiteTable : ((List.range 22).drop 3).all smallRow = true := by decide

end PrimeRemainders
