import Std

/-! # Fixed-width reverse subtraction (OEIS A338203)

A bit word stores its two outer digits and the word between them. The first
outer digit is the least significant. `subtractReverse` implements subtraction
of the reversed word, including an incoming borrow and the outgoing borrow.
The full word map `step` starts with borrow zero and discards the last borrow.
-/

namespace ReverseSubtract

inductive Word : Nat → Type where
  | empty : Word 0
  | center (bit : Bool) : Word 1
  | pair {n : Nat} (low : Bool) (inner : Word n) (high : Bool) : Word (n + 2)

def Word.low {n} : Word (n + 2) → Bool
  | .pair x _ _ => x

def Word.inner {n} : Word (n + 2) → Word n
  | .pair _ w _ => w

def Word.high {n} : Word (n + 2) → Bool
  | .pair _ _ y => y

def Palindrome {n} : Word n → Prop
  | .empty => True
  | .center _ => True
  | .pair x w y => x = y ∧ Palindrome w

/-- The output bit and the outgoing borrow in one digit of binary subtraction. -/
def outBit (x y a : Bool) : Bool := (x ^^ y) ^^ a
def borrow (x y a : Bool) : Bool := if x = y then a else y

def subtractReverse {n} : Word n → Bool → Word n × Bool
  | .empty, a => (.empty, a)
  | .center _, a => (.center a, a)
  | .pair x w y, a =>
    let (v, b) := subtractReverse w (borrow x y a)
    (.pair (outBit x y a) v (outBit y x b), borrow y x b)

def step {n} (w : Word n) := (subtractReverse w false).1

def solid (bit : Bool) : (n : Nat) → Word n
  | 0 => .empty
  | 1 => .center bit
  | n + 2 => .pair bit (solid bit n) bit

private theorem pal_pair {n} (w : Word (n + 2)) :
    Palindrome w ↔ w.low = w.high ∧ Palindrome w.inner := by cases w <;> rfl

private theorem low_sub {n} (w : Word (n + 2)) (a : Bool) :
    (subtractReverse w a).1.low = outBit w.low w.high a := by cases w <;> rfl
private theorem inner_sub {n} (w : Word (n + 2)) (a : Bool) :
    (subtractReverse w a).1.inner = (subtractReverse w.inner (borrow w.low w.high a)).1 := by
  cases w <;> rfl
private theorem high_sub {n} (w : Word (n + 2)) (a : Bool) :
    (subtractReverse w a).1.high = outBit w.high w.low
        (subtractReverse w.inner (borrow w.low w.high a)).2 := by cases w <;> rfl
private theorem borrow_sub {n} (w : Word (n + 2)) (a : Bool) :
    (subtractReverse w a).2 = borrow w.high w.low
        (subtractReverse w.inner (borrow w.low w.high a)).2 := by cases w <;> rfl

private theorem monotone_on_cycle (f : Nat → Bool) (p : Nat) (hp : 0 < p)
    (period : ∀ t, f (t + p) = f t)
    (absorbs : ∀ t, f t = false → f (t+1) = false) :
    (∀ t, f t = false) ∨ (∀ t, f t = true) := by
  have persists (t k : Nat) (h : f t = false) : f (t+k) = false := by
    induction k with
    | zero => exact h
    | succ k ih => exact absorbs (t+k) ih
  have adjacent (t : Nat) : f (t+1) = f t := by
    cases h : f t with
    | false => exact absorbs t h
    | true =>
      cases hnext : f (t+1) with
      | true => rfl
      | false =>
        have hbad := persists (t+1) (p-1) hnext
        rw [show t+1+(p-1) = t+p by omega, period, h] at hbad
        contradiction
  have constant (t : Nat) : f t = f 0 := by
    induction t with
    | zero => rfl
    | succ t ih => exact (adjacent t).trans ih
  cases initial : f 0 with
  | false => exact Or.inl (fun t => (constant t).trans initial)
  | true => exact Or.inr (fun t => (constant t).trans initial)

/-- Boundary-borrow theorem for a periodic inner block. Its two boundary
borrows agree at each time. Either the block is always palindromic or its
boundary borrow alternates at every step. The incoming borrow may vary. -/
theorem periodic_boundaries (n p : Nat) (hp : 0 < p) (w : Nat → Word n) (a : Nat → Bool)
    (period : ∀ t, w (t+p) = w t)
    (next : ∀ t, w (t+1) = (subtractReverse (w t) (a t)).1) :
    (∀ t, (subtractReverse (w t) (a t)).2 = a t) ∧
    ((∀ t, Palindrome (w t)) ∨ (∀ t, a (t+1) = !(a t))) := by
  induction n using Nat.strongRecOn generalizing a with
  | ind n ih =>
    cases n with
    | zero => exact ⟨fun t => by cases (w t) <;> rfl,
                    Or.inl (fun t => by cases (w t) <;> trivial)⟩
    | succ m =>
      cases m with
      | zero => exact ⟨fun t => by cases (w t) <;> rfl,
                      Or.inl (fun t => by cases (w t) <;> trivial)⟩
      | succ m =>
        let x := fun t => (w t).low
        let y := fun t => (w t).high
        let v := fun t => (w t).inner
        let c := fun t => borrow (x t) (y t) (a t)
        let b := fun t => (subtractReverse (v t) (c t)).2
        have vi (t) : v (t+p) = v t := congrArg Word.inner (period t)
        have vn (t) : v (t+1) = (subtractReverse (v t) (c t)).1 :=
          (congrArg Word.inner (next t)).trans (inner_sub (w t) (a t))
        obtain ⟨bc, inside⟩ := ih m (by omega) v c vi vn
        have crossing (t) : b t = c t := bc t
        have xl (t) : x (t+1) = outBit (x t) (y t) (a t) :=
          (congrArg Word.low (next t)).trans (low_sub (w t) (a t))
        have yh (t) : y (t+1) = outBit (y t) (x t) (c t) :=
          ((congrArg Word.high (next t)).trans (high_sub (w t) (a t))).trans
            (congrArg (outBit (y t) (x t)) (crossing t))
        have whole (t) : (subtractReverse (w t) (a t)).2 = borrow (y t) (x t) (c t) :=
          (borrow_sub (w t) (a t)).trans (congrArg (borrow (y t) (x t)) (crossing t))
        let s := fun t => x t ^^ y t
        have sp (t) : s (t+p) = s t := congrArg (fun q => q.low ^^ q.high) (period t)
        have absorbs (t) (h : s t = false) : s (t+1) = false := by
          change (x (t+1) ^^ y (t+1)) = false
          rw [xl, yh]
          change ((outBit (x t) (y t) (a t)) ^^ (outBit (y t) (x t) (borrow (x t) (y t) (a t)))) = false
          change (x t ^^ y t) = false at h
          revert h
          generalize x t = xx; generalize y t = yy; generalize a t = aa
          cases xx <;> cases yy <;> cases aa <;> decide
        rcases monotone_on_cycle s p hp sp absorbs with same | different
        · have eqbits (t) : x t = y t := by
            have h : (x t ^^ y t) = false := same t
            revert h
            generalize x t = xx; generalize y t = yy
            cases xx <;> cases yy <;> decide
          have ca (t) : c t = a t := by simp [c, borrow, eqbits t]
          refine ⟨fun t => by rw [whole, ca, eqbits, borrow]; simp, ?_⟩
          rcases inside with h | h
          · exact Or.inl (fun t => (pal_pair (w t)).2 ⟨eqbits t, h t⟩)
          · exact Or.inr (fun t => (ca (t+1)).symm.trans ((h t).trans (congrArg Bool.not (ca t))))
        · have pair_data (t : Nat) : a t = !(y t) ∧ y (t+1) = !(y t) ∧
                borrow (y t) (x t) (c t) = a t := by
            have h : (x t ^^ y t) = true := different t
            have hn : (x (t+1) ^^ y (t+1)) = true := different (t+1)
            rw [xl, yh] at hn
            rw [yh]
            dsimp only [c] at hn ⊢
            revert h hn
            generalize x t = xx; generalize y t = yy; generalize a t = aa
            cases xx <;> cases yy <;> cases aa <;> decide
          refine ⟨fun t => (whole t).trans (pair_data t).2.2, Or.inr ?_⟩
          intro t
          rw [(pair_data (t+1)).1, (pair_data t).2.1, (pair_data t).1]

private theorem pal_sub {n} (w : Word n) (a : Bool) (h : Palindrome w) :
    subtractReverse w a = (solid a n, a) := by
  induction w generalizing a with
  | empty => rfl
  | center => rfl
  | pair x w y ih =>
    obtain ⟨rfl, hinner⟩ := h
    simp [subtractReverse, borrow, outBit, solid, ih a hinner]

/-- Every periodic orbit of the concrete fixed-width subtraction map consists
entirely of the all-zero word. This holds at every width and period. -/
theorem zero_is_only_cycle {n p : Nat} (hp : 0 < p) (w : Nat → Word n)
    (period : ∀ t, w (t+p) = w t) (next : ∀ t, w (t+1) = step (w t)) :
    ∀ t, w t = solid false n := by
  obtain ⟨_, h | alt⟩ := periodic_boundaries n p hp w (fun _ => false) period next
  · intro t
    have pred : t + p = (t + (p-1)) + 1 := by omega
    rw [← period t, pred, next]
    exact congrArg Prod.fst (pal_sub (w (t+(p-1))) false (h _))
  · have bad := alt 0
    contradiction

private def words : (n : Nat) → List (Word n)
  | 0 => [.empty]
  | 1 => [.center false, .center true]
  | n + 2 => (words n).flatMap (fun w =>
      [.pair false w false, .pair false w true, .pair true w false, .pair true w true])

private theorem mem_words {n} (w : Word n) : w ∈ words n := by
  induction w with
  | empty => simp [words]
  | center b => cases b <;> simp [words]
  | pair x w y ih =>
    apply List.mem_flatMap.mpr
    exact ⟨w, ih, by cases x <;> cases y <;> simp⟩

private theorem repeat_in_list {α : Type} (l : List α) (f : Nat → α)
    (covered : ∀ t, f t ∈ l) : ∃ i j, i < j ∧ f i = f j := by
  induction l generalizing f with
  | nil => have h := covered 0; simp at h
  | cons x xs ih =>
    by_cases appears : ∃ i, f i = x
    · obtain ⟨i, hi⟩ := appears
      by_cases again : ∃ j, i < j ∧ f j = x
      · obtain ⟨j, ij, hj⟩ := again
        exact ⟨i, j, ij, hi.trans hj.symm⟩
      · let tail := fun t => f (i+1+t)
        have tailmem (t) : tail t ∈ xs := by
          cases List.mem_cons.mp (covered (i+1+t)) with
          | inl h => exact False.elim (again ⟨i+1+t, by omega, h⟩)
          | inr h => exact h
        obtain ⟨j,k,jk,h⟩ := ih tail tailmem
        exact ⟨i+1+j,i+1+k,by omega,h⟩
    · apply ih f
      intro t
      exact (List.mem_cons.mp (covered t)).resolve_left (fun h => appears ⟨t,h⟩)

/-- Iterating the concrete word map from an arbitrary starting word. -/
def orbit {n} (w : Word n) : Nat → Word n
  | 0 => w
  | k + 1 => step (orbit w k)

/-- Every fixed-width word reaches zero after finitely many iterations. -/
theorem every_orbit_hits_zero {n} (w : Word n) : ∃ t, orbit w t = solid false n := by
  obtain ⟨i,j,ij,eq⟩ := repeat_in_list (words n) (orbit w) (fun t => mem_words (orbit w t))
  have shift (t) : orbit w (i+t) = orbit w (j+t) := by
    induction t with
    | zero => exact eq
    | succ t ih => exact congrArg step ih
  let tail := fun t => orbit w (i+t)
  have per (t) : tail (t+(j-i)) = tail t := by
    change orbit w (i+(t+(j-i))) = orbit w (i+t)
    rw [show i+(t+(j-i)) = j+t by omega]
    exact (shift t).symm
  have nxt (t) : tail (t+1) = step (tail t) := rfl
  exact ⟨i, zero_is_only_cycle (p := j-i) (by omega) tail per nxt 0⟩

/-- Evaluate a word in binary place value, including leading zeros. -/
def Word.value {n} : Word n → Nat
  | .empty => 0
  | .center b => b.toNat
  | @Word.pair m x w y => x.toNat + 2*w.value + 2^(m+1)*y.toNat

def Word.reverse {n} : Word n → Word n
  | .empty => .empty
  | .center b => .center b
  | .pair x w y => .pair y w.reverse x

theorem Word.value_lt {n} (w : Word n) : w.value < 2^n := by
  induction w with
  | empty => decide
  | center b => cases b <;> decide
  | @pair m x w y ih =>
    cases x <;> cases y <;> simp [Word.value, Nat.pow_succ] <;> omega

/-- Every integer in the n-bit range has a word of that exact width. -/
theorem word_of_lt (n k : Nat) (bound : k < 2^n) : ∃ w : Word n, w.value = k := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    cases n with
    | zero => exact ⟨.empty, by simp at bound; simpa [Word.value] using bound.symm⟩
    | succ m =>
      cases m with
      | zero =>
        have hk : k = 0 ∨ k = 1 := by simp at bound; omega
        rcases hk with rfl | rfl <;> first | exact ⟨.center false, rfl⟩ | exact ⟨.center true, rfl⟩
      | succ m =>
        have fill (u : Nat) (hu : u < 2^(m+1)) (y : Bool) :
            ∃ w : Word (m+2), w.value = u + 2^(m+1)*y.toNat := by
          obtain ⟨v,hv⟩ := ih m (by omega) (u/2) ((Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr
            (by simpa [Nat.pow_succ] using hu))
          have r : u%2 = 0 ∨ u%2 = 1 := by omega
          rcases r with r | r
          · exact ⟨.pair false v y, by simp [Word.value,hv]; omega⟩
          · exact ⟨.pair true v y, by simp [Word.value,hv]; omega⟩
        by_cases h : k < 2^(m+1)
        · simpa using fill k h false
        · have h' : k-2^(m+1) < 2^(m+1) := by
            rw [show 2^(m+1+1) = 2^(m+1)*2 by simp [Nat.pow_succ]] at bound
            omega
          obtain ⟨w,hw⟩ := fill (k-2^(m+1)) h' true
          exact ⟨w, by simp at hw; omega⟩

private theorem digit_balance (x y a : Bool) :
    (outBit x y a).toNat + y.toNat + a.toNat = x.toNat + 2*(borrow x y a).toNat := by
  cases x <;> cases y <;> cases a <;> decide

/-- Place-value identity for subtraction, including both boundary borrows. -/
theorem subtraction_balance {n} (w : Word n) (a : Bool) :
    (subtractReverse w a).1.value + w.reverse.value + a.toNat =
      w.value + 2^n * (subtractReverse w a).2.toNat := by
  induction w generalizing a with
  | empty => simp [Word.value, Word.reverse, subtractReverse]
  | center b => cases a <;> cases b <;> decide
  | @pair m x w y ih =>
    let b := (subtractReverse w (borrow x y a)).2
    have low := digit_balance x y a
    have middle := ih (borrow x y a)
    have upper := congrArg (fun z : Nat => 2^(m+1)*z) (digit_balance y x b)
    change (outBit x y a).toNat + 2*(subtractReverse w (borrow x y a)).1.value +
      2^(m+1)*(outBit y x b).toNat + (y.toNat + 2*w.reverse.value + 2^(m+1)*x.toNat) + a.toNat =
      x.toNat + 2*w.value + 2^(m+1)*y.toNat + 2^(m+2)*(borrow y x b).toNat
    change (subtractReverse w (borrow x y a)).1.value + w.reverse.value + (borrow x y a).toNat =
      w.value + 2^m * b.toNat at middle
    dsimp only at upper
    simp only [Nat.mul_add, ← Nat.mul_assoc] at upper
    rw [show 2^(m+2) = 2^(m+1)*2 by simp [Nat.pow_succ]]
    have carry := congrArg (fun z : Nat => 2*z) middle
    simp only [Nat.mul_add, ← Nat.mul_assoc] at carry
    have bb : 2*2^m = 2^(m+1) := by simp [Nat.pow_succ, Nat.mul_comm]
    rw [bb] at carry
    omega

/-- The unsigned value of a step is subtraction of the n-bit reversal modulo 2^n.
The extra copy of the modulus on the right makes natural subtraction exact. -/
theorem step_mod {n} (w : Word n) :
    (step w).value = (2^n + w.value - w.reverse.value) % 2^n := by
  have bal := subtraction_balance w false
  have bound := (step w).value_lt
  change (step w).value + w.reverse.value + 0 = w.value + 2^n * (subtractReverse w false).2.toNat at bal
  cases b : (subtractReverse w false).2 <;> simp [b] at bal
  · rw [show 2^n + w.value - w.reverse.value = (step w).value + 2^n by omega]
    simp [Nat.mod_eq_of_lt bound]
  · rw [show 2^n + w.value - w.reverse.value = (step w).value by omega]
    exact (Nat.mod_eq_of_lt bound).symm

/-- Forget the unique central bit of an odd-width word. -/
def deleteCenter : (m : Nat) → Word (2*m+1) → Word (2*m)
  | 0, .center _ => .empty
  | m+1, .pair x w y => .pair x (deleteCenter m w) y

theorem delete_sub (m : Nat) (w : Word (2*m+1)) (a : Bool) :
    (deleteCenter m (subtractReverse w a).1, (subtractReverse w a).2) =
      subtractReverse (deleteCenter m w) a := by
  induction m generalizing a with
  | zero => cases w <;> rfl
  | succ m ih =>
    cases w with
    | pair x v y =>
      have h := ih v (borrow x y a)
      cases hs : subtractReverse v (borrow x y a) with
      | mk z b =>
        rw [hs] at h
        simp only at h
        simp [deleteCenter, subtractReverse, hs, ← h]

theorem delete_pal (m : Nat) (w : Word (2*m+1)) :
    Palindrome (deleteCenter m w) ↔ Palindrome w := by
  induction m with
  | zero => cases w <;> rfl
  | succ m ih => cases w with | pair x v y => simp [deleteCenter, Palindrome, ih]

theorem delete_orbit (m : Nat) (w : Word (2*m+1)) (t : Nat) :
    deleteCenter m (orbit w t) = orbit (deleteCenter m w) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    exact (congrArg Prod.fst (delete_sub m (orbit w t) false)).trans (congrArg step ih)

/-- Odd-width central deletion preserves exactly which times are palindrome
hits, including time zero. In particular, it preserves the first hit. -/
theorem palindrome_times_delete (m : Nat) (w : Word (2*m+1)) (t : Nat) :
    Palindrome (orbit (deleteCenter m w) t) ↔ Palindrome (orbit w t) := by
  rw [← delete_orbit]
  exact delete_pal m (orbit w t)

theorem solid_palindrome (b : Bool) : ∀ n, Palindrome (solid b n)
  | 0 => trivial
  | 1 => trivial
  | n+2 => ⟨rfl, solid_palindrome b n⟩

/-- The OEIS termination statement with its palindrome stopping condition. -/
theorem every_word_reaches_palindrome {n} (w : Word n) : ∃ t, Palindrome (orbit w t) := by
  obtain ⟨t,h⟩ := every_orbit_hits_zero w
  exact ⟨t, h ▸ solid_palindrome false n⟩

#print axioms every_word_reaches_palindrome
#print axioms word_of_lt
#print axioms palindrome_times_delete
#print axioms step_mod
#print axioms every_orbit_hits_zero
#print axioms periodic_boundaries
#print axioms zero_is_only_cycle

end ReverseSubtract
