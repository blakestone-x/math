import Std

/-! Sharp tail prefixes of both Gray recurrences for every positive seed pair.
Indices in this file start at zero. Only Lean's standard library is imported. -/
namespace GrayUniversal

def gray (n : Nat) : Nat := n ^^^ (n/2)

theorem gray_div (n k : Nat) : gray n / 2^k = gray (n/2^k) := by
  simp only [gray, Nat.xor_div_two_pow]
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm 2 (2^k)]

private theorem gray_zero (n : Nat) (h : gray n = 0) : n = 0 := by
  have he : (n ^^^ (n/2)) ^^^ (n/2) = n := by
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  change n ^^^ (n/2) = 0 at h
  rw [h, Nat.zero_xor] at he
  omega

private theorem positive_gray (n : Nat) (h : 0<n) : 0<gray n := by
  by_cases z : gray n = 0
  · have := gray_zero n z
    omega
  · omega

def a (x y : Nat) : Nat → Nat
  | 0 => x
  | 1 => y
  | n+2 => gray (a x y n + a x y (n+1))

def b (x y : Nat) : Nat → Nat
  | 0 => x
  | 1 => y
  | n+2 => gray (b x y n) + gray (b x y (n+1))

abbrev Pair := Nat × Nat

def pair (x y n k : Nat) : Pair :=
  (a x y n / 2^k, a x y (n+1) / 2^k)

def rise (q : Pair) (c : Fin 2) := if q.1+q.2+c.val < 4 then 0 else 1

def step (q : Pair) (c : Fin 2) : Pair :=
  (q.2 / 2^(rise q c), gray (q.1+q.2+c.val) / 2^(rise q c))

private theorem realized (x y n k : Nat) :
    ∃ c : Fin 2, pair x y (n+1) (k+rise (pair x y n k) c) =
      step (pair x y n k) c := by
  let d := 2^k
  let t := a x y n
  let u := a x y (n+1)
  have hd : 0<d := Nat.two_pow_pos k
  have hc : ∃ c : Fin 2, (t+u)/d=t/d+u/d+c.val := by
    rw [Nat.add_div hd]
    split <;> rename_i hw
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  obtain ⟨c, hc⟩ := hc
  refine ⟨c, ?_⟩
  simp only [pair, step, Nat.pow_add, ← Nat.div_div_eq_div_mul, Prod.mk.injEq]
  constructor
  · trivial
  · change (gray (t+u)/d)/_ = (gray (t/d+u/d+c.val)) / _
    rw [show gray (t+u)/d = gray ((t+u)/d) from gray_div (t+u) k, hc]

private theorem scale_available (z : Nat) (hz : 2 ≤ z) :
    ∃ k, 2 ≤ z/2^k ∧ z/2^k < 4 := by
  induction z using Nat.strongRecOn with
  | ind z ih =>
    by_cases h : z<4
    · exact ⟨0, by simpa, by simpa⟩
    · obtain ⟨k, hk⟩ := ih (z/2) (by omega) (by omega)
      refine ⟨k+1, ?_⟩
      rwa [Nat.pow_succ, Nat.mul_comm (2^k) 2, ← Nat.div_div_eq_div_mul]

private def allowed : List Pair :=
  [(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)]

private theorem initial (x y : Nat) (hx : 0<x) (hy : 0<y) :
    ∃ k, pair x y 1 k ∈ allowed := by
  obtain ⟨k, hlo, hhi⟩ := scale_available (x+y) (by omega)
  have hle : y/2^k ≤ (x+y)/2^k := by
    have := Nat.zero_le (x/2^k)
    rw [Nat.add_div (Nat.two_pow_pos k)]
    split <;> omega
  have hnonneg := Nat.zero_le (y/2^k)
  refine ⟨k, ?_⟩
  change (y/2^k, gray (x+y)/2^k) ∈ allowed
  rw [gray_div]
  have hy' : y/2^k = 0 ∨ y/2^k = 1 ∨ y/2^k = 2 ∨ y/2^k = 3 := by omega
  have hsum : (x+y)/2^k = 2 ∨ (x+y)/2^k = 3 := by omega
  rcases hy' with hy'|hy'|hy'|hy' <;> rcases hsum with hs|hs <;>
    rw [hy', hs] <;> decide

private theorem four_steps : ∀ q ∈ allowed, ∀ c d e f : Fin 2,
    step (step (step (step q c) d) e) f = (1,3) := by decide

private theorem stable : ∀ c : Fin 2, rise (1,3) c=1 ∧ step (1,3) c=(1,3) := by decide

/-- At indices 5+j and 6+j (zero-based), the two scaled prefixes are 1 and 3.
Thus consecutive lengths increase by one and every term from index 6 begins with 11. -/
theorem universal_a_prefix (x y : Nat) (hx : 0<x) (hy : 0<y) :
    ∃ k, ∀ j, pair x y (5+j) (k+j) = (1,3) := by
  obtain ⟨k, hk⟩ := initial x y hx hy
  obtain ⟨c, hc⟩ := realized x y 1 k
  obtain ⟨d, hd⟩ := realized x y 2 _
  obtain ⟨e, he⟩ := realized x y 3 _
  obtain ⟨f, hf⟩ := realized x y 4 _
  have start := four_steps _ hk c d e f
  rw [← hc, ← hd, ← he, ← hf] at start
  have start_at : ∃ w, pair x y 5 w = (1,3) := ⟨_, start⟩
  obtain ⟨w, hw⟩ := start_at
  refine ⟨w, ?_⟩
  intro j
  induction j with
  | zero => exact hw
  | succ j ih =>
    obtain ⟨z, hz⟩ := realized x y (5+j) (w+j)
    rw [ih, (stable z).1, (stable z).2] at hz
    exact hz

private theorem conjugacy (x y n : Nat) : a (gray x) (gray y) n = gray (b x y n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 | 1 => rfl
    | k+2 =>
      change gray (a (gray x) (gray y) k + a (gray x) (gray y) (k+1)) = _
      rw [ih k (by omega), ih (k+1) (by omega)]
      rfl

private theorem small_inverse (n : Nat) (h : gray n=3) : n=2 := by
  have ht := gray_div n 2
  rw [h] at ht
  have hn : n/4=0 := gray_zero (n/4) (by simpa using ht.symm)
  have hs : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
  rcases hs with h0|h1|h2|h3 <;> subst n <;> first | rfl | contradiction

/-- Every term of the second recurrence from zero-based index 6 has prefix 10,
with its lower-bit width increasing by one at every step. -/
theorem universal_b_prefix (x y : Nat) (hx : 0<x) (hy : 0<y) :
    ∃ k, ∀ j, b x y (6+j)/2^(k+j)=2 := by
  obtain ⟨k,h⟩ := universal_a_prefix (gray x) (gray y)
    (positive_gray x hx) (positive_gray y hy)
  refine ⟨k, ?_⟩
  intro j
  have ht := congrArg Prod.snd (h j)
  change a (gray x) (gray y) (5+j+1) / 2^(k+j) = 3 at ht
  rw [conjugacy, gray_div] at ht
  exact small_inverse _ (by simpa only [show 5+j+1=6+j by omega] using ht)

#print axioms universal_a_prefix
#print axioms universal_b_prefix
end GrayUniversal
