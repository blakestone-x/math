import Blocks

namespace Kimberling288511
open Letter

def phase : ℕ → Phase
  | 0 => 0
  | n+1 => next (phase n)

def core : ℕ → List Letter
  | 0 => [A,C,C,B,B,C,B,B,C,A,A]
  | n+1 => left (phase n) ++ sigma (core n) ++ extra (phase n)

def trailing : ℕ → ℕ
  | 0 => 5
  | n+1 => trailing n + gain (phase n)

/-- Exact equality of finite binary words, not just their lengths. -/
theorem word_shape (n : ℕ) :
    word (n+9) = shape (phase n) (core n) (trailing n) := by
  induction n with
  | zero => simp [word, rewrite, shape, phase, core, trailing, front,
      suffix, tail, encode, block, ones]
  | succ n ih =>
    rw [show n+1+9 = (n+9)+1 by omega, word, ih, rewrite_shape]
    rfl

def count (a : Letter) : List Letter → ℤ
  | [] => 0
  | b :: v => (if a = b then 1 else 0) + count a v

@[simp] lemma count_append (a : Letter) (u v : List Letter) :
    count a (u ++ v) = count a u + count a v := by
  induction u with
  | nil => simp [count]
  | cons b u ih => simp [count, ih, add_assoc]

lemma sigma_counts (v : List Letter) :
    count A (sigma v) = 2 * count C v ∧
    count B (sigma v) = count A v + count C v ∧
    count C (sigma v) = count B v := by
  induction v with
  | nil => simp [count, sigma]
  | cons a v ih =>
    simp only [sigma] at ih
    cases a <;> simp [sigma, subst, count, ih.1, ih.2.1, ih.2.2] <;> omega

lemma encode_length (v : List Letter) :
    ((encode v).length : ℤ) = 2 * count A v + 3 * count B v + 4 * count C v := by
  induction v with
  | nil => simp [encode, count]
  | cons a v ih =>
    cases a <;> simp [encode, block, count] at * <;> omega

@[simp] lemma ones_length (t : ℕ) : (ones t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [ones, ih]

structure State where
  p : Phase
  a : ℤ
  b : ℤ
  c : ℤ
  t : ℤ
  deriving DecidableEq

def advance (s : State) : State :=
  ⟨next s.p,
    2*s.c + count A (left s.p) + count A (extra s.p),
    s.a + s.c + count B (left s.p) + count B (extra s.p),
    s.b + count C (left s.p) + count C (extra s.p),
    s.t + gain s.p⟩

def observe (s : State) : ℤ :=
  2*s.a + 3*s.b + 4*s.c + s.t + 1 + (front s.p).length + (encode (tail s.p)).length

def pack (p : Phase) (v : List Letter) (t : ℕ) : State :=
  ⟨p, count A v, count B v, count C v, t⟩

lemma shape_length (p : Phase) (v : List Letter) (t : ℕ) :
    ((shape p v t).length : ℤ) = observe (pack p v t) := by
  simp [shape, suffix, observe, pack, encode_length]
  ring

lemma pack_advance (p : Phase) (v : List Letter) (t : ℕ) :
    pack (next p) (left p ++ sigma v ++ extra p) (t + gain p) =
      advance (pack p v t) := by
  obtain ⟨ha,hb,hc⟩ := sigma_counts v
  simp [pack, advance, ha, hb, hc, add_comm, add_left_comm, add_assoc]

def future : ℕ → State → State
  | 0, s => s
  | n+1, s => advance (future n s)

lemma future_add (m n : ℕ) (s : State) :
    future (m+n) s = future n (future m s) := by
  induction n with
  | zero => simp [future]
  | succ n ih => simp [future, ih, Nat.add_succ]

def seed : State := pack 0 [A,C,C,B,B,C,B,B,C,A,A] 5

lemma packed_future (n : ℕ) :
    pack (phase n) (core n) (trailing n) = future n seed := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change pack (next (phase n)) (left (phase n) ++ sigma (core n) ++ extra (phase n))
      (trailing n + gain (phase n)) = advance (future n seed)
    rw [pack_advance, ih]

def lengthValue (n : ℕ) : ℤ := ((word n).length : ℤ)

theorem literal_numeric_bridge (n : ℕ) :
    lengthValue (n+9) = observe (future n seed) := by
  rw [lengthValue, word_shape, shape_length, packed_future]

end Kimberling288511
