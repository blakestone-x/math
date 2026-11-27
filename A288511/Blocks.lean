import Mathlib.Tactic

/-! The literal nonoverlapping replacement in OEIS A288508/A288512. -/
namespace Kimberling288511

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, true, false, true] ++ rewrite w
  | true :: false :: w => [false, false, true] ++ rewrite w
  | false :: true :: w => false :: rewrite (true :: w)
  | true :: true :: w => true :: rewrite (true :: w)
termination_by w => w.length

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

inductive Letter | A | B | C deriving DecidableEq, Repr
open Letter

def block : Letter → List Bool
  | A => [true, false]
  | B => [true, false, false]
  | C => [true, false, false, false]

def image : Letter → List Bool
  | A => [false, false, true]
  | B => [false, false, true, false]
  | C => [false, false, true, false, true, false, true]

def subst : Letter → List Letter
  | A => [B]
  | B => [C]
  | C => [A, A, B]

def encode (v : List Letter) : List Bool := v.flatMap block
def sigma (v : List Letter) : List Letter := v.flatMap subst
def images (v : List Letter) : List Bool := v.flatMap image

@[simp] lemma encode_append (u v : List Letter) :
    encode (u ++ v) = encode u ++ encode v := by simp [encode]
@[simp] lemma sigma_append (u v : List Letter) :
    sigma (u ++ v) = sigma u ++ sigma v := by simp [sigma]

lemma rewrite_block (a : Letter) (v : List Letter) (u : List Bool) :
    rewrite (block a ++ encode v ++ true :: u) =
      image a ++ rewrite (encode v ++ true :: u) := by
  cases v with
  | nil => cases a <;> simp [encode, block, image, rewrite]
  | cons b v => cases a <;> cases b <;> simp [encode, block, image, rewrite]

lemma rewrite_encode (v : List Letter) (u : List Bool) :
    rewrite (encode v ++ true :: u) = images v ++ rewrite (true :: u) := by
  induction v with
  | nil => simp [encode, images]
  | cons a v ih =>
    simpa [encode, images, List.append_assoc] using
      (rewrite_block a v u).trans (congrArg (fun w => image a ++ w) ih)

/-- The two-zero conjugacy responsible for the interior cubic recurrence. -/
theorem rotation (v : List Letter) :
    images v ++ [false, false] = [false, false] ++ encode (sigma v) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [images, List.flatMap_cons, List.append_assoc] at *
    rw [ih]
    cases a <;> simp [sigma, subst, image, encode, block, List.append_assoc]

def ones : ℕ → List Bool
  | 0 => []
  | n+1 => true :: ones n

@[simp] lemma ones_add (m n : ℕ) : ones (m+n) = ones m ++ ones n := by
  induction m with
  | zero => simp [ones]
  | succ m ih => simpa [ones, Nat.succ_add] using congrArg (List.cons true) ih

@[simp] lemma rewrite_ones (n : ℕ) : rewrite (ones n) = ones n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [ones, rewrite]
  | one => simp [ones, rewrite]
  | more n ih ih' => simpa [ones, rewrite] using congrArg (List.cons true) ih'

@[simp] lemma rewrite_cons_ones (n : ℕ) :
    rewrite (true :: ones n) = true :: ones n := rewrite_ones (n+1)

@[simp] lemma ones_append_one (n : ℕ) : ones n ++ [true] = true :: ones n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [ones] using congrArg (List.cons true) ih

abbrev Phase := Fin 10
def next (p : Phase) : Phase := ⟨(p.val + 1) % 10, Nat.mod_lt _ (by decide)⟩

def tail : Phase → List Letter
  | 0 => [B,A,A]
  | 1 => [C,B]
  | 2 => [A,B,A]
  | 3 => [B,C]
  | 4 => [C,A,A]
  | 5 => [A,B,B]
  | 6 => [B,C,A]
  | 7 => [A,A,B]
  | 8 => [B,B,A]
  | 9 => [C,C]

def extra : Phase → List Letter
  | 1 => [A]
  | 4 => [A]
  | 6 => [C]
  | 9 => [A,A]
  | _ => []

def gain : Phase → ℕ
  | 1 => 0
  | 5 => 0
  | 7 => 0
  | _ => 1

def front : Phase → List Bool
  | 0 | 2 | 4 | 6 | 8 => [false]
  | _ => [false, false, false]

def left : Phase → List Letter
  | 0 | 2 | 4 | 6 | 8 => []
  | _ => [A,C]

def suffix (p : Phase) (t : ℕ) := encode (tail p) ++ ones (t+1)

lemma suffix_starts (p : Phase) (t : ℕ) : ∃ u, suffix p t = true :: u := by
  fin_cases p <;> simp [suffix, tail, encode, block]

lemma rewrite_suffix (p : Phase) (t : ℕ) :
    rewrite (suffix p t) = [false,false] ++ encode (extra p) ++
      suffix (next p) (t + gain p) := by
  fin_cases p <;>
    simp [suffix, tail, extra, next, gain, encode, block, ones, rewrite,
      List.append_assoc, Nat.add_assoc]

lemma rewrite_interior (v : List Letter) (p : Phase) (t : ℕ) :
    rewrite (encode v ++ suffix p t) =
      [false,false] ++ encode (sigma v) ++ encode (extra p) ++
        suffix (next p) (t + gain p) := by
  obtain ⟨u, hu⟩ := suffix_starts p t
  rw [hu, rewrite_encode, ← hu, rewrite_suffix]
  simpa [List.append_assoc] using congrArg
    (fun w => w ++ encode (extra p) ++ suffix (next p) (t + gain p)) (rotation v)

def shape (p : Phase) (v : List Letter) (t : ℕ) : List Bool :=
  front p ++ encode v ++ suffix p t

lemma shape_starts (v : List Letter) (p : Phase) (t : ℕ) :
    ∃ u, encode v ++ suffix p t = true :: u := by
  cases v with
  | nil => simpa [encode] using suffix_starts p t
  | cons a v => cases a <;> simp [encode, block]

/-- Every boundary state is checked against the literal scanner. -/
theorem rewrite_shape (p : Phase) (v : List Letter) (t : ℕ) :
    rewrite (shape p v t) =
      shape (next p) (left p ++ sigma v ++ extra p) (t + gain p) := by
  obtain ⟨u, hu⟩ := shape_starts v p t
  have h := rewrite_interior v p t
  rw [hu] at h
  unfold shape
  simp only [List.append_assoc]
  rw [hu]
  fin_cases p <;>
    simpa [front, left, next, encode, block, List.append_assoc, rewrite]
      using congrArg (fun w => [false] ++ w) h

end Kimberling288511
