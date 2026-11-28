import Mathlib.Tactic

/-! Exact finite-word bridge for the nonoverlapping scanner in OEIS A289128. -/
namespace Kimberling289128

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, false, true, false] ++ rewrite w
  | false :: true :: w => [false, true, true] ++ rewrite w
  | true :: false :: w => [false, true, false] ++ rewrite w
  | true :: true :: w => true :: rewrite (true :: w)
termination_by w => w.length

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

def repeatWord (w : List Bool) : ℕ → List Bool
  | 0 => []
  | n+1 => w ++ repeatWord w n

lemma repeatWord_add (w : List Bool) (m n : ℕ) :
    repeatWord w (m+n) = repeatWord w m ++ repeatWord w n := by
  induction m with
  | zero => simp [repeatWord]
  | succ m ih =>
    simpa [repeatWord, List.append_assoc, Nat.succ_add] using
      congrArg (fun v => w ++ v) ih

def A (t : ℕ) : List Bool := false :: repeatWord [true, false] t
def B (t : ℕ) : List Bool := false :: repeatWord [true, true, false] t

@[simp] lemma A_zero : A 0 = [false] := rfl
@[simp] lemma B_zero : B 0 = [false] := rfl
lemma A_succ (t : ℕ) : A (t+1) = [false, true] ++ A t := rfl
lemma B_succ (t : ℕ) : B (t+1) = [false, true, true] ++ B t := rfl

lemma rewrite_triples (s : ℕ) (u : List Bool) :
    rewrite (repeatWord [true, true, false] s ++ u) =
      repeatWord [true, false] (2*s) ++ rewrite u := by
  induction s with
  | zero => simp [repeatWord]
  | succ s ih =>
    rw [show 2*(s+1) = 2+2*s by omega, repeatWord_add _ 2 (2*s)]
    simpa [repeatWord, rewrite, List.append_assoc] using
      congrArg (fun v : List Bool => [true, false, true, false] ++ v) ih

/-- A paired block ends at a scanner boundary, for every possible suffix. -/
theorem rewrite_pair (t s : ℕ) (u : List Bool) :
    rewrite (A t ++ (B s ++ u)) = B t ++ (A (2*s+1) ++ rewrite u) := by
  induction t with
  | zero =>
    simpa [A, B, repeatWord, rewrite, List.append_assoc] using
      congrArg (fun v : List Bool => [false, false, true, false] ++ v)
        (rewrite_triples s u)
  | succ t ih =>
    simpa [A_succ, B_succ, rewrite, List.append_assoc] using
      congrArg (fun v : List Bool => [false, true, true] ++ v) ih

theorem rewrite_A (t : ℕ) : rewrite (A t) = B t := by
  induction t with
  | zero => simp [rewrite]
  | succ t ih =>
    simpa [A_succ, B_succ, rewrite] using
      congrArg (fun v : List Bool => [false, true, true] ++ v) ih

lemma rewrite_pair_nil (t s : ℕ) :
    rewrite (A t ++ B s) = B t ++ A (2*s+1) := by
  simpa [rewrite] using rewrite_pair t s []

def size : ℕ → ℕ
  | 0 => 1
  | m+1 => 2 * size m + 1

def core : ℕ → List Bool
  | 0 => [false, false, true, false]
  | m+1 => core m ++ A (size m) ++ B (size m)

/-- Both the exact image and the absence of a pending scanner letter. -/
theorem core_scanner (m : ℕ) :
    rewrite (core m) = core m ++ A (size m) ∧
    ∀ u, rewrite (core m ++ u) = rewrite (core m) ++ rewrite u := by
  induction m with
  | zero => simp [core, size, A, repeatWord, rewrite]
  | succ m ih =>
    constructor
    · simp only [core, List.append_assoc, ih.2, rewrite_pair, rewrite_pair_nil, List.append_nil,
        rewrite, ih.1, size]
    · intro u
      simp only [core, List.append_assoc, ih.2, rewrite_pair, rewrite_pair_nil, List.append_nil,
        rewrite, ih.1, size]

/-- The literal words at odd and positive even indices. -/
theorem word_blocks (m : ℕ) :
    word (2*m+1) = core m ∧
    word (2*m+2) = core m ++ A (size m) := by
  induction m with
  | zero => simp [word, core, size, A, repeatWord, rewrite]
  | succ m ih =>
    have ho : word (2*(m+1)+1) = core (m+1) := by
      rw [show 2*(m+1)+1 = (2*m+2)+1 by omega, word, ih.2,
        (core_scanner m).2, (core_scanner m).1, rewrite_A]
      simp [core, List.append_assoc]
    refine ⟨ho, ?_⟩
    rw [show 2*(m+1)+2 = (2*(m+1)+1)+1 by omega, word, ho,
      (core_scanner (m+1)).1]

end Kimberling289128
