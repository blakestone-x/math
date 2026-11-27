import Mathlib.Tactic

/-!
# Literal retained-singleton scanners for A289001, A289035, and A289239

`false` is the source letter 0 and `true` is 1.  A matched pair is consumed
once.  An unmatched leading letter is copied, and a final singleton is retained.
The invariant below proves that the unmatched `11` branch is never reached by
any of the source iterates; it is nevertheless part of the literal scanner.
-/

namespace A289004

inductive Variant where
  | left   -- A289001: 01 -> 001
  | middle -- A289035: 01 -> 010
  | right  -- A289239: 01 -> 100
  deriving DecidableEq

def image01 : Variant → List Bool
  | .left => [false, false, true]
  | .middle => [false, true, false]
  | .right => [true, false, false]

def rewrite (v : Variant) : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, false, true, false] ++ rewrite v w
  | false :: true :: w => image01 v ++ rewrite v w
  | true :: false :: w => [false, true, false] ++ rewrite v w
  | true :: true :: w => true :: rewrite v (true :: w)

def word (v : Variant) : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => rewrite v (word v n)

/-- Every 1 is followed by 0, so there are no `11` factors and the last letter
of every nonempty good word is 0. -/
def Good : List Bool → Prop
  | [] => True
  | false :: w => Good w
  | true :: false :: w => Good w
  | _ => False

lemma good_tail {b : Bool} {w : List Bool} (h : Good (b :: w)) : Good w := by
  cases b
  · exact h
  · cases w with
    | nil => exact False.elim h
    | cons c u =>
      cases c
      · exact h
      · exact False.elim h

lemma good_pair_tail {a b : Bool} {w : List Bool} (h : Good (a :: b :: w)) :
    Good w := good_tail (good_tail h)

lemma rewrite_left_zero (w : List Bool) :
    ∃ u, rewrite .left (false :: w) = false :: u := by
  cases w with
  | nil => exact ⟨[], rfl⟩
  | cons b u => cases b <;> simp [rewrite, image01]

theorem rewrite_good (v : Variant) (w : List Bool) (h : Good w) :
    Good (rewrite v w) := by
  induction w using (measure List.length).wf.induction with
  | h w ih =>
    cases w with
    | nil => trivial
    | cons a w =>
      cases w with
      | nil =>
        cases a
        · trivial
        · exact False.elim h
      | cons b u =>
        have hu : Good u := good_pair_tail h
        have hr : Good (rewrite v u) :=
          ih u (by change u.length < _; simp only [List.length_cons]; omega) hu
        cases a <;> cases b
        · simpa [rewrite, Good] using hr
        · cases v with
          | middle => simpa [rewrite, image01, Good] using hr
          | right => simpa [rewrite, image01, Good] using hr
          | left =>
            cases u with
            | nil => exact False.elim h
            | cons c t =>
              cases c
              · obtain ⟨z, hz⟩ := rewrite_left_zero t
                simp only [hz, Good] at hr
                simpa [rewrite, image01, hz, Good] using hr
              · exact False.elim h
        · simpa [rewrite, Good] using hr
        · exact False.elim h

theorem word_good (v : Variant) (n : ℕ) : Good (word v n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact rewrite_good v _ ih

/-- Each consumed pair contributes exactly one 1; an odd final 0 contributes none. -/
theorem rewrite_ones (v : Variant) (w : List Bool) (h : Good w) :
    (rewrite v w).count true = w.length / 2 := by
  induction w using (measure List.length).wf.induction with
  | h w ih =>
    cases w with
    | nil => simp [rewrite]
    | cons a w =>
      cases w with
      | nil => cases a <;> simp_all [rewrite, Good]
      | cons b u =>
        have hr := ih u
          (by change u.length < _; simp only [List.length_cons]; omega) (good_pair_tail h)
        have hm := Nat.mod_lt u.length (by omega : 0 < 2)
        have hd := Nat.mod_add_div u.length 2
        cases a <;> cases b <;> cases v <;>
          simp_all only [rewrite, image01, Good, List.count_append, List.count_cons,
            List.count_nil, List.length_cons, List.length_nil,
            show (true == true) = true from rfl, show (false == true) = false from rfl,
            List.nil_append, List.cons_append, Bool.false_eq_true, if_false, if_true] <;> omega

/-- The exact length identity, including the retained odd final letter. -/
theorem rewrite_length (v : Variant) (w : List Bool) (h : Good w) :
    (rewrite v w).length + w.count true + w.length % 2 = 2 * w.length := by
  induction w using (measure List.length).wf.induction with
  | h w ih =>
    cases w with
    | nil => simp [rewrite]
    | cons a w =>
      cases w with
      | nil => cases a <;> simp_all [rewrite, Good]
      | cons b u =>
        have hr := ih u
          (by change u.length < _; simp only [List.length_cons]; omega) (good_pair_tail h)
        cases a <;> cases b <;> cases v <;>
          simp_all only [rewrite, image01, Good, List.length_append, List.count_cons,
            List.length_cons, List.length_nil,
            show (true == true) = true from rfl, show (false == true) = false from rfl,
            List.nil_append, List.cons_append, Bool.false_eq_true, if_false, if_true] <;> omega

lemma good_ones_bound (w : List Bool) (h : Good w) : 2 * w.count true ≤ w.length := by
  induction w using (measure List.length).wf.induction with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a u =>
      cases a
      · have ht := ih u (by change u.length < _; simp only [List.length_cons]; omega) h
        simpa only [List.count_cons, show (false == true) = false from rfl, Bool.false_eq_true, if_false, if_true, zero_add,
          List.length_cons] using Nat.le_succ_of_le ht
      · cases u with
        | nil => exact False.elim h
        | cons b t =>
          cases b
          · have ht := ih t (by change t.length < _; simp only [List.length_cons]; omega) h
            simp only [List.count_cons, show (true == true) = true from rfl, show (false == true) = false from rfl,
              Bool.false_eq_true, if_false, if_true, List.length_cons]
            omega
          · exact False.elim h

end A289004
