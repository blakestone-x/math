import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

open Nat

namespace LucasGreedy

macro "fibomega" : tactic =>
  `(tactic| ((try simp only [Nat.add_assoc, Nat.reduceAdd] at *) <;> omega))

def lucas : ℕ → ℕ
  | 0 => 2
  | k+1 => fib k + fib (k+2)

theorem luc_rec (k : ℕ) : lucas (k+2) = lucas k + lucas (k+1) := by
  cases k with
  | zero => decide
  | succ k => change fib (k+2)+fib (k+4) = (fib k+fib (k+2))+(fib (k+1)+fib (k+3));
              have a := @fib_add_two k; have b := @fib_add_two (k+2); fibomega

theorem luc_mono : Monotone (fun k => lucas (k+1)) := by
  intro a b h
  exact Nat.add_le_add (fib_mono h) (fib_mono (by fibomega : a+2 ≤ b+2))

theorem luc_pos (j : ℕ) : 0 < lucas j := by
  cases j with
  | zero => decide
  | succ i => have := fib_pos.mpr (by fibomega : 0 < i+2); simp only [lucas]; fibomega

theorem luc_le_at {i k : ℕ} (h : i ≤ k+2) : lucas i ≤ lucas (k+2) := by
  cases i with
  | zero => exact (by decide : lucas 0 ≤ lucas 2).trans (luc_mono (by fibomega : 1 ≤ k+1))
  | succ j => exact luc_mono (by fibomega : j ≤ k+1)

inductive Basis | fibonacci | lucasOnly | mixed deriving DecidableEq

def coin (b : Basis) (n : ℕ) : Bool :=
  (List.range (n+3)).any fun i => match b with
    | .fibonacci => fib i == n
    | .lucasOnly => lucas i == n
    | .mixed => fib i == n || lucas i == n

theorem fib_coin (n : ℕ) : coin .fibonacci n ↔ ∃ i, fib i = n := by
  simp only [coin, List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨i, _, h⟩; exact ⟨i,h⟩
  · rintro ⟨i,rfl⟩; exact ⟨i,by have := le_fib_add_one i; fibomega,rfl⟩

theorem luc_coin (n : ℕ) : coin .lucasOnly n ↔ ∃ i, lucas i = n := by
  simp only [coin, List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨i, _, h⟩; exact ⟨i,h⟩
  · rintro ⟨i,rfl⟩
    refine ⟨i, ?_, rfl⟩
    cases i with
    | zero => decide
    | succ k => have := le_fib_add_one k; simp only [lucas]; fibomega

theorem mixed_coin (n : ℕ) : coin .mixed n ↔ coin .fibonacci n ∨ coin .lucasOnly n := by
  simp only [coin, List.any_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq]
  aesop

def largest (b : Basis) (n : ℕ) := findGreatest (fun k => coin b k = true) n

def weightAux (b : Basis) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel+1, n => if 0 < largest b n then 1 + weightAux b fuel (n-largest b n) else 0

def weight (b : Basis) (n : ℕ) : ℕ := weightAux b n n

private theorem aux_agree (b : Basis) (n f g : ℕ) (hf : n≤f) (hg : n≤g) :
    weightAux b f n = weightAux b g n := by
  induction n using Nat.strong_induction_on generalizing f g with
  | h n ih =>
    by_cases hn : n=0
    · subst n; cases f <;> cases g <;> simp [weightAux,largest]
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [weightAux]
        by_cases hp : 0<largest b n
        · rw [if_pos hp,if_pos hp]
          congr 1
          exact ih _ (by omega) f g (by omega) (by omega)
        · simp [hp]

theorem weight_step (b : Basis) (n : ℕ) (hp : 0 < largest b n) :
    weight b n = 1+weight b (n-largest b n) := by
  have le : largest b n ≤ n := Nat.findGreatest_le _
  cases n with
  | zero => omega
  | succ n =>
    change weightAux b (n+1) (n+1) = _
    rw [weightAux,if_pos hp]
    exact congrArg (1+·) (aux_agree b _ _ _ (by omega) le_rfl)

abbrev z := weight .fibonacci
abbrev u := weight .lucasOnly
abbrev w := weight .mixed

theorem selected {b : Basis} {c r : ℕ} (hc : 0 < c) (mem : coin b c)
    (gap : ∀ d, coin b d → c < d → c+r < d) : weight b (c+r) = 1+weight b r := by
  have pick : largest b (c+r) = c := findGreatest_eq_iff.mpr
    ⟨by fibomega, fun _ => mem, fun d lo hi hd => (Nat.not_lt_of_ge hi) (gap d hd lo)⟩
  rw [weight_step b _ (by simpa [pick] using hc), pick, Nat.add_sub_cancel_left]

theorem z_step (k r : ℕ) (hr : r < fib (k+1)) : z (fib (k+2)+r) = 1+z r := by
  apply selected (fib_pos.mpr (by fibomega)) ((fib_coin _).mpr ⟨_,rfl⟩)
  intro d hd big
  obtain ⟨i,rfl⟩ := (fib_coin _).mp hd
  have idx : k+3 ≤ i := by by_contra! h; exact (not_le.mpr big) (fib_mono (by omega : i ≤ k+2))
  have := @fib_add_two (k+1)
  exact Nat.lt_of_lt_of_le (by fibomega : fib (k+2)+r < fib (k+3)) (fib_mono idx)

theorem u_step (k r : ℕ) (hr : r < lucas (k+1)) : u (lucas (k+2)+r) = 1+u r := by
  apply selected (luc_pos _) ((luc_coin _).mpr ⟨_,rfl⟩)
  intro d hd big
  obtain ⟨i,rfl⟩ := (luc_coin _).mp hd
  have idx : k+3 ≤ i := by by_contra! h; exact (not_le.mpr big) (luc_le_at (by fibomega))
  have rec := luc_rec (k+1)
  cases i with
  | zero => fibomega
  | succ j => exact Nat.lt_of_lt_of_le (by fibomega : lucas (k+2)+r < lucas (k+3)) (luc_mono (by fibomega : k+2 ≤ j))

theorem w_fib (k r : ℕ) (hr : r < fib (k+1)) : w (fib (k+3)+r) = 1+w r := by
  apply selected (fib_pos.mpr (by fibomega)) ((mixed_coin _).mpr (.inl ((fib_coin _).mpr ⟨_,rfl⟩)))
  intro d hd big
  have f0 := @fib_add_two k
  have f1 := @fib_add_two (k+1)
  have f2 := @fib_add_two (k+2)
  rcases (mixed_coin _).mp hd with hd | hd
  · obtain ⟨i,rfl⟩ := (fib_coin _).mp hd
    have idx : k+4 ≤ i := by by_contra! h; exact (not_le.mpr big) (fib_mono (by omega : i ≤ k+3))
    exact Nat.lt_of_lt_of_le (by fibomega : fib (k+3)+r < fib (k+4)) (fib_mono idx)
  · obtain ⟨i,rfl⟩ := (luc_coin _).mp hd
    cases i with
    | zero => have h := fib_mono (by fibomega : 3 ≤ k+3); norm_num [lucas] at big; have : fib 3=2 := rfl; fibomega
    | succ j =>
      by_cases lo : j ≤ k
      · have h := luc_mono lo
        have hk := fib_mono (by fibomega : k ≤ k+1)
        simp only [lucas] at h big
        fibomega
      · have h := luc_mono (by fibomega : k+1 ≤ j)
        simp only [lucas] at h ⊢
        fibomega

theorem w_luc (k r : ℕ) (hr : r < fib k) : w (lucas (k+2)+r) = 1+w r := by
  apply selected (luc_pos _) ((mixed_coin _).mpr (.inr ((luc_coin _).mpr ⟨_,rfl⟩)))
  intro d hd big
  have f0 := @fib_add_two k
  have f1 := @fib_add_two (k+1)
  have f2 := @fib_add_two (k+2)
  rcases (mixed_coin _).mp hd with hd | hd
  · obtain ⟨i,rfl⟩ := (fib_coin _).mp hd
    have hcut : lucas (k+2) = fib (k+1)+fib (k+3) := rfl
    have idx : k+4 ≤ i := by by_contra! h; have h' := fib_mono (show i ≤ k+3 by fibomega); fibomega
    exact Nat.lt_of_lt_of_le (by fibomega : lucas (k+2)+r < fib (k+4)) (fib_mono idx)
  · obtain ⟨i,rfl⟩ := (luc_coin _).mp hd
    have idx : k+3 ≤ i := by by_contra! h; exact (not_le.mpr big) (luc_le_at (by fibomega))
    cases i with
    | zero => fibomega
    | succ j =>
      have h := luc_mono (by fibomega : k+2 ≤ j)
      have hcut : lucas (k+2) = fib (k+1)+fib (k+3) := rfl
      have hnext : lucas (k+3) = fib (k+2)+fib (k+4) := rfl
      fibomega

def total (f : ℕ → ℕ) (n : ℕ) := ∑ i ∈ Finset.range n, f i

theorem total_add (f : ℕ → ℕ) (n r : ℕ) :
    total f (n+r) = total f n + ∑ i ∈ Finset.range r, f (n+i) :=
  Finset.sum_range_add _ _ _

end LucasGreedy
