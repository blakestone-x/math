import Std

namespace Nakamura

/-- Number of pairs formed by e later smaller entries. -/
def pairs : Nat → Nat
  | 0 => 0
  | k+1 => pairs k + k

theorem twice_pairs (k : Nat) : 2 * pairs (k+1) = k * (k+1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    change 2 * (pairs (k+1) + (k+1)) = (k+1) * (k+2)
    rw [Nat.mul_add, ih,
      show (k+1)*(k+2) = (k+1)*(k+1) + (k+1) by rw [Nat.mul_succ],
      Nat.succ_mul k (k+1)]
    omega

theorem rank_le_cost_add_one (e : Nat) : e ≤ pairs e + 1 := by
  cases e with
  | zero => decide
  | succ k => simp only [pairs]; omega

def cost : List Nat → Nat
  | [] => 0
  | e::rest => pairs e + cost rest

/-- q is the largest pending size. Size one means that all comparisons are settled. -/
def advance (q e : Nat) : Nat := if e < q then q-1 else e

inductive Finishes : Nat → List Nat → Prop where
  | done : Finishes 1 []
  | step {q e : Nat} {rest : List Nat} (active : 2 ≤ q)
      (tail : Finishes (advance q e) rest) : Finishes q (e::rest)

def IsCluster : List Nat → Prop
  | [] => False
  | e::rest => 2 ≤ e ∧ Finishes e rest

theorem tail_bound {q : Nat} {word : List Nat} (h : Finishes q word) :
    word.length ≤ cost word + (q-1) := by
  induction h with
  | done => decide
  | @step q e rest active tail ih =>
    simp only [List.length_cons, cost]
    by_cases smaller : e < q
    · simp only [advance, if_pos smaller] at ih
      omega
    · simp only [advance, if_neg smaller] at ih
      have := rank_le_cost_add_one e
      omega

theorem cluster_bound {word : List Nat} (h : IsCluster word) :
    word.length ≤ cost word + 1 := by
  cases word with
  | nil => exact False.elim h
  | cons e rest =>
    obtain ⟨active, tail⟩ := h
    have ht := tail_bound tail
    have he := rank_le_cost_add_one e
    simp only [List.length_cons, cost]
    omega

theorem remaining_room {q : Nat} {word : List Nat} (h : Finishes q word) :
    q ≤ word.length+1 := by
  induction h with
  | done => decide
  | @step q e rest active tail ih =>
    simp only [List.length_cons]
    by_cases smaller : e < q
    · simp only [advance, if_pos smaller] at ih
      omega
    · simp only [advance, if_neg smaller] at ih
      omega

/-- Each digit fits its Lehmer bound when the obligatory final zero follows. -/
def Fits : List Nat → Prop
  | [] => True
  | e::rest => e ≤ rest.length+1 ∧ Fits rest

theorem finished_fits {q : Nat} {word : List Nat} (h : Finishes q word) : Fits word := by
  induction h with
  | done => trivial
  | @step q e rest active tail ih =>
    have room := remaining_room tail
    refine ⟨?_,ih⟩
    by_cases smaller : e < q
    · simp only [advance, if_pos smaller] at room
      omega
    · simpa [advance, smaller] using room

theorem cluster_fits {word : List Nat} (h : IsCluster word) : Fits word := by
  cases word with
  | nil => exact False.elim h
  | cons e rest => exact ⟨remaining_room h.2, finished_fits h.2⟩

def used : List (List Nat) → Nat
  | [] => 0
  | word::rest => word.length + used rest

def budget : List (List Nat) → Nat
  | [] => 0
  | word::rest => cost word + budget rest

theorem tuple_bound (ws : List (List Nat)) (h : ∀ w ∈ ws, IsCluster w) :
    used ws ≤ budget ws + ws.length := by
  induction ws with
  | nil => decide
  | cons w rest ih =>
    have head := cluster_bound (h w (by simp))
    have tail := ih (fun x hx => h x (by simp [hx]))
    simp only [used, budget, List.length_cons]
    omega

end Nakamura
