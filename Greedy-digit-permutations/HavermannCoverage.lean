import OMAStatements.S_oeis_a218468
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.Ring

open OMA.S_oeis_a218468
namespace HavermannCoverage

private theorem le_list_sum {xs : List ℕ} {m : ℕ} (hm : m ∈ xs) : m ≤ xs.sum := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    rcases List.mem_cons.mp hm with h | h
    · subst m; simp
    · have := ih h
      simp only [List.sum_cons]
      omega

private theorem earlier {i n : ℕ} (h : i ≤ n) : term i ∈ history n := by
  induction n with
  | zero => have : i = 0 := by omega
            subst i; simp [history, term]
  | succ n ih =>
    by_cases he : i = n+1
    · subst i; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by omega))

private theorem listed {n m : ℕ} (h : m ∈ history n) : ∃ j, term j = m := by
  induction n with
  | zero => simp [history] at h; exact ⟨0, h.symm⟩
  | succ n ih =>
    rcases List.mem_cons.mp h with eqn | hm
    · exact ⟨n+1, eqn.symm⟩
    · exact ih hm

private def permits (x y : ℕ) : Prop := ∃ d ∈ Nat.digits 10 x, 0 < d ∧ d ∣ y
private def word (t : ℕ) : ℕ := 120 + 10^3*(63*t+15)

private theorem has_one (t : ℕ) : 1 ∈ Nat.digits 10 (word t) := by
  have app := Nat.digits_append_digits (b := 10) (n := 120) (m := 63*t+15) (by decide)
  rw [show (Nat.digits 10 120).length = 3 by decide] at app
  rw [show Nat.digits 10 (word t) = _ from app.symm]
  exact List.mem_append_left _ (by decide : 1 ∈ Nat.digits 10 120)

private theorem universal (t x : ℕ) (hx : 0 < x) : permits x (word t) := by
  have ne : Nat.digits 10 x ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  let d := (Nat.digits 10 x).getLast ne
  have mem : d ∈ Nat.digits 10 x := List.getLast_mem ne
  have nz : d ≠ 0 := Nat.getLast_digit_ne_zero 10 (by omega)
  have lt : d < 10 := Nat.digits_lt_base (by decide) mem
  have tab : ∀ i : Fin 9, i.val+1 ∣ 2520 := by decide
  have small := tab ⟨d-1, by omega⟩
  have hd : d ∣ 2520 := by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ d)] using small
  have mult : 2520 ∣ word t := ⟨25*t+6, by unfold word; ring⟩
  exact ⟨d, mem, by omega, hd.trans mult⟩

private theorem positive (n : ℕ) : 0 < term n := by
  cases n with
  | zero => decide
  | succ n => change 0 < 1 + _; omega

private theorem fresh (n : ℕ) : term (n+1) ∉ history n := by
  let xs := history n
  let y := word (xs.sum+1)
  have hy : xs.sum < y := by dsimp [y,word]; omega
  have hsub : y-1+1=y := by omega
  have hh : y-1 ∈ {k : ℕ | k+1 ∉ xs ∧ permits (term n) (k+1)} := by
    change y-1+1 ∉ xs ∧ permits (term n) (y-1+1)
    rw [hsub]
    exact ⟨fun h => (Nat.not_le_of_lt hy) (le_list_sum h), universal _ _ (positive n)⟩
  have hne := (Nat.sInf_mem (Set.nonempty_of_mem hh)).1
  change 1 + sInf {k : ℕ | k+1 ∉ xs ∧ permits (term n) (k+1)} ∉ xs
  rw [Nat.add_comm 1]
  exact hne

private theorem term_injective : Function.Injective term := by
  have diff : ∀ i j : ℕ, i < j → term i ≠ term j := by
    intro i j h eqn
    cases j with
    | zero => omega
    | succ j =>
      apply fresh j
      exact eqn ▸ earlier (show i ≤ j by omega)
  intro i j h
  rcases lt_trichotomy i j with lt | eqn | gt
  · exact (diff _ _ lt h).elim
  · exact eqn
  · exact (diff _ _ gt h.symm).elim

private theorem occurs (m : ℕ) (hm : 0 < m) (recur : ∀ B, ∃ n ≥ B, permits (term n) m) :
    ∃ i, term i = m := by
  by_contra! absent
  obtain ⟨B, hB⟩ := Filter.tendsto_atTop_atTop.mp term_injective.nat_tendsto_atTop (m+1)
  obtain ⟨n, hn, he⟩ := recur B
  have high := hB (n+1) (by omega)
  have hnot : m ∉ history n := fun h => (listed h).elim (fun j eqn => absent j eqn)
  let candidates := {k : ℕ | k+1 ∉ history n ∧ permits (term n) (k+1)}
  have hmem : m-1 ∈ candidates := by
    change m-1+1 ∉ history n ∧ permits (term n) (m-1+1)
    simpa only [Nat.sub_add_cancel hm] using And.intro hnot he
  have low := Nat.sInf_le hmem
  change m+1 ≤ 1 + sInf candidates at high
  omega

/-- The permutation assertion of A218468. Its separate all-exponents fixed-point
assertion is established by the paper and eight finite prefix certificates. -/
theorem permutation : Function.Injective term ∧ (∀ m : ℕ, 0 < m ↔ ∃ n, term n = m) := by
  refine ⟨term_injective, fun m => ⟨?_, ?_⟩⟩
  · intro hm
    apply occurs m hm
    intro B
    let t := (history B).sum+1
    have large : (history B).sum < word t := by dsimp [word,t]; omega
    obtain ⟨j, hj⟩ := occurs (word t) (by omega) (fun b => ⟨b, le_rfl, universal _ _ (positive _)⟩)
    refine ⟨j, ?_, 1, by rw [hj]; exact has_one _, by decide, one_dvd _⟩
    by_contra! early
    have h := le_list_sum (earlier (Nat.le_of_lt early))
    rw [hj] at h
    omega
  · rintro ⟨j, rfl⟩; exact positive j

#print axioms permutation
end HavermannCoverage
