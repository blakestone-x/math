import OMAStatements.S_oeis_a340138
import Mathlib.Order.Filter.Cofinite
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

open OMA.S_oeis_a340138
namespace RootCoverage

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

private def rich (r t : ℕ) := 10000000000 * (9*t+r) + 1023456789

private theorem every_digit (r t d : ℕ) (hd : d < 10) : hasDigit (rich r t) d := by
  have tab : ∀ e : Fin 10, ∃ i : Fin 10, 10^(i:ℕ) ≤ 1023456789 ∧
      10^(i:ℕ)*10 ∣ 10000000000 ∧ 1023456789 / 10^(i:ℕ) % 10 = (e:ℕ) := by decide
  obtain ⟨i, hi, hdiv, he⟩ := tab ⟨d,hd⟩
  refine ⟨i, hi.trans (Nat.le_add_left _ _), ?_⟩
  rw [← Nat.mod_mul_right_div_self] at he ⊢
  unfold rich
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hdiv _), Nat.zero_add,
    Nat.mod_mod, he]

private theorem prescribed_root (r t : ℕ) (h1 : 0 < r) (h2 : r < 10) :
    root (rich r t) = r := by
  unfold root rich
  split <;> omega

private theorem small_root (m : ℕ) : root m < 10 := by unfold root; split <;> omega

private theorem fresh (n : ℕ) : term (n+1) ∉ history n := by
  let xs := history n
  let y := rich 1 (xs.sum + 1)
  have high : xs.sum < y := by dsimp [y, rich]; omega
  have hy : y ∉ xs := fun h => (Nat.not_le_of_lt high) (le_list_sum h)
  exact (Nat.sInf_mem (s := {v : ℕ | v ∉ xs ∧ 0 < v ∧ hasDigit v (root (xs.headD 0))})
    ⟨y, hy, by omega, every_digit _ _ _ (small_root _)⟩).1

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

private theorem occurs (m : ℕ) (hm : 0 < m)
    (hallow : ∀ B, ∃ n ≥ B, hasDigit m (root (term n))) : ∃ j, term j = m := by
  by_contra! absent
  obtain ⟨B, hB⟩ := Filter.tendsto_atTop_atTop.mp term_injective.nat_tendsto_atTop (m+1)
  obtain ⟨n, hn, he⟩ := hallow B
  have high := hB (n+1) (by omega)
  have hnot : m ∉ history n := fun h => (listed h).elim (fun j eqn => absent j eqn)
  have low : term (n+1) ≤ m := Nat.sInf_le
    (s := {v : ℕ | v ∉ history n ∧ 0 < v ∧ hasDigit v (root (term n))}) ⟨hnot, hm, he⟩
  omega

private theorem nonzero_digit (m : ℕ) (hm : 0 < m) :
    ∃ r : ℕ, 0 < r ∧ r < 10 ∧ hasDigit m r := by
  let j := Nat.log 10 m
  have hlo : 10^j ≤ m := Nat.pow_log_le_self 10 (by omega)
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 10) m
  change m < 10^(j+1) at hhi
  rw [pow_succ, Nat.mul_comm] at hhi
  have hp : 0 < 10^j := Nat.pow_pos (by decide)
  have hd : m / 10^j < 10 := (Nat.div_lt_iff_lt_mul hp).mpr hhi
  exact ⟨m / 10^j, Nat.div_pos hlo hp, hd, j, hlo, Nat.mod_eq_of_lt hd⟩

private theorem term_surjective : Function.Surjective term := by
  intro m
  by_cases hz : m = 0
  · exact ⟨0, hz.symm⟩
  obtain ⟨r, hr, hr', hd⟩ := nonzero_digit m (by omega)
  apply occurs m (by omega)
  intro B
  let t := (history B).sum + 1
  let y := rich r t
  have high : (history B).sum < y := by dsimp [y, rich, t]; omega
  obtain ⟨n, hn⟩ := occurs y (by omega) (fun b => ⟨b, le_rfl, every_digit _ _ _ (small_root _)⟩)
  have late : B ≤ n := by
    by_contra! earlierN
    have bound := le_list_sum (earlier (Nat.le_of_lt earlierN))
    rw [hn] at bound
    omega
  exact ⟨n, late, by rw [hn, prescribed_root r t hr hr']; exact hd⟩

end RootCoverage

theorem OMA.solution : type_of% @OMA.S_oeis_a340138.main :=
  ⟨RootCoverage.term_injective, RootCoverage.term_surjective⟩
