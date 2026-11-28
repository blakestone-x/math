import OMAStatements.S_oeis_a350831
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Order.Filter.Cofinite
import Mathlib.Data.Fintype.Pigeonhole

open OMA.S_oeis_a350831
namespace PrimeBayonets

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

private theorem prime_table (d : ℕ) (hp : 0 < d) (hb : d < 10) :
    ∃ f : ℕ, 0 < f ∧ f < 10 ∧ paired d f := by
  have tab : ∀ e : Fin 9, ∃ f : Fin 9, paired (e.val+1) (f.val+1) := by
    unfold paired; decide
  obtain ⟨f, h⟩ := tab ⟨d-1, by omega⟩
  exact ⟨f.val+1, by omega, by omega, by simpa [Nat.sub_add_cancel hp] using h⟩

private theorem endpoints (f l t : ℕ) (hf : 0 < f) (hf' : f < 10) (hl : 0 < l) (hl' : l < 10) :
    ∃ y > t, (Nat.digits 10 y).getLastD 0 = f ∧ y % 10 = l := by
  let y := l + 10^(1+t)*f
  have dl := Nat.digits_of_lt 10 l (by omega) hl'
  have df := Nat.digits_of_lt 10 f (by omega) hf'
  have digits := Nat.digits_append_zeroes_append_digits (b := 10) (k := t) (m := f) (n := l)
    (by decide) hf
  rw [dl, df] at digits
  change ([l] ++ List.replicate t 0) ++ [f] = Nat.digits 10 y at digits
  have ht : 1+t < 10^(1+t) := Nat.lt_pow_self (by decide)
  have hm := Nat.le_mul_of_pos_right (10^(1+t)) hf
  refine ⟨y, by dsimp [y]; omega, ?_, ?_⟩
  · rw [← digits, List.getLastD_concat]
  · dsimp [y]
    simp [pow_add, Nat.mul_assoc, Nat.add_mod, Nat.mod_eq_of_lt hl']

private theorem next_spec (xs : List ℕ) (hx : (xs.headD 1) % 10 ≠ 0) :
    next xs ∉ xs ∧ 0 < next xs ∧ allowed (xs.headD 1) (next xs) := by
  obtain ⟨f, hf, hf', pair⟩ := prime_table ((xs.headD 1) % 10) (by omega) (Nat.mod_lt _ (by decide))
  obtain ⟨y, large, lead, last⟩ := endpoints f 1 xs.sum hf hf' (by decide) (by decide)
  apply Nat.sInf_mem (s := {y : ℕ | y ∉ xs ∧ 0 < y ∧ allowed (xs.headD 1) y})
  refine ⟨y, fun hm => (Nat.not_le_of_lt large) (le_list_sum hm), by omega, ?_, ?_⟩
  · omega
  · simpa only [lead] using pair

private theorem live (n : ℕ) : term n % 10 ≠ 0 := by
  induction n with
  | zero => decide
  | succ n ih => exact (next_spec (history n) ih).2.2.1

private theorem fresh (n : ℕ) : term (n+1) ∉ history n := (next_spec _ (live n)).1

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

private def recurrent (d : ℕ) := ∀ B : ℕ, ∃ n ≥ B, term n % 10 = d

private theorem some_state : ∃ d, 0 < d ∧ d < 10 ∧ recurrent d := by
  let color (i : ℕ) : Fin 10 := ⟨term i % 10, Nat.mod_lt _ (by decide)⟩
  obtain ⟨d, hi⟩ := Finite.exists_infinite_fiber color
  have recur : recurrent d.val := by
    intro B
    obtain ⟨n, hn, hB⟩ := (Set.infinite_coe_iff.mp hi).exists_gt B
    exact ⟨n, hB.le, congrArg Fin.val (show color n = d from hn)⟩
  obtain ⟨n, _, eqn⟩ := recur 0
  have := live n
  exact ⟨d, by omega, d.isLt, recur⟩

private theorem after_state (d m : ℕ) (hrec : recurrent d) (hm : 0 < m)
    (liveM : m % 10 ≠ 0) (hp : paired d ((Nat.digits 10 m).getLastD 0)) : ∃ i, term i = m := by
  by_contra! absent
  obtain ⟨B, hB⟩ := Filter.tendsto_atTop_atTop.mp term_injective.nat_tendsto_atTop (m+1)
  obtain ⟨n, hn, hd⟩ := hrec B
  have high := hB (n+1) (by omega)
  have hnot : m ∉ history n := fun h => (listed h).elim (fun j eqn => absent j eqn)
  have low : term (n+1) ≤ m := Nat.sInf_le
    (s := {v : ℕ | v ∉ history n ∧ 0 < v ∧ allowed (term n) v})
    ⟨hnot, hm, liveM, by simpa [hd] using hp⟩
  omega

private theorem all_states (l : ℕ) (hl : 0 < l) (hl' : l < 10) : recurrent l := by
  obtain ⟨d, hd, hd', hrec⟩ := some_state
  obtain ⟨f, hf, hf', hpair⟩ := prime_table d hd hd'
  intro B
  obtain ⟨y, hy, hlead, hlast⟩ := endpoints f l (history B).sum hf hf' hl hl'
  obtain ⟨n, hn⟩ := after_state d y hrec (by omega) (by omega) (by simpa only [hlead] using hpair)
  refine ⟨n, ?_, by rw [hn, hlast]⟩
  by_contra! lt
  have h := le_list_sum (earlier (Nat.le_of_lt lt))
  rw [hn] at h
  omega

private theorem coverage (m : ℕ) (hm : 0 < m) (hlive : m % 10 ≠ 0) : ∃ n, term n = m := by
  let ds := Nat.digits 10 m
  have ne : ds ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have first : ds.getLastD 0 = ds.getLast ne := by simp [List.getLast?_eq_some_getLast ne]
  have nz : ds.getLast ne ≠ 0 := Nat.getLast_digit_ne_zero _ (by omega)
  have lt : ds.getLast ne < 10 := Nat.digits_lt_base (by decide : 1 < 10) (List.getLast_mem ne)
  obtain ⟨d, hd, hd', pair⟩ := prime_table (ds.getLast ne) (by omega) lt
  apply after_state d m (all_states d hd hd') hm hlive
  change paired d (ds.getLastD 0)
  rw [first]
  exact pair.symm

end PrimeBayonets

theorem OMA.solution : type_of% @OMA.S_oeis_a350831.main := PrimeBayonets.coverage
