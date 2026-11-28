import OMAStatements.S_oeis_a275482

open OMA.S_oeis_a275482

private theorem term_pos (n : ℕ) : 0 < term n := by
  cases n with
  | zero => decide
  | succ n => change 0 < 1 + _; omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a275482.main) := by
  intro h
  obtain ⟨n, hn⟩ := h.2 0
  have hp := term_pos n
  omega
