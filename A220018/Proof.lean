import OrbitCount
import DivisorGrid
import GridSums

namespace CyclotomicCosets

lemma cosetCount_ten_eq_grid (b n : ℕ) (hb : b.Coprime 10) :
    cosetCount b (10^n) (hb.pow_right n) = gridCount b n := by
  rw [cosetCount_eq_divisor_sum, divisor_sum_eq_grid]
  rfl

/-- Literal source sequences, with the source's offset-one convention understood. -/
noncomputable def C3 (n : ℕ) : ℕ := cosetCount 3 (10^n) ((by decide : Nat.Coprime 3 10).pow_right n)
noncomputable def C7 (n : ℕ) : ℕ := cosetCount 7 (10^n) ((by decide : Nat.Coprime 7 10).pow_right n)
noncomputable def C9 (n : ℕ) : ℕ := cosetCount 9 (10^n) ((by decide : Nat.Coprime 9 10).pow_right n)
noncomputable def C13 (n : ℕ) : ℕ := cosetCount 13 (10^n) ((by decide : Nat.Coprime 13 10).pow_right n)

/-- Barker's A220018 conjecture, for every source index n > 2. -/
theorem A220018_conjecture (n : ℕ) (hn : 2 < n) :
    (C3 n : ℤ) = 8*(n:ℤ)^2 - 14*n - 1 := by
  have h : C3 n + 14*n + 1 = 8*n^2 := by
    rw [C3, cosetCount_ten_eq_grid 3 n (by decide)]
    exact grid_three_closed n (by omega)
  have hz : (C3 n : ℤ) + 14*n + 1 = 8*(n:ℤ)^2 := by exact_mod_cast h
  linarith

/-- Barker's A220019 conjecture, for every source index n > 3. -/
theorem A220019_conjecture (n : ℕ) (hn : 3 < n) :
    (C7 n : ℤ) = 5*(16*(n:ℤ)^2 - 60*n + 37) := by
  have h : C7 n + 300*n = 80*n^2 + 185 := by
    rw [C7, cosetCount_ten_eq_grid 7 n (by decide)]
    exact grid_seven_closed n (by omega)
  have hz : (C7 n : ℤ) + 300*n = 80*(n:ℤ)^2 + 185 := by exact_mod_cast h
  linarith

/-- Barker's A220020 conjecture, for every source index n > 2. -/
theorem A220020_conjecture (n : ℕ) (hn : 2 < n) :
    (C9 n : ℤ) = 4*(4*(n:ℤ)^2 - 7*n - 1) := by
  have h : C9 n + 28*n + 4 = 16*n^2 := by
    rw [C9, cosetCount_ten_eq_grid 9 n (by decide)]
    exact grid_nine_closed n (by omega)
  have hz : (C9 n : ℤ) + 28*n + 4 = 16*(n:ℤ)^2 := by exact_mod_cast h
  linarith

/-- Barker's A221855 conjecture, for every source index n > 2. -/
theorem A221855_conjecture (n : ℕ) (hn : 2 < n) :
    (C13 n : ℤ) = 2*(n:ℤ)*(4*n-7) := by
  have h : C13 n + 14*n = 8*n^2 := by
    rw [C13, cosetCount_ten_eq_grid 13 n (by decide)]
    exact grid_thirteen_closed n (by omega)
  have hz : (C13 n : ℤ) + 14*n = 8*(n:ℤ)^2 := by exact_mod_cast h
  nlinarith

#print axioms A220018_conjecture
#print axioms A220019_conjecture
#print axioms A220020_conjecture
#print axioms A221855_conjecture
#print axioms cosetCount_ten_eq_grid

end CyclotomicCosets
