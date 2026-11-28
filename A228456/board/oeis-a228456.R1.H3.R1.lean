import OMAReductions.R_oeis_a228456_R1

/-!
# Pairing successive ratios of Sun's Hankel determinants

The scalar coefficient at index n below is the moment of the coefficient of
degree 2n in 1 / (1 - (X - 3)t + t²). The first step is the determinant-to-
coefficient identity. The second step classifies only those scalar coefficients
with a binary automaton. The paired-product invariant is proved here: only
nine unordered pairs are needed, with product three throughout their orbit.
-/
namespace OMA.R_oeis_a228456_R1_H3_R1

open OMA.S_oeis_a228456

/-- Factor the determinant modulo eight using the scalar Chebyshev moments. -/
def H1 : Prop := ∀ r : ℕ → ℤ, (∀ n, r n % 8 = ((∑ j ∈ Finset.range (n + 1), (-1 : ℤ)^j * ((2*n-j).choose j : ℤ) *
      ∑ i ∈ Finset.range (2*n-2*j+1), ((2*n-2*j).choose i : ℤ) *
        (-3 : ℤ)^(2*n-2*j-i) * b i) % 8)) →
  ∀ n, a n % 8 = (∏ j ∈ Finset.range (n+1), r j) % 8

/-- A 19-state two-kernel for the scalar moments, independent of the determinants. -/
def H2 : Prop :=
  let t : List (ℤ × ℕ × ℕ) := [(1,1,2), (1,3,4), (3,5,6), (1,3,7), (3,8,4), (3,5,9), (1,10,6), (5,11,6), (3,5,12), (7,13,4), (1,3,14), (5,15,7), (3,8,16), (7,17,9), (1,10,18), (5,15,14), (7,13,16), (7,17,12), (5,11,18)]
  ∃ u : ℕ → ℕ → ℤ, (∀ n, u 0 n % 8 = ((∑ j ∈ Finset.range (n + 1), (-1 : ℤ)^j * ((2*n-j).choose j : ℤ) *
      ∑ i ∈ Finset.range (2*n-2*j+1), ((2*n-2*j).choose i : ℤ) *
        (-3 : ℤ)^(2*n-2*j-i) * b i) % 8)) ∧
    (∀ s < 19, u s 0 = (t.getD s (0,0,0)).1) ∧
    (∀ s < 19, ∀ n, u s (2*n) = u (t.getD s (0,0,0)).2.1 n ∧
      u s (2*n+1) = u (t.getD s (0,0,0)).2.2 n)

section

set_option maxHeartbeats 1000000 in
theorem main : H1 → H2 → OMA.R_oeis_a228456_R1.H3 := by
  intro factors certificate
  obtain ⟨u, hu, hz, ht⟩ := certificate
  let P (n : ℕ) : Prop :=
    (u 1 n * u 2 n) % 8 = 3 ∧
    (u 3 n * u 5 n) % 8 = 3 ∧
    (u 4 n * u 6 n) % 8 = 3 ∧
    (u 7 n * u 9 n) % 8 = 3 ∧
    (u 8 n * u 10 n) % 8 = 3 ∧
    (u 11 n * u 13 n) % 8 = 3 ∧
    (u 12 n * u 14 n) % 8 = 3 ∧
    (u 15 n * u 17 n) % 8 = 3 ∧
    (u 16 n * u 18 n) % 8 = 3
  have invariant (n : ℕ) : P n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases zero : n = 0
      · subst n
        dsimp only [P]
        repeat' constructor
        all_goals (rw [hz _ (by decide), hz _ (by decide)]; decide)
      · let k := n / 2
        have hk : k < n := Nat.div_lt_self (by omega) (by decide)
        obtain ⟨p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := ih k hk
        by_cases he : n % 2 = 0
        · have hn : n = 2*k := by dsimp [k]; omega
          rw [hn]
          dsimp only [P]
          repeat' constructor
          · rw [(ht 1 (by decide) k).1, (ht 2 (by decide) k).1]
            exact p2
          · rw [(ht 3 (by decide) k).1, (ht 5 (by decide) k).1]
            exact p2
          · rw [(ht 4 (by decide) k).1, (ht 6 (by decide) k).1]
            exact p5
          · rw [(ht 7 (by decide) k).1, (ht 9 (by decide) k).1]
            exact p6
          · rw [(ht 8 (by decide) k).1, (ht 10 (by decide) k).1]
            change (u 5 k * u 3 k) % 8 = 3
            rw [mul_comm]; exact p2
          · rw [(ht 11 (by decide) k).1, (ht 13 (by decide) k).1]
            exact p8
          · rw [(ht 12 (by decide) k).1, (ht 14 (by decide) k).1]
            exact p5
          · rw [(ht 15 (by decide) k).1, (ht 17 (by decide) k).1]
            exact p8
          · rw [(ht 16 (by decide) k).1, (ht 18 (by decide) k).1]
            change (u 13 k * u 11 k) % 8 = 3
            rw [mul_comm]; exact p6
        · have hn : n = 2*k+1 := by dsimp [k]; omega
          rw [hn]
          dsimp only [P]
          repeat' constructor
          · rw [(ht 1 (by decide) k).2, (ht 2 (by decide) k).2]
            exact p3
          · rw [(ht 3 (by decide) k).2, (ht 5 (by decide) k).2]
            exact p4
          · rw [(ht 4 (by decide) k).2, (ht 6 (by decide) k).2]
            exact p3
          · rw [(ht 7 (by decide) k).2, (ht 9 (by decide) k).2]
            change (u 6 k * u 4 k) % 8 = 3
            rw [mul_comm]; exact p3
          · rw [(ht 8 (by decide) k).2, (ht 10 (by decide) k).2]
            exact p7
          · rw [(ht 11 (by decide) k).2, (ht 13 (by decide) k).2]
            exact p4
          · rw [(ht 12 (by decide) k).2, (ht 14 (by decide) k).2]
            exact p9
          · rw [(ht 15 (by decide) k).2, (ht 17 (by decide) k).2]
            change (u 14 k * u 12 k) % 8 = 3
            rw [mul_comm]; exact p7
          · rw [(ht 16 (by decide) k).2, (ht 18 (by decide) k).2]
            exact p9

  have paired (k : ℕ) : (u 0 (2*k) * u 0 (2*k+1)) % 8 = 3 := by
    rw [(ht 0 (by decide) k).1, (ht 0 (by decide) k).2]
    exact (invariant k).1
  let V (j : ℕ) : ℤ := ∏ i ∈ Finset.range j, u 0 i
  have next (k : ℕ) : V (2*(k+1)) % 8 = (V (2*k) % 8 * 3) % 8 := by
    dsimp only [V]
    rw [show 2*(k+1) = 2*k+1+1 by omega, Finset.prod_range_succ, Finset.prod_range_succ,
      mul_assoc, Int.mul_emod, paired]
  have oddClass (m : ℕ) : V (4*m+2) % 8 = 3 := by
    induction m with
    | zero =>
      have base := next 0
      simpa [V] using base
    | succ m ih =>
      rw [show 4*(m+1)+2 = 2*((2*m+2)+1) by omega, next,
        show 2*(2*m+2) = 2*((2*m+1)+1) by omega, next,
        show 2*(2*m+1) = 4*m+2 by omega, ih]
      decide
  intro m
  rw [factors _ hu (4*m+1)]
  exact oddClass m

end

end OMA.R_oeis_a228456_R1_H3_R1
