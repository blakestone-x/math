import Population

namespace VonNeumann

private def smallTest (r n x y : ℕ) :=
  (r == 323 && n == 1) || (cell r n x y == cell 65 n x y)

set_option maxHeartbeats 2000000 in
private theorem early (r n : ℕ) (hr : r=65 ∨ r=321 ∨ r=323) (hn : n < 6) (h : r≠323 ∨ n≠1) :
    cell r n=cell 65 n := by
  have cert : (List.range 6).all (fun n => (List.range 6).all (fun x =>
      (List.range 6).all (smallTest r n x)))=true := by
    rcases hr with rfl|rfl|rfl <;> decide +kernel
  funext x y
  by_cases small : x < 6 ∧ y < 6
  · have e := checked (List.all_eq_true.mp cert n (List.mem_range.mpr hn)) small.1 small.2
    simp only [smallTest,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at e
    tauto
  · rw [outside r n x y (by omega),outside 65 n x y (by omega)]
    rcases hr with rfl|rfl|rfl <;> interval_cases n <;> decide

theorem cross_agreement (r n : ℕ) (hr : r=65 ∨ r=321 ∨ r=323) (h : r≠323 ∨ n≠1) : cell r n=cell 65 n := by
  by_cases sm : n < 6
  · exact early r n hr sm h
  have a := cross_shapes r (n/2) hr (by omega)
  have b := cross_shapes 65 (n/2) (Or.inl rfl) (by omega)
  rcases Nat.mod_two_eq_zero_or_one n with e|e
  · simpa only [show 2*(n/2)=n by omega] using a.1.trans b.1.symm
  · simpa only [show 2*(n/2)+1=n by omega] using a.2.trans b.2.symm

theorem stage_one_difference : cell 323 1 0 0=true ∧ cell 65 1 0 0=false := by decide

theorem population_from_five (r n : ℕ) (hr : r=65 ∨ r=321 ∨ r=323) (hn : 5≤n) :
    population r n=if n%2=0 then 2*n+5 else 4*n^2-2*n+6 := by
  by_cases sm : n=5
  · subst n; rcases hr with rfl|rfl|rfl <;> decide +kernel
  rcases Nat.mod_two_eq_zero_or_one n with e|e
  · rw [if_pos e]
    have a := even_population r (n/2) hr (by omega)
    rw [show 2*(n/2)=n by omega] at a
    omega
  · rw [if_neg (by omega)]
    have a := odd_population r (n/2) hr (by omega)
    simpa only [show 2*(n/2)+1=n by omega] using a

#print axioms cross_agreement
#print axioms population_from_five
end VonNeumann
