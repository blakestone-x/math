import Std

namespace Hardin

/-- The two possible signed values of the mixed difference on a square. -/
def Stress (d a b c e : Int) : Prop :=
  a + e - b - c = d ∨ a + e - b - c = -d

theorem corner_unique {q d a b c u v : Int}
    (small : q ≤ 2*d) (hu : 0 ≤ u ∧ u < q) (hv : 0 ≤ v ∧ v < q)
    (su : Stress d a b c u) (sv : Stress d a b c v) : u = v := by
  rcases su with su | su <;> rcases sv with sv | sv <;> omega

/-- In the finite-phase regime a rectangle is determined by its first row
    and column, for arbitrary positive or zero side lengths. -/
theorem boundary_unique {q d : Int} {h w : Nat} (small : q ≤ 2*d)
    (f g : Nat → Nat → Int)
    (fb : ∀ i ≤ h, ∀ j ≤ w, 0 ≤ f i j ∧ f i j < q)
    (gb : ∀ i ≤ h, ∀ j ≤ w, 0 ≤ g i j ∧ g i j < q)
    (fl : ∀ i < h, ∀ j < w, Stress d (f i j) (f i (j+1)) (f (i+1) j) (f (i+1) (j+1)))
    (gl : ∀ i < h, ∀ j < w, Stress d (g i j) (g i (j+1)) (g (i+1) j) (g (i+1) (j+1)))
    (top : ∀ j ≤ w, f 0 j = g 0 j)
    (left : ∀ i ≤ h, f i 0 = g i 0) :
    ∀ i ≤ h, ∀ j ≤ w, f i j = g i j := by
  intro i
  induction i with
  | zero => exact fun _ => top
  | succ i rows =>
    intro hi j
    induction j with
    | zero => exact fun _ => left (i+1) hi
    | succ j cols =>
      intro hj
      have hf := fl i (by omega) j (by omega)
      rw [rows (by omega) j (by omega), rows (by omega) (j+1) hj, cols (by omega)] at hf
      exact corner_unique small (fb (i+1) hi (j+1) hj) (gb (i+1) hi (j+1) hj)
        hf (gl i (by omega) j (by omega))

#print axioms boundary_unique

end Hardin
