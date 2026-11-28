import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Abel

namespace SingularCircles

/-- The last vector in the binary linear construction can avoid both forbidden
sets once the second direction space crosses the first hyperplane. -/
theorem avoid_coset {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (H W : Submodule F V) (hW : W ≠ ⊤) (hcross : ∃ w ∈ W, w ∉ H) (u : V) :
    ∃ x : V, x ∉ H ∧ x-u ∉ W := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : V, y ∉ W := by
    by_contra! all
    exact hW (top_unique (fun v _ => all v))
  obtain ⟨w, hw, hout⟩ := hcross
  by_cases hh : u+y ∈ H
  · refine ⟨u+y+w, ?_, ?_⟩
    · intro h
      exact hout (by simpa using H.sub_mem h hh)
    · intro h
      apply hy
      convert W.sub_mem h hw using 1
      abel
  · exact ⟨u+y, hh, by simpa [add_comm] using hy⟩

/-- Switching two successors in a common label fiber permutes the old labels. -/
theorem switch_labels {V : Type*} [Add V] [DecidableEq V] (L S : V → V)
    (x y : V) (he : L x = L y)
    (hp : Function.Bijective (fun z => L z + S z)) :
    Function.Bijective (fun z => L z + S (Equiv.swap x y z)) := by
  have eqn : (fun z => L z + S (Equiv.swap x y z)) =
      (fun z => L z + S z) ∘ Equiv.swap x y := by
    funext z
    by_cases hx : z=x
    · subst z; simp [he]
    by_cases hy : z=y
    · subst z; simp [he]
    simp [Equiv.swap_apply_of_ne_of_ne hx hy]
  rw [eqn]
  exact hp.comp (Equiv.swap x y).bijective

#print axioms avoid_coset
#print axioms switch_labels
end SingularCircles
