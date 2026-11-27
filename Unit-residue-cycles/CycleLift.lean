import Mathlib.Logic.Function.Iterate

/-! The two abstract steps of the unit-residue lift. The arithmetic input in the
manuscript supplies the full-lap multiplier and the bijections on each fiber. -/
namespace ResidueCycle

variable {I J A B : Type*}

/-- A first-coordinate bijection and bijective maps of its fibers give a bijection. -/
theorem fiberwise_bijective (base : I → A) (fiber : I → J → B)
    (hbase : Function.Bijective base) (hfiber : ∀ i, Function.Bijective (fiber i)) :
    Function.Bijective (fun v : I × J => (base v.1, fiber v.1 v.2)) := by
  constructor
  · rintro ⟨i, y⟩ ⟨j, z⟩ h
    have hij : i = j := hbase.1 (congrArg Prod.fst h)
    subst j
    have hyz : y = z := (hfiber i).1 (congrArg Prod.snd h)
    simp [hyz]
  · rintro ⟨a, b⟩
    obtain ⟨i, hi⟩ := hbase.2 a
    obtain ⟨y, hy⟩ := (hfiber i).2 b
    exact ⟨(i, y), Prod.ext hi hy⟩

/-- If laps are transitive on a chosen fiber and its phase iterates map onto
all fibers, the single lifted orbit visits every point. -/
theorem transitive_lift (T : I × J → I × J) (H : J → J) (a : I) (y₀ : J) (L : ℕ)
    (lap : ∀ y, T^[L] (a, y) = (a, H y))
    (hfull : ∀ y, ∃ k : ℕ, H^[k] y₀ = y)
    (hphase : ∀ i z, ∃ r y, T^[r] (a, y) = (i, z)) :
    ∀ i z, ∃ t : ℕ, T^[t] (a, y₀) = (i, z) := by
  have hlaps (k : ℕ) : T^[k*L] (a, y₀) = (a, H^[k] y₀) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, Nat.add_comm (k*L) L, Function.iterate_add_apply, ih, lap,
          Function.iterate_succ_apply']
  intro i z
  obtain ⟨r, y, hr⟩ := hphase i z
  obtain ⟨k, hk⟩ := hfull y
  exact ⟨r + k*L, by rw [Function.iterate_add_apply, hlaps, hk, hr]⟩

#print axioms fiberwise_bijective
#print axioms transitive_lift
end ResidueCycle
