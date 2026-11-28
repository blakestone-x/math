import Mathlib.Order.Filter.Cofinite

namespace GreedyCoverage

/-- A fixed target allowed at arbitrarily late turns must occur in an injective
least-unused sequence. The comparison axiom only concerns this one target. -/
theorem occurs {a : ℕ → ℕ} (ha : Function.Injective a) (m : ℕ) (eligible : ℕ → Prop)
    (hrecur : ∀ B, ∃ n ≥ B, eligible n)
    (hle : (∀ j, a j ≠ m) → ∀ n, eligible n → a (n+1) ≤ m) :
    ∃ j, a j = m := by
  by_contra! absent
  obtain ⟨B, hB⟩ := Filter.tendsto_atTop_atTop.mp ha.nat_tendsto_atTop (m+1)
  obtain ⟨n, hn, he⟩ := hrecur B
  have hlarge := hB (n+1) (by omega)
  have hsmall := hle absent n he
  omega

#print axioms occurs
end GreedyCoverage
