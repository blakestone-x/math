import Lengths
import Limits

/-!
# A289128: exact lengths and nonconvergent position ratios

The scanner is literal, finite words provably nest, and `position b k`
is the one-based position of the k-th b in their unique infinite limit.
The two position-limit assertions are refuted by distinct subsequential limits.
-/

open Filter
open scoped Topology

namespace Kimberling289128

/-- The conjectured A289129 limit is false. -/
theorem A289129_limit_false :
    ¬ Tendsto (fun k => (position false k : ℝ)/(k : ℝ)) atTop (𝓝 (5/2)) :=
  zero_ratio_no_limit (5/2)

/-- The conjectured A289130 limit is false. -/
theorem A289130_limit_false :
    ¬ Tendsto (fun k => (position true k : ℝ)/(k : ℝ)) atTop (𝓝 (5/3)) :=
  one_ratio_no_limit (5/3)

/-- Stronger statement: neither ratio has any real limit. -/
theorem position_ratios_do_not_converge :
    (∀ c : ℝ, ¬ Tendsto (fun k => (position false k : ℝ)/(k : ℝ)) atTop (𝓝 c)) ∧
    (∀ c : ℝ, ¬ Tendsto (fun k => (position true k : ℝ)/(k : ℝ)) atTop (𝓝 c)) :=
  ⟨zero_ratio_no_limit, one_ratio_no_limit⟩

end Kimberling289128

#print axioms Kimberling289128.rewrite_pair
#print axioms Kimberling289128.word_blocks
#print axioms Kimberling289128.word_nested
#print axioms Kimberling289128.bit_stabilizes
#print axioms Kimberling289128.infinite_word_unique
#print axioms Kimberling289128.original_length_conjecture
#print axioms Kimberling289128.position_spec
#print axioms Kimberling289128.zero_even_limit
#print axioms Kimberling289128.zero_odd_limit
#print axioms Kimberling289128.one_even_limit
#print axioms Kimberling289128.one_odd_limit
#print axioms Kimberling289128.A289129_limit_false
#print axioms Kimberling289128.A289130_limit_false
#print axioms Kimberling289128.position_ratios_do_not_converge
