import Counts

namespace A289004

/-- A289004's independent order-ten integer recurrence.  The source's printed
initial-value prose repeats index 9; its term list and Mathematica program
unambiguously give the value 151 at index 8, used here. -/
def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 11
  | 4 => 18
  | 5 => 31
  | 6 => 52
  | 7 => 89
  | 8 => 151
  | 9 => 257
  | n+10 => 2 * reference (n+9) - reference (n+8) + 2 * reference (n+6) -
      reference (n+5) + reference (n+3) - reference (n+2) - reference n

theorem arithmetic_counterexample : lengthSeq 22 = 268184 ∧ reference 22 = 268182 := by
  norm_num [lengthSeq, state, reference]

theorem arithmetic_earlier_agreement :
    ∀ n : Fin 22, (lengthSeq n : ℤ) = reference n := by
  decide

/-- Every one of the three literal scanners first disagrees with A289004 at
iteration 22, with the source seed called iteration 0. -/
theorem first_failure (v : Variant) :
    (∀ n < 22, ((word v n).length : ℤ) = reference n) ∧
    (word v 22).length = 268184 ∧ reference 22 = 268182 ∧
    ((word v 22).length : ℤ) ≠ reference 22 := by
  refine ⟨?_, ?_, arithmetic_counterexample.2, ?_⟩
  · intro n hn
    rw [(word_counts v n).1]
    exact arithmetic_earlier_agreement ⟨n, hn⟩
  · rw [(word_counts v 22).1]
    exact arithmetic_counterexample.1
  · rw [(word_counts v 22).1, arithmetic_counterexample.1, arithmetic_counterexample.2]
    norm_num

end A289004
