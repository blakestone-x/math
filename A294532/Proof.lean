import Analytic

/-!
# OEIS A294532–A294565: complementary Fibonacci recurrences

Blake Stone, developed with OpenAI Astra 6.2.
-/

open Filter Topology

namespace ComplementaryFibonacci

/-- Coefficients of the zero-based recurrence:
`a(n+2) = a(n+1) + a(n) + p*b(n+1) + q*b(n) + r*n + s`. -/
structure Parameters where
  p : ℤ
  q : ℤ
  r : ℤ
  s : ℤ
  deriving DecidableEq

def Parameters.force (v : Parameters) (n x y : ℕ) : ℤ :=
  v.p * y + v.q * x + v.r * n + v.s

/-- The increasing complementary sequences and their defining recurrence. -/
structure Solution (v : Parameters) (a b : ℕ → ℕ) : Prop where
  a_zero : a 0 = 1
  a_one : a 1 = 2
  b_zero : b 0 = 3
  strict_a : StrictMono a
  strict_b : StrictMono b
  disjoint : ∀ i j, a i ≠ b j
  cover : ∀ m, 0 < m → (∃ i, a i = m) ∨ (∃ j, b j = m)
  recurrence : ∀ n, (a (n + 2) : ℤ) = a (n + 1) + a n + v.force n (b n) (b (n + 1))

lemma Solution.a_lower {v : Parameters} {a b : ℕ → ℕ}
    (h : Solution v a b) (n : ℕ) : n + 1 ≤ a n := by
  simpa [h.a_zero] using h.strict_a.add_le_nat n 0

lemma Solution.b_lower {v : Parameters} {a b : ℕ → ℕ}
    (h : Solution v a b) (n : ℕ) : n + 3 ≤ b n := by
  simpa [h.b_zero] using h.strict_b.add_le_nat n 0

/-- Beyond the initial pair 1,2, adjacent terms of `a` are separated by at least two. -/
lemma Solution.a_gap {v : Parameters} {a b : ℕ → ℕ}
    (h : Solution v a b)
    (he : ∀ n, 0 ≤ v.force n (b n) (b (n + 1))) (n : ℕ) :
    a (n + 1) + 2 ≤ a (n + 2) := by
  cases n with
  | zero =>
    have hs := h.strict_a (show 1 < 2 by omega)
    have hd := h.disjoint 2 0
    change a 1 + 2 ≤ a 2
    simp only [h.a_one, h.b_zero] at *
    omega
  | succ n =>
    have ha := h.a_lower (n + 1)
    have hr := h.recurrence (n + 1)
    have hh := he (n + 1)
    omega

/-- A gap of length three in `b` would place two consecutive integers in `a`. -/
lemma Solution.b_gap {v : Parameters} {a b : ℕ → ℕ}
    (h : Solution v a b)
    (he : ∀ n, 0 ≤ v.force n (b n) (b (n + 1))) (n : ℕ) :
    b (n + 1) ≤ b n + 2 := by
  by_contra hbad
  have hno (m : ℕ) (hm1 : b n < m) (hm2 : m < b (n + 1)) :
      ¬ ∃ j, b j = m := by
    rintro ⟨j, hj⟩
    by_cases hjn : j ≤ n
    · have hs := h.strict_b.monotone hjn
      omega
    · have hs := h.strict_b.monotone (show n + 1 ≤ j by omega)
      omega
  have hfirst := h.cover (b n + 1) (by omega)
  have hsecond := h.cover (b n + 2) (by omega)
  have hn1 : ¬ ∃ j, b j = b n + 1 := hno _ (by omega) (by omega)
  have hn2 : ¬ ∃ j, b j = b n + 2 := hno _ (by omega) (by omega)
  obtain ⟨i, hi⟩ := hfirst.resolve_right hn1
  obtain ⟨j, hj⟩ := hsecond.resolve_right hn2
  have hij : i < j := h.strict_a.lt_iff_lt.mp (by omega)
  have hi0 : 0 < i := by
    have hb := h.b_lower n
    by_contra hh
    have hz : i = 0 := by omega
    simp only [hz, h.a_zero] at hi
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [hk] at hi
  have hgap := h.a_gap he k
  have hle := h.strict_a.monotone (show k + 2 ≤ j by omega)
  simp only [Nat.succ_eq_add_one] at hi
  omega

/-- The complement is at most linear, uniformly over every allowed disturbance. -/
theorem Solution.b_upper {v : Parameters} {a b : ℕ → ℕ}
    (h : Solution v a b)
    (he : ∀ n, 0 ≤ v.force n (b n) (b (n + 1))) (n : ℕ) :
    b n ≤ 2 * n + 3 := by
  induction n with
  | zero => simp [h.b_zero]
  | succ n ih =>
    have hs := h.b_gap he n
    omega


def A294532 : Parameters := ⟨0, 1, 0, 0⟩
def A294533 : Parameters := ⟨0, 1, 0, 1⟩
def A294534 : Parameters := ⟨0, 1, 0, 2⟩
def A294535 : Parameters := ⟨0, 1, 0, 3⟩
def A294536 : Parameters := ⟨0, 1, 0, -1⟩
def A294537 : Parameters := ⟨0, 1, 1, 2⟩
def A294538 : Parameters := ⟨0, 1, 2, 4⟩
def A294539 : Parameters := ⟨0, 1, 1, 1⟩
def A294540 : Parameters := ⟨0, 1, 2, 3⟩
def A294541 : Parameters := ⟨1, 0, 0, 0⟩
def A294542 : Parameters := ⟨1, 0, 0, 1⟩
def A294543 : Parameters := ⟨1, 0, 0, 2⟩
def A294544 : Parameters := ⟨1, 0, 0, 3⟩
def A294545 : Parameters := ⟨1, 0, 0, -1⟩
def A294546 : Parameters := ⟨1, 0, 1, 2⟩
def A294547 : Parameters := ⟨1, 0, 2, 4⟩
def A294548 : Parameters := ⟨1, 0, 1, 1⟩
def A294549 : Parameters := ⟨1, 0, 1, 3⟩
def A294550 : Parameters := ⟨1, 1, 0, 0⟩
def A294551 : Parameters := ⟨1, 1, 0, 1⟩
def A294552 : Parameters := ⟨1, 1, 1, 2⟩
def A294553 : Parameters := ⟨1, 1, -1, -2⟩
def A294554 : Parameters := ⟨1, 1, 0, 2⟩
def A294555 : Parameters := ⟨1, 1, 0, 3⟩
def A294556 : Parameters := ⟨1, 1, 1, 3⟩
def A294557 : Parameters := ⟨1, 1, 1, 1⟩
def A294558 : Parameters := ⟨1, 1, 2, 4⟩
def A294559 : Parameters := ⟨1, 2, 0, 0⟩
def A294560 : Parameters := ⟨2, 2, 0, 0⟩
def A294561 : Parameters := ⟨2, 1, 0, 0⟩
def A294562 : Parameters := ⟨1, -1, 0, 1⟩
def A294563 : Parameters := ⟨1, -1, 1, 2⟩
def A294564 : Parameters := ⟨2, -1, 0, -1⟩
def A294565 : Parameters := ⟨2, -1, 0, -2⟩
def A294565Guide : Parameters := ⟨2, -1, 0, -3⟩

/-- The 34 OEIS title recurrences, plus the guide's distinct final variant. -/
def parameterTable : List Parameters := [
  A294532,
  A294533,
  A294534,
  A294535,
  A294536,
  A294537,
  A294538,
  A294539,
  A294540,
  A294541,
  A294542,
  A294543,
  A294544,
  A294545,
  A294546,
  A294547,
  A294548,
  A294549,
  A294550,
  A294551,
  A294552,
  A294553,
  A294554,
  A294555,
  A294556,
  A294557,
  A294558,
  A294559,
  A294560,
  A294561,
  A294562,
  A294563,
  A294564,
  A294565,
  A294565Guide]

def Supported (v : Parameters) : Prop := v ∈ parameterTable

/-- The signed formulas are positive using only increasing complement values. -/
theorem force_lower {v : Parameters} (hv : Supported v) (n x y : ℕ)
    (hx : n + 3 ≤ x) (hy : x + 1 ≤ y) : 2 ≤ v.force n x y := by
  simp only [Supported, parameterTable, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [Parameters.force, A294532, A294533, A294534, A294535, A294536, A294537, A294538, A294539, A294540, A294541, A294542, A294543, A294544, A294545, A294546, A294547, A294548, A294549, A294550, A294551, A294552, A294553, A294554, A294555, A294556, A294557, A294558, A294559, A294560, A294561, A294562, A294563, A294564, A294565, A294565Guide]
  all_goals omega

/-- Once the complement is linearly bounded, every listed formula has a
uniform linear upper bound. -/
theorem force_upper {v : Parameters} (hv : Supported v) (n x y : ℕ)
    (hx : n + 3 ≤ x) (hy : x + 1 ≤ y)
    (hx' : x ≤ 2 * n + 3) (hy' : y ≤ 2 * n + 5) :
    v.force n x y ≤ 32 * (n + 1) := by
  simp only [Supported, parameterTable, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [Parameters.force, A294532, A294533, A294534, A294535, A294536, A294537, A294538, A294539, A294540, A294541, A294542, A294543, A294544, A294545, A294546, A294547, A294548, A294549, A294550, A294551, A294552, A294553, A294554, A294555, A294556, A294557, A294558, A294559, A294560, A294561, A294562, A294563, A294564, A294565, A294565Guide]
  all_goals omega

/-- The integer formulas produce a nonnegative natural disturbance bounded by
`32*(n+1)`, without any asymptotic hypothesis. -/
lemma Solution.linear_disturbance {v : Parameters} {a b : ℕ → ℕ}
    (h : Solution v a b) (hv : Supported v) :
    ∃ e : ℕ → ℕ,
      (∀ n, a (n + 2) = a (n + 1) + a n + e n) ∧
      (∀ n, e n ≤ 32 * (n + 1)) := by
  have he0 (n : ℕ) : 0 ≤ v.force n (b n) (b (n + 1)) := by
    have hb : b n < b (n + 1) := h.strict_b (by omega)
    have hl := force_lower hv n (b n) (b (n + 1)) (h.b_lower n) (by omega)
    omega
  let e : ℕ → ℕ := fun n => (v.force n (b n) (b (n + 1))).toNat
  have hecast (n : ℕ) : (e n : ℤ) = v.force n (b n) (b (n + 1)) := by
    exact Int.toNat_of_nonneg (he0 n)
  refine ⟨e, ?_, ?_⟩
  · intro n
    have hr : (a (n + 2) : ℤ) = a (n + 1) + a n + (e n : ℤ) := by
      rw [hecast]
      exact h.recurrence n
    exact_mod_cast hr
  · intro n
    have hb : b n < b (n + 1) := h.strict_b (by omega)
    have hby := h.b_upper he0 (n + 1)
    have hu := force_upper hv n (b n) (b (n + 1))
      (h.b_lower n) (by omega) (h.b_upper he0 n) (by omega)
    rw [← hecast] at hu
    exact_mod_cast hu


/-- Every solution of any listed recurrence has the asserted ratio limit.
No convergence or growth assumption is part of `Solution`. -/
theorem solution_ratio_limit {v : Parameters} {a b : ℕ → ℕ}
    (h : Solution v a b) (hv : Supported v) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) := by
  obtain ⟨e, hr, he⟩ := h.linear_disturbance hv
  exact ratio_limit_of_nat_linear_error a e 32
    (by simp [h.a_zero]) (by simp [h.a_one]) hr he

/-- One quantitative estimate valid uniformly across all 34 OEIS entries. -/
theorem solution_ratio_error_bound {v : Parameters} {a b : ℕ → ℕ}
    (h : Solution v a b) (hv : Supported v) (n : ℕ) :
    |(a (n + 1) : ℝ) / a n - phi| ≤ 97 * (n + 1) * (2 / 3 : ℝ) ^ n := by
  obtain ⟨e, hr, he⟩ := h.linear_disturbance hv
  have hb := ratio_error_bound_nat a e 32
    (by simp [h.a_zero]) (by simp [h.a_one]) hr he n
  simp only [h.a_zero, h.a_one, Nat.cast_one, Nat.cast_ofNat, mul_one] at hb
  have hphi : 0 < 2 - phi := by linarith [phi_bounds.2]
  rw [abs_of_pos hphi] at hb
  have hp : 0 < (3 / 2 : ℝ) ^ n := by positivity
  calc
    |(a (n + 1) : ℝ) / a n - phi| ≤
        (3 * 32 + (2 - phi)) * (n + 1) / (3 / 2 : ℝ) ^ n := hb
    _ ≤ 97 * (n + 1) / (3 / 2 : ℝ) ^ n := by
      apply div_le_div_of_nonneg_right _ hp.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [phi_bounds.1]
    _ = 97 * (n + 1) * (2 / 3 : ℝ) ^ n := by
      rw [div_eq_mul_inv, ← inv_pow]
      norm_num

theorem A294532_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294532 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294533_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294533 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294534_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294534 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294535_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294535 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294536_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294536 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294537_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294537 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294538_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294538 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294539_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294539 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294540_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294540 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294541_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294541 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294542_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294542 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294543_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294543 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294544_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294544 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294545_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294545 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294546_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294546 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294547_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294547 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294548_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294548 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294549_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294549 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294550_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294550 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294551_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294551 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294552_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294552 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294553_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294553 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294554_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294554 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294555_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294555 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294556_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294556 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294557_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294557 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294558_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294558 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294559_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294559 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294560_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294560 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294561_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294561 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294562_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294562 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294563_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294563 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294564_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294564 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294565_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294565 a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

theorem A294565Guide_ratio_limit {a b : ℕ → ℕ}
    (h : Solution A294565Guide a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) :=
  solution_ratio_limit h (by unfold Supported; decide)

#print axioms solution_ratio_limit
#print axioms solution_ratio_error_bound
#print axioms A294532_ratio_limit
#print axioms A294565_ratio_limit
#print axioms A294565Guide_ratio_limit

end ComplementaryFibonacci
