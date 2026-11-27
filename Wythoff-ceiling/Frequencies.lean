import Counts

namespace CeilingArray
open goldenRatio Filter Topology

noncomputable def rate (t : Statistic) : ℝ := (φ ^ (10-t.offset))⁻¹

theorem rate_pos (t : Statistic) : 0 < rate t := inv_pos.mpr (pow_pos gold_pos _)

theorem rate_le_one (t : Statistic) : rate t ≤ 1 := by
  exact inv_le_one_of_one_le₀ (one_le_pow₀ one_lt_gold.le)

private theorem fib_reference (t : Statistic) (k : ℕ) :
    |(Nat.fib (k+t.offset) : ℝ) - rate t * Nat.fib (k+10)| ≤ 2 := by
  let m := k+t.offset
  let d := 10-t.offset
  have index : k+10 = m+d := by cases t <;> simp [m,d,Statistic.offset]
  have phi_cancel : rate t * φ ^ (m+d) = φ ^ m := by
    rw [pow_add]
    change (φ^d)⁻¹ * (φ^m * φ^d) = φ^m
    rw [mul_left_comm, inv_mul_cancel₀ (pow_ne_zero _ gold_ne_zero), mul_one]
  have small (j : ℕ) : |goldenConj ^ j| ≤ 1 := by
    rw [abs_pow]; apply pow_le_one₀ (abs_nonneg _)
    rw [abs_of_neg goldConj_neg]
    linarith [gold_add_goldConj,gold_lt_two]
  have e : (Nat.fib m : ℝ) - rate t * Nat.fib (m+d) =
      (rate t * goldenConj^(m+d)-goldenConj^m)/Real.sqrt 5 := by
    rw [Real.coe_fib_eq,Real.coe_fib_eq]
    simp only [div_eq_mul_inv]
    linear_combination -(Real.sqrt 5)⁻¹ * phi_cancel
  change |(Nat.fib m : ℝ)-rate t*Nat.fib (k+10)| ≤ 2
  rw [index,e,abs_div,abs_of_pos (Real.sqrt_pos.mpr (by norm_num))]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
  have a := abs_sub (rate t * goldenConj^(m+d)) (goldenConj^m)
  rw [abs_mul,abs_of_pos (rate_pos t)] at a
  have c := mul_le_mul_of_nonneg_left (small (m+d)) (rate_pos t).le
  have rt : (1:ℝ) ≤ Real.sqrt 5 := by norm_num
  linarith [small m,rate_le_one t]

theorem word_length (b : Kind) (k : ℕ) (s : State) : (word b k s).length = Nat.fib (k+2) := by
  induction k using Nat.twoStepInduction generalizing s with
  | zero => rfl
  | one => rfl
  | more k a c => rw [word,List.length_append,c,a,Nat.fib_add_two (n := k+2),Nat.add_comm]

private theorem boundary_le (t : Statistic) (a b : Summary) : boundary t a b ≤ 1 := by
  cases a <;> cases b <;> simp [boundary]
  split <;> decide

private theorem crude (t : Statistic) (w : List Bool) : (measure t w).count ≤ 2*w.length := by
  induction w with
  | nil => exact Nat.le_refl 0
  | cons x w ih =>
    have b := boundary_le t (unitMeasure t x).shape (measure t w).shape
    have c : (unitMeasure t x).count ≤ 1 := by simp [unitMeasure]; split <;> decide
    change (unitMeasure t x).count + (measure t w).count + _ ≤ _
    rw [List.length_cons]; omega

theorem full_error (b : Kind) (t : Statistic) (k : ℕ) (s : State) :
    |(total b t k s : ℝ)-rate t*Nat.fib (k+2)| ≤ (k:ℝ)+100 := by
  by_cases h : 8 ≤ k
  · obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm 8 i]
    have a := residual_bound b t i s
    unfold residual at a
    have ar : |(total b t (i+8) s : ℝ) - Nat.fib (i+t.offset)| ≤ (i:ℝ)+6 := by exact_mod_cast a
    have br := fib_reference t i
    have tri := abs_sub_le (total b t (i+8) s : ℝ) (Nat.fib (i+t.offset)) (rate t*Nat.fib (i+10))
    push_cast
    linarith
  · have f : Nat.fib (k+2) ≤ 34 := Nat.fib_mono (show k+2≤9 by omega)
    have c := crude t (word b k s)
    rw [measure_word,word_length] at c
    change total b t k s ≤ 2*Nat.fib (k+2) at c
    have cr : (total b t k s : ℝ) ≤ 68 := by exact_mod_cast (show total b t k s ≤ 68 by omega)
    have fr : (Nat.fib (k+2):ℝ) ≤ 34 := by exact_mod_cast f
    have z := mul_nonneg (rate_pos t).le (Nat.cast_nonneg (Nat.fib (k+2)) : (0:ℝ)≤_)
    have le := mul_le_mul_of_nonneg_right (rate_le_one t) (Nat.cast_nonneg (Nat.fib (k+2)) : (0:ℝ)≤_)
    rw [abs_le]; constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) k, Nat.cast_nonneg (α:=ℝ) (total b t k s)]

private theorem tiny_prefix (b : Kind) (t : Statistic) (k n : ℕ) (s : State)
    (tiny : k≤1) (hn : n≤Nat.fib (k+2)) :
    |((measure t ((word b k s).take n)).count : ℝ) - rate t*n| ≤ ((k:ℝ)+110)^2 := by
  have known : Nat.fib (k+2) ≤ 2 := Nat.fib_mono (show k+2≤3 by omega)
  have c := crude t ((word b k s).take n)
  rw [List.length_take,word_length,min_eq_left hn] at c
  have cr : ((measure t ((word b k s).take n)).count : ℝ) ≤ 4 := by exact_mod_cast (show _ ≤ 4 by omega)
  have nr : (n:ℝ) ≤ 2 := by exact_mod_cast hn.trans known
  have lo := mul_nonneg (rate_pos t).le (Nat.cast_nonneg (α:=ℝ) n)
  have hi := mul_le_mul_of_nonneg_right (rate_le_one t) (Nat.cast_nonneg (α:=ℝ) n)
  rw [abs_le]; constructor <;> nlinarith [Nat.cast_nonneg (α:=ℝ) k,
    Nat.cast_nonneg (α:=ℝ) (measure t ((word b k s).take n)).count]

theorem prefix_error (b : Kind) (t : Statistic) (k : ℕ) (s : State) (n : ℕ) (hn : n ≤ Nat.fib (k+2)) :
    |((measure t ((word b k s).take n)).count : ℝ) - rate t*n| ≤ ((k:ℝ)+110)^2 := by
  induction k using Nat.twoStepInduction generalizing s n with
  | zero => exact tiny_prefix _ _ _ _ _ (by decide) hn
  | one => exact tiny_prefix _ _ _ _ _ (by decide) hn
  | more k a c =>
    let l := word b (k+1) (readZero s)
    let r := word b k (readZero (readOne s))
    have len : l.length = Nat.fib (k+3) := word_length ..
    change |((measure t ((l++r).take n)).count : ℝ) - rate t*n| ≤ _
    by_cases cut : n ≤ l.length
    · rw [List.take_append_of_le_length cut]
      have bound := c (readZero s) n (len ▸ cut)
      change |((measure t (l.take n)).count : ℝ)-_| ≤ _ at bound
      push_cast at bound ⊢
      nlinarith [Nat.cast_nonneg (α:=ℝ) k]
    · let j := n-l.length
      have eq : n = l.length+j := by dsimp [j]; omega
      have jr : j ≤ Nat.fib (k+2) := by
        rw [Nat.fib_add_two (n:=k+2)] at hn
        change n ≤ Nat.fib (k+2) + Nat.fib (k+3) at hn
        omega
      rw [eq,List.take_append,measure_append]
      let left := measure t l
      let right := measure t (r.take j)
      have left_count : left.count = total b t (k+1) (readZero s) := by simp [left,l,measure_word]
      have hb := full_error b t (k+1) (readZero s)
      rw [← left_count, ← len] at hb
      have ha := a (readZero (readOne s)) j jr
      change |(right.count:ℝ) - rate t*j| ≤ _ at ha
      have hc : (boundary t left.shape right.shape : ℝ) ≤ 1 := by exact_mod_cast boundary_le t left.shape right.shape
      have hz := Nat.cast_nonneg (α:=ℝ) (boundary t left.shape right.shape)
      change |(↑(left.count+right.count+boundary t left.shape right.shape):ℝ)-rate t*↑(l.length+j)| ≤ _
      push_cast at hb ⊢; rw [mul_add,abs_le]
      rw [abs_le] at ha hb
      constructor <;> nlinarith [ha.1,ha.2,hb.1,hb.2,Nat.cast_nonneg (α:=ℝ) k]

noncomputable def population (b : Kind) (t : Statistic) (n : ℕ) :=
  (measure t ((List.range n).map (bit b))).count

private theorem cubic (j : ℕ) : (j+24)^3 ≤ Nat.fib (j+25) := by
  induction j using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more j a c =>
    rw [show j+2+25 = (j+25)+2 by omega, Nat.fib_add_two]
    change (j+2+24)^3 ≤ Nat.fib (j+25) + Nat.fib (j+1+25)
    nlinarith [Nat.zero_le (j^3),Nat.zero_le (j^2)]

/-- Densities of hits and of each shared gap, counted within [0,n). -/
theorem population_limit (b : Kind) (t : Statistic) :
    Tendsto (fun n : ℕ => (population b t n : ℝ)/n) atTop (𝓝 (rate t)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨a,ha⟩ := exists_nat_gt (4/ε)
  let K := a+110
  refine ⟨Nat.fib (K+2)+1,?_⟩
  intro n hn
  have poss : ∃ k, n ≤ Nat.fib (k+2) := ⟨n,by have := Nat.le_fib_add_one (n+2); omega⟩
  let k := Nat.find poss
  have width : n ≤ Nat.fib (k+2) := Nat.find_spec poss
  have big : K < k := by
    by_contra! e
    have f := Nat.fib_mono (show k+2≤K+2 by omega)
    omega
  have k110 : 110 ≤ k := by dsimp [K] at big; omega
  have prev := Nat.find_min poss (m := k-1) (show k-1<k by omega)
  change ¬n ≤ Nat.fib (k-1+2) at prev
  rw [show k-1+2=k+1 by omega] at prev
  have cube := cubic (k-24)
  rw [show k-24+24=k by omega,show k-24+25=k+1 by omega] at cube
  have kr : (110:ℝ) ≤ k := by exact_mod_cast k110
  have kpos : (0:ℝ) < k := by linarith
  have large : (k:ℝ)^3 < n := by exact_mod_cast (show k^3 < n by omega)
  have npos : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have bound := prefix_error b t k none n width
  rw [← word_root,← List.map_take,List.take_range,min_eq_left width] at bound
  change |(population b t n : ℝ)-rate t*n| ≤ _ at bound
  have poly : ((k:ℝ)+110)^2 ≤ (2*(k:ℝ))^2 := by gcongr; linarith
  have ak : (a:ℝ) < k := by exact_mod_cast (show a<k by dsimp [K] at big; omega)
  have rat : 4 < ε * (k:ℝ) := by have := (div_lt_iff₀ hε).mp (ha.trans ak); linarith
  have estimate := mul_lt_mul_of_pos_right rat (sq_pos_of_pos kpos)
  have high := mul_lt_mul_of_pos_left large hε
  rw [Real.dist_eq,show (population b t n:ℝ)/n-rate t = ((population b t n:ℝ)-rate t*n)/n by field_simp; ring,
    abs_div, abs_of_pos npos]
  apply (div_lt_iff₀ npos).mpr
  nlinarith [bound.trans poly]

/-- Frequencies per observed hit. Dividing by the number of complete gaps
instead gives the same limit, since a nonempty prefix has one fewer gap. -/
theorem relative_frequency (b : Kind) (t : Statistic) :
    Tendsto (fun n : ℕ => (population b t n : ℝ)/population b .hits n) atTop
      (𝓝 (rate t/rate .hits)) := by
  apply ((population_limit b t).div (population_limit b .hits) (rate_pos .hits).ne').congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  simp only [Pi.div_apply]
  field_simp [show (n:ℝ)≠0 by exact_mod_cast hn.ne']

#print axioms population_limit
#print axioms relative_frequency

end CeilingArray
