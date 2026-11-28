import Product

namespace WythoffProduct
open goldenRatio

def add (u v : Point) : Point := (u.1+v.1,u.2+v.2)
def fibPoint (i : ℕ) : Point := (Nat.fib (i+1),Nat.fib i)
def weight : List ℕ → Point | [] => (0,0) | i::is => add (fibPoint i) (weight is)

/-- Indices of the ones in a finite word, least significant digit first, starting at F₂. -/
def indices : List Bool → List ℕ
  | [] => []
  | false::ds => (indices ds).map (·+1)
  | true::ds => 2::(indices ds).map (·+1)

theorem fib_shift (i : ℕ) : fibPoint (i+1)=shift (fibPoint i) := by
  apply Prod.ext
  · change (Nat.fib (i+2):ℤ)=Nat.fib (i+1)+Nat.fib i
    rw [Nat.fib_add_two,Nat.cast_add]; ring
  · rfl

theorem fib_mul (i j : ℕ) : mul (fibPoint i) (fibPoint j)=fibPoint (i+j) := by
  induction i with
  | zero => simp [fibPoint,mul]
  | succ i ih => rw [fib_shift,mul_shift_left,ih,Nat.succ_add,fib_shift]

private theorem add_shift (u v : Point) : add (shift u) (shift v)=shift (add u v) := by ext <;> simp [add,shift]; ring
private theorem shifted_weight (l : List ℕ) : weight (l.map (·+1))=shift (weight l) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons,weight,fib_shift,ih,add_shift]

private theorem internal_add (u v : Point) : internal (add u v)=internal u+internal v := by simp [internal,add]; ring

noncomputable def tailValue : List Bool → ℝ
  | [] => 0
  | d::ds => d.toNat-beta*tailValue ds

private theorem tail_bounds (ds : List Bool) : -1<tailValue ds ∧ tailValue ds<φ := by
  induction ds with
  | nil => simpa [tailValue] using gold_pos
  | cons d ds ih =>
    have l := mul_lt_mul_of_pos_left ih.1 beta_pos
    have u := mul_lt_mul_of_pos_left ih.2 beta_pos
    cases d <;> simp only [tailValue,Bool.toNat_false,Bool.toNat_true,Nat.cast_zero,Nat.cast_one] <;>
      constructor <;> linarith [beta_phi,phi_eq]

private theorem digit_internal (ds : List Bool) : internal (weight (indices ds))=beta^2*tailValue ds := by
  induction ds with
  | nil => simp [indices,weight,internal,tailValue]
  | cons d ds ih =>
    cases d with
    | false => simp only [indices,shifted_weight,internal_shift,ih,tailValue,Bool.toNat_false,Nat.cast_zero]; ring
    | true =>
      simp only [indices,weight,shifted_weight,internal_add,internal_shift,ih,tailValue,Bool.toNat_true,Nat.cast_one]
      have u : internal (fibPoint 2)=beta^2 := by
        norm_num [internal,fibPoint,Nat.fib]; linarith [beta_sq,phi_eq]
      rw [u]; ring

theorem digit_lift (ds : List Bool) : lift (weight (indices ds)).2=weight (indices ds) := by
  apply lift_unique
  have l := mul_lt_mul_of_pos_left (tail_bounds ds).1 (sq_pos_of_pos beta_pos)
  have u := mul_lt_mul_of_pos_left (tail_bounds ds).2 (sq_pos_of_pos beta_pos)
  have bp : beta^2*φ=beta := by linear_combination beta*beta_phi
  unfold canonical; rw [digit_internal]
  constructor <;> linarith

private theorem mul_add_left (u v w : Point) : mul (add u v) w=add (mul u w) (mul v w) := by ext <;> simp [add,mul] <;> ring
private theorem mul_add_right (u v w : Point) : mul u (add v w)=add (mul u v) (mul u w) := by ext <;> simp [add,mul] <;> ring

def doubleSum (l m : List ℕ) : ℕ := (l.map (fun i => (m.map (fun j => Nat.fib (i+j))).sum)).sum

private theorem mul_weight (l m : List ℕ) : (mul (weight l) (weight m)).2=(doubleSum l m:ℤ) := by
  have one (i : ℕ) : (mul (fibPoint i) (weight m)).2=↑(m.map (fun j => Nat.fib (i+j))).sum := by
    induction m with
    | nil => simp [weight,mul]
    | cons j m ih =>
      rw [weight,mul_add_right,fib_mul]
      change (Nat.fib (i+j):ℤ)+(mul (fibPoint i) (weight m)).2=_
      rw [ih]; simp
  induction l with
  | nil => simp [weight,mul,doubleSum]
  | cons i l ih =>
    rw [weight,mul_add_left]
    change (mul (fibPoint i) (weight m)).2+(mul (weight l) (weight m)).2=_
    rw [one,ih]; simp [doubleSum]

private theorem second_weight (l : List ℕ) : (weight l).2=↑(l.map Nat.fib).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [weight,add,fibPoint,ih]

/-- The original double Fibonacci sum equals the floor formula on every pair of finite binary words.
This includes all Zeckendorf expansions, and allows even adjacent one-digits. -/
theorem knuth_double_sum (ds es : List Bool) :
    circle (↑((indices ds).map Nat.fib).sum) (↑((indices es).map Nat.fib).sum)=doubleSum (indices ds) (indices es) := by
  rw [← second_weight,← second_weight]
  have nonneg (l : List ℕ) : 0≤(weight l).2 := by rw [second_weight]; positivity
  have h := mul_lift _ _ (nonneg (indices ds)) (nonneg (indices es))
  rw [digit_lift,digit_lift] at h
  have k := congrArg Prod.snd h
  simpa only [mul_weight,lift] using k.symm

#print axioms knuth_double_sum
end WythoffProduct
