import Cross

namespace VonNeumann

/-- Sum over signed coordinates from -n to n of a function of the absolute coordinate. -/
def line : ℕ → (ℕ → ℕ) → ℕ
  | 0,f => f 0
  | n+1,f => line n f+2*f (n+1)

def square (n : ℕ) (f : ℕ → ℕ → ℕ) := line n (fun x => line n (f x))
def population (rule n : ℕ) := square n (fun x y => (cell rule n x y).toNat)
private def band (a b x : ℕ) : ℕ := (decide (a≤x ∧ x≤b)).toNat

private theorem line_add (n : ℕ) (f g : ℕ → ℕ) :
    line n (fun x => f x+g x)=line n f+line n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [line,ih]; ring

private theorem line_mul (n k : ℕ) (f : ℕ → ℕ) :
    line n (fun x => k*f x)=k*line n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [line,ih]; ring

private theorem line_band (n a b : ℕ) :
    line n (band a b)=if a=0 then 1+2*min n b else 2*(min n b+1-a) := by
  induction n with
  | zero => by_cases az : a=0 <;> simp [line,band,az]; omega
  | succ n ih =>
    rw [line,ih]
    unfold band; split_ifs <;> by_cases hit : a≤n+1 ∧ n+1≤b <;> simp [hit] <;> omega

private theorem total (n : ℕ) : line n (fun _ => 1)=2*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [line,ih]; omega

private theorem rect (n a b c d : ℕ) : square n (fun x y => band a b x*band c d y)=
    line n (band a b)*line n (band c d) := by
  unfold square
  simp only [line_mul]
  simp_rw [mul_comm (band a b _) (line n (band c d))]
  rw [line_mul,mul_comm]

private theorem square_add (n : ℕ) (f g : ℕ → ℕ → ℕ) :
    square n (fun x y => f x y+g x y)=square n f+square n g := by
  unfold square; simp only [line_add]

private theorem bit_nat (P : Prop) [Decidable P] : (decide P).toNat=if P then 1 else 0 := by
  by_cases h : P <;> simp [h]

private theorem even_rect (m x y : ℕ) (hm : 3≤m) :
    (even65 m x y).toNat=band 0 0 x*band 0 m y + band 1 m x*band 0 0 y + band 1 1 x*band 1 1 y := by
  have shape : even65 m x y=decide ((x=0 ∧ y≤m) ∨ (y=0 ∧ x≤m) ∨ (x=1 ∧ y=1)) := by
    simp [even65,evenShape,axis,Bool.or_assoc]
  rw [shape]
  simp only [band,bit_nat]
  split_ifs <;> first | rfl | omega

private theorem odd_rect (m x y : ℕ) (hm : 3≤m) :
    (!(odd65 m x y)).toNat=band 0 0 x*band 0 (m+1) y + band 1 1 x*band 0 m y +
      band 2 m x*band 0 1 y + band (m+1) (m+1) x*band 0 0 y := by
  have shape : (!(odd65 m x y))=decide (((x=0 ∧ y≤m+1) ∨ (y=0 ∧ x≤m+1)) ∨
      (((x=0 ∨ x=1) ∧ y≤m) ∨ ((y=0 ∨ y=1) ∧ x≤m))) := by
    simp [odd65,oddDefects,axis,Bool.or_assoc]
  rw [shape]
  simp only [band,bit_nat]
  split_ifs <;> first | rfl | omega

theorem even_population (rule m : ℕ) (hr : rule=65 ∨ rule=321 ∨ rule=323) (hm : 3≤m) :
    population rule (2*m)=4*m+5 := by
  unfold population; rw [(cross_shapes rule m hr hm).1]
  simp only [even_rect m _ _ hm,square_add,rect]
  simp (disch := omega) [line_band,min_eq_right]; omega

theorem odd_population (rule m : ℕ) (hr : rule=65 ∨ rule=321 ∨ rule=323) (hm : 3≤m) :
    population rule (2*m+1)=4*(2*m+1)^2-2*(2*m+1)+6 := by
  let n:=2*m+1
  have defects : square n (fun x y => (!(odd65 m x y)).toNat)=12*m+1 := by
    simp only [odd_rect m _ _ hm,square_add,rect]
    dsimp [n]
    simp (disch := omega) [line_band,min_eq_right]; omega
  have e : square n (fun x y => (odd65 m x y).toNat)+square n (fun x y => (!(odd65 m x y)).toNat)
      =(2*n+1)^2 := by
    rw [← square_add]
    have v (x y) : (odd65 m x y).toNat+(!(odd65 m x y)).toNat=1 := by cases odd65 m x y <;> decide
    simp only [v,square,total]
    have rec : (fun _ : ℕ => 2*n+1)=(fun _ => (2*n+1)*1) := by funext; simp
    rw [rec,line_mul,total]; ring
  rw [defects] at e
  unfold population; rw [(cross_shapes rule m hr hm).2]
  dsimp [n] at e
  have k : 2*(2*m+1)≤4*(2*m+1)^2 := by nlinarith [sq_nonneg (2*m)]
  zify [k] at *; nlinarith

#print axioms even_population
#print axioms odd_population
end VonNeumann
