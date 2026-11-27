import Automaton

namespace VonNeumann

structure Location where
  positive : Bool
  interior : Bool
  even : Bool
  strip : Bool
  deriving DecidableEq

def location (x y : ℕ) : Location :=
  ⟨decide (0<x+y),decide (0<x ∧ 0<y),decide ((x+y)%2=0),decide (x≤y+2 ∧ y≤x+2)⟩

/-- h is time minus Manhattan radius. No restriction is placed on the unclassified interior. -/
def mask (h : ℤ) (v : Location) : Option Bool :=
  if h<0 then some false else if h≤1 then some true else if h≤3 then some (v.interior && v.even)
  else if v.strip then some (v.positive && v.even) else none

def fits (m : Option Bool) (v : Bool) : Prop := m=none ∨ m=some v
instance (m : Option Bool) (v : Bool) : Decidable (fits m v) := by unfold fits; infer_instance

private def lo (m : Option Bool) := (m.getD false).toNat
private def hi (m : Option Bool) := (m.getD true).toNat

private def weight (f : Option Bool → ℕ) (c e w a b : Option Bool) := f c+2*(f e+f w+f a+f b)

private def safe (v c e w a b : Option Bool) : Bool :=
  match v with
  | none => true
  | some true => decide (1≤weight lo c e w a b ∧ weight hi c e w a b≤5)
  | some false => decide (weight hi c e w a b=0 ∨ 6≤weight lo c e w a b)

private theorem endpoints {m : Option Bool} {v : Bool} (h : fits m v) : lo m≤v.toNat ∧ v.toNat≤hi m := by
  rcases h with rfl|rfl <;> cases v <;> decide

private theorem safe_sound {t c e w a b : Option Bool} {C E W A B : Bool} (h : safe t c e w a b=true)
    (hc : fits c C) (he : fits e E) (hw : fits w W) (ha : fits a A) (hb : fits b B) :
    fits t (output 62 C E W A B) := by
  have rule : output 62 C E W A B=true ↔
      1≤C.toNat+2*(E.toNat+W.toNat+A.toNat+B.toNat) ∧ C.toNat+2*(E.toNat+W.toNat+A.toNat+B.toNat)≤5 := by
    cases C <;> cases E <;> cases W <;> cases A <;> cases B <;> decide
  have l₁ := endpoints hc; have l₂ := endpoints he; have l₃ := endpoints hw
  have l₄ := endpoints ha; have l₅ := endpoints hb
  cases t with
  | none => exact Or.inl rfl
  | some bit =>
    right; congr 1
    cases bit <;> simp only [safe,weight,decide_eq_true_eq] at h
    · exact Bool.eq_false_iff.mpr (fun hit => by have := rule.mp hit; omega) |>.symm
    · exact (rule.mpr (by omega)).symm

private def inward (h : ℤ) (x : ℕ) := if x=0 then h-1 else h+1

private def check (h : ℤ) (x y : ℕ) :=
  safe (mask (h+1) (location x y)) (mask h (location x y))
    (mask (h-1) (location (x+1) y)) (mask (inward h x) (location (back x) y))
    (mask (h-1) (location x (y+1))) (mask (inward h y) (location x (back y)))

private def gapCode (d : ℕ) := if d≤4 then d else 6+d%2
private def timeCode (h : ℤ) := max (-2) (min h 7)

private theorem same_time (h j : ℤ) (lj : -1≤j) (uj : j≤1) (v : Location) :
    mask (h+j) v=mask (timeCode h+j) v := by
  unfold timeCode mask
  split_ifs <;> first | rfl | omega

private theorem neighbours (x d : ℕ) :
    let y := x+d
    let X := min x 7
    let Y := X+gapCode d
    location x y=location X Y ∧ location (x+1) y=location (X+1) Y ∧
    location (back x) y=location (back X) Y ∧ location x (y+1)=location X (Y+1) ∧
    location x (back y)=location X (back Y) ∧ (x=0 ↔ X=0) ∧ (y=0 ↔ Y=0) := by
  have bk (n : ℕ) : back n=if n=0 then 1 else n-1 := by cases n <;> simp [back]
  dsimp only; simp only [bk,location,Location.mk.injEq,decide_eq_decide]
  unfold gapCode
  split_ifs <;> omega

private theorem check_compress (h : ℤ) (x d : ℕ) :
    check h x (x+d)=check (timeCode h) (min x 7) (min x 7+gapCode d) := by
  obtain ⟨c,e,w,a,b,z₁,z₂⟩ := neighbours x d
  have t₀ (v) : mask h v=mask (timeCode h) v := by simpa using same_time h 0 (by decide) (by decide) v
  have t₁ (v) := same_time h 1 (by decide) (by decide) v
  have t₂ (v) : mask (h-1) v=mask (timeCode h-1) v := same_time h (-1) (by decide) (by decide) v
  unfold check inward
  simp only [c,e,w,a,b,z₁,z₂]
  split_ifs <;> rw [t₁,t₀,t₂] <;> simp only [t₂,t₁]

private def checkedPoint (i x y : ℕ) :=
  let h := (i:ℤ)-2
  decide (3≤x+y ∨ 7≤h+x+y) == false || check h x y

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
private theorem certificate : (List.range 10).all (fun i => (List.range 8).all (fun x =>
    (List.range 15).all (checkedPoint i x)))=true := by decide +kernel

private theorem local62 (h : ℤ) (x y : ℕ) (order : x≤y) (t : 7≤h+x+y) : check h x y=true := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le order
  rw [check_compress]
  let H := timeCode h
  let X := min x 7
  let Y := X+gapCode d
  let i := (H+2).toNat
  have lim : -2≤H ∧ H≤7 := by dsimp [H,timeCode]; omega
  have index : (i:ℤ)-2=H := by dsimp [i]; omega
  have il : i<10 := by omega
  have xx : X<8 := by dsimp [X]; omega
  have yy : Y<15 := by dsimp [Y,X,gapCode]; split_ifs <;> omega
  have nonex : 3≤X+Y ∨ 7≤H+X+Y := by
    dsimp [H,X,Y,timeCode,gapCode]
    split_ifs <;> omega
  have result := checked (List.all_eq_true.mp certificate i (List.mem_range.mpr il)) xx yy
  change (decide (3≤X+Y ∨ 7≤(i:ℤ)-2+X+Y) == false || check ((i:ℤ)-2) X Y)=true at result
  simpa [index,nonex] using result

def description (t x y : ℕ) := mask ((t:ℤ)-x-y) (location x y)

private theorem sym_desc (t x y : ℕ) : description t x y=description t y x := by
  have e : (t:ℤ)-x-y=(t:ℤ)-y-x := by omega
  simp only [description,location,e,Nat.add_comm x y,and_comm]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 6000 in
private theorem initial : ∀ x y, fits (description 7 x y) (cell 62 7 x y) := by
  have cert : (List.range 8).all (fun x => (List.range 8).all (fun y =>
      decide (fits (description 7 x y) (cell 62 7 x y))))=true := by decide +kernel
  intro x y
  by_cases small : x<8 ∧ y<8
  · exact of_decide_eq_true (checked cert small.1 small.2)
  · rw [outside 62 7 x y (by omega)]
    have h : (7:ℤ)-x-y<0 := by omega
    simp [description,mask,h,fits]; decide

theorem invariant62 (t : ℕ) (ht : 7≤t) (x y : ℕ) : fits (description t x y) (cell 62 t x y) := by
  induction t,ht using Nat.le_induction generalizing x y with
  | base => exact initial x y
  | succ t ht ih =>
    wlog o : x≤y generalizing x y
    · rw [sym_desc,symmetry]; exact this _ _ (by omega)
    let h : ℤ := (t:ℤ)-x-y
    have p := local62 h x y o (by dsimp [h]; omega)
    have relation (n : ℕ) : (n:ℤ)-(back n:ℕ)=(if n=0 then -1 else 1 : ℤ) := by cases n <;> simp [back]
    have wx : inward h x=(t:ℤ)-(back x:ℕ)-y := by
      have := relation x; dsimp [inward,h]; split_ifs <;> omega
    have wy : inward h y=(t:ℤ)-x-(back y:ℕ) := by
      have := relation y; dsimp [inward,h]; split_ifs <;> omega
    have ex : h-1=(t:ℤ)-(↑(x+1:ℕ):ℤ)-y := by dsimp [h]; omega
    have ey : h-1=(t:ℤ)-x-(↑(y+1:ℕ):ℤ) := by dsimp [h]; omega
    have c : (↑(t+1:ℕ):ℤ)-x-y=h+1 := by dsimp [h]; omega
    unfold description; rw [c]
    apply safe_sound p (ih x y)
    · rw [ex]; exact ih (x+1) y
    · rw [wx]; exact ih (back x) y
    · rw [ey]; exact ih x (y+1)
    · rw [wy]; exact ih x (back y)

#print axioms invariant62

end VonNeumann
