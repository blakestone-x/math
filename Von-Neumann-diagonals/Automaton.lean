import Mathlib.Tactic

namespace VonNeumann

/-- The neighbour across zero has absolute coordinate one. -/
def back : ℕ → ℕ | 0 => 1 | n+1 => n

def output (rule : ℕ) (c e w a b : Bool) : Bool :=
  rule.testBit (c.toNat+2*(e.toNat+w.toNat+a.toNat+b.toNat))

def update (rule : ℕ) (s : ℕ → ℕ → Bool) (x y : ℕ) :=
  output rule (s x y) (s (x+1) y) (s (back x) y) (s x (y+1)) (s x (back y))

def cell (rule : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0,x,y => decide (x=0 ∧ y=0)
  | t+1,x,y => update rule (cell rule t) x y

def background (rule : ℕ) : ℕ → Bool
  | 0 => false
  | t+1 => let b := background rule t; output rule b b b b b

theorem back_bounds (x : ℕ) : back x≤x+1 ∧ x≤back x+1 := by
  cases x <;> simp [back]
  omega

theorem outside (rule t x y : ℕ) (far : t<x ∨ t<y) : cell rule t x y=background rule t := by
  induction t generalizing x y with
  | zero => simp [cell,background]; omega
  | succ t ih =>
    have bx := back_bounds x; have by' := back_bounds y
    simp only [cell,update,background]
    rw [ih x y (by omega),ih (x+1) y (by omega),ih (back x) y (by omega),
      ih x (y+1) (by omega),ih x (back y) (by omega)]

theorem symmetry (rule t x y : ℕ) : cell rule t x y=cell rule t y x := by
  induction t generalizing x y with
  | zero => simp [cell,and_comm]
  | succ t ih =>
    simp only [cell,update,output]
    conv_lhs => rw [ih x y,ih (x+1) y,ih (back x) y,ih x (y+1),ih x (back y)]
    ac_rfl

def world (rule t : ℕ) (x y : ℤ) := cell rule t x.natAbs y.natAbs

private theorem two_sides (f : ℕ → Bool) (x : ℤ) :
    (f (x+1).natAbs).toNat+(f (x-1).natAbs).toNat =
    (f (x.natAbs+1)).toNat+(f (back x.natAbs)).toNat := by
  cases x with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [show Int.ofNat (n+1)-1=(n:ℤ) by change ((n:ℤ)+1)-1=n; ring]
      rfl
  | negSucc n => cases n <;> exact Nat.add_comm _ _

/-- The quadrant evaluator satisfies the original update on the entire integer lattice. -/
theorem world_step (rule t : ℕ) (x y : ℤ) :
    world rule (t+1) x y =
      output rule (world rule t x y) (world rule t (x+1) y) (world rule t (x-1) y)
        (world rule t x (y+1)) (world rule t x (y-1)) := by
  unfold world
  simp only [cell,update,output]
  have hx := two_sides (fun i => cell rule t i y.natAbs) x
  have hy := two_sides (fun j => cell rule t x.natAbs j) y
  congr 1
  omega

/-- A finite table checked by the kernel can be used at any of its entries. -/
theorem checked {P : ℕ → ℕ → Bool} {k l : ℕ}
    (cert : (List.range k).all (fun i => (List.range l).all (P i))=true)
    {i j : ℕ} (hi : i<k) (hj : j<l) : P i j=true :=
  List.all_eq_true.mp (List.all_eq_true.mp cert i (List.mem_range.mpr hi)) j (List.mem_range.mpr hj)

end VonNeumann
