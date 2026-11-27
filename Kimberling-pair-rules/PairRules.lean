import Mathlib.Tactic.Ring

/-! Literal nonoverlapping replacement, the return tiles, and both length theorems. -/
namespace PairRules

inductive Rule | middle | zeros deriving DecidableEq
inductive Letter | a | b | c deriving DecidableEq
inductive Phase | p0 | p1 | p2 | p3 | p4 | p5 deriving DecidableEq
open Letter Phase

def oneImage : Rule → List Bool
  | .middle => [false,true,false]
  | .zeros => [false,false,false]

def scan (m : Rule) : List Bool → List Bool
  | [] => []
  | true :: xs => oneImage m ++ scan m xs
  | false :: false :: xs => [false,false,true] ++ scan m xs
  | false :: true :: xs => false :: (oneImage m ++ scan m xs)
  | [false] => [false]

def word (m : Rule) : Nat → List Bool
  | 0 => [false,false]
  | n+1 => scan m (word m n)

def next : Phase → Phase
  | p0 => p1 | p1 => p2 | p2 => p3 | p3 => p4 | p4 => p5 | p5 => p0

def size : Rule → Letter → Nat
  | .middle, a => 1 | .middle, b => 2 | .middle, c => 3
  | .zeros, a => 2 | .zeros, b => 5 | .zeros, c => 6

def sub : Rule → Letter → List Letter
  | .middle, a => [c] | .middle, b => [c,a] | .middle, c => [c,b]
  | .zeros, a => [b] | .zeros, b => [a,c] | .zeros, c => [a,a,b]

def lead : Rule → Letter | .middle => a | .zeros => b
def z (k : Nat) := List.replicate k false
def pad (m : Rule) := z (size m (lead m))
def tile (m : Rule) (x : Letter) := true :: z (size m x)
def tiles (m : Rule) (v : List Letter) := v.flatMap (tile m)

def tailRest : Rule → Phase → List Bool
  | .middle, p0 | .middle, p3 => z 0
  | .middle, p1 | .middle, p4 => z 1
  | .middle, p2 | .middle, p5 => z 2
  | .zeros, p0 => z 5 ++ true :: (z 2 ++ true :: z 5)
  | .zeros, p1 => z 5 ++ true :: (z 2 ++ true :: z 1)
  | .zeros, p2 => z 2 ++ true :: (z 6 ++ true :: z 4)
  | .zeros, p3 => z 5 ++ true :: (z 2 ++ true :: z 0)
  | .zeros, p4 => z 2 ++ true :: (z 6 ++ true :: z 3)
  | .zeros, p5 => z 2 ++ true :: (z 5 ++ true :: z 1)

def tail (m : Rule) (p : Phase) := true :: tailRest m p

def extra : Rule → Phase → List Letter
  | .middle, p2 | .middle, p5 => [c]
  | .zeros, p0 => [a,c]
  | .zeros, p2 => [b,a,a]
  | .zeros, p4 => [b,a]
  | _, _ => []

theorem tile_boundary (m : Rule) (x : Letter) (u : List Bool) :
    scan m (tile m x ++ true :: u) = scan m (tile m x) ++ scan m (true :: u) := by
  cases m <;> cases x <;> rfl

theorem tile_substitution (m : Rule) (x : Letter) :
    scan m (tile m x) ++ pad m = pad m ++ tiles m (sub m x) := by
  cases m <;> cases x <;> decide

theorem tail_transition (m : Rule) (p : Phase) :
    scan m (tail m p) = pad m ++ (tiles m (extra m p) ++ tail m (next p)) := by
  cases m <;> cases p <;> decide

private theorem starts (m : Rule) (v : List Letter) (p : Phase) :
    ∃ u, tiles m v ++ tail m p = true :: u := by
  cases v with
  | nil => exact ⟨_, rfl⟩
  | cons x xs => exact ⟨_, rfl⟩

private theorem middle_scan (m : Rule) (p : Phase) (v : List Letter) :
    scan m (tiles m v ++ tail m p) =
      pad m ++ (tiles m (v.flatMap (sub m)) ++ (tiles m (extra m p) ++ tail m (next p))) := by
  induction v with
  | nil => exact tail_transition m p
  | cons x xs ih =>
    obtain ⟨u, hu⟩ := starts m xs p
    have h : scan m (tile m x ++ (tiles m xs ++ tail m p)) =
        scan m (tile m x) ++ scan m (tiles m xs ++ tail m p) := by
      rw [hu]; exact tile_boundary m x u
    simp only [tiles, List.flatMap_cons, List.flatMap_append, List.append_assoc]
    change scan m (tile m x ++ (tiles m xs ++ tail m p)) = _
    rw [h, ih]
    have hx := tile_substitution m x
    simp only [tiles] at hx
    simpa only [List.append_assoc] using congrArg
      (fun t => t ++ (tiles m (xs.flatMap (sub m)) ++ (tiles m (extra m p) ++ tail m (next p)))) hx

def encode (m : Rule) (p : Phase) (v : List Letter) := false :: false :: (tiles m v ++ tail m p)

def expand (m : Rule) (p : Phase) (v : List Letter) :=
  lead m :: (v.flatMap (sub m) ++ extra m p)

theorem literal_step (m : Rule) (p : Phase) (v : List Letter) :
    scan m (encode m p v) = encode m (next p) (expand m p v) := by
  change false :: false :: true :: scan m (tiles m v ++ tail m p) = _
  rw [middle_scan]
  simp [encode, expand, tiles, tile, pad, List.append_assoc]

structure Counts where
  na : Int
  nb : Int
  nc : Int
  deriving DecidableEq

def zero : Counts := ⟨0,0,0⟩
def plus (x y : Counts) : Counts := ⟨x.na+y.na,x.nb+y.nb,x.nc+y.nc⟩
def unit : Letter → Counts | a => ⟨1,0,0⟩ | b => ⟨0,1,0⟩ | c => ⟨0,0,1⟩
def tally : List Letter → Counts
  | [] => zero
  | x::xs => plus (unit x) (tally xs)

def matrix : Rule → Counts → Counts
  | .middle, x => ⟨x.nb,x.nc,x.na+x.nb+x.nc⟩
  | .zeros, x => ⟨x.nb+2*x.nc,x.na+x.nc,x.nb⟩

theorem tally_append (v w : List Letter) :
    tally (v ++ w) = plus (tally v) (tally w) := by
  induction v with
  | nil => simp [tally, plus, zero]
  | cons x xs ih =>
    simp [tally, ih, plus, Int.add_assoc]

theorem tally_sub (m : Rule) (v : List Letter) :
    tally (v.flatMap (sub m)) = matrix m (tally v) := by
  induction v with
  | nil => cases m <;> rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, tally_append, ih, tally]
    cases m <;> cases x <;> simp [sub,tally,matrix,plus,unit,zero] <;> omega

def weighted : Rule → Counts → Int
  | .middle, x => 2*x.na+3*x.nb+4*x.nc
  | .zeros, x => 3*x.na+6*x.nb+7*x.nc

theorem tiles_length (m : Rule) (v : List Letter) :
    ((tiles m v).length : Int) = weighted m (tally v) := by
  induction v with
  | nil => cases m <;> rfl
  | cons x xs ih =>
    change (((tile m x ++ tiles m xs).length : Nat) : Int) = _
    rw [List.length_append, Nat.cast_add, ih]
    cases m <;> cases x <;> simp [tile,z,size,weighted,tally,plus,unit] <;> omega

structure Model where
  phase : Phase
  counts : Counts

def step (m : Rule) (s : Model) : Model :=
  ⟨next s.phase, plus (unit (lead m)) (plus (matrix m s.counts) (tally (extra m s.phase)))⟩

def lengthOf (m : Rule) (s : Model) : Int :=
  2 + weighted m s.counts + (tail m s.phase).length

def walk (m : Rule) : Nat → Model → Model
  | 0, s => s
  | n+1, s => walk m n (step m s)

private theorem tally_step (m : Rule) (p : Phase) (v : List Letter) :
    tally (expand m p v) = (step m ⟨p,tally v⟩).counts := by
  simp [expand,tally,tally_append,tally_sub,step]

theorem actual_length (m : Rule) (n : Nat) (p : Phase) (v : List Letter) :
    (((scan m)^[n] (encode m p v)).length : Int) = lengthOf m (walk m n ⟨p,tally v⟩) := by
  induction n generalizing p v with
  | zero => simp [encode,lengthOf,walk,tiles_length]; omega
  | succ n ih =>
    rw [Function.iterate_succ_apply, literal_step, ih, tally_step]
    rfl

def L (m : Rule) (n : Nat) : Int := (word m n).length

private theorem word_shift (m : Rule) (k n : Nat) :
    word m (n+k) = (scan m)^[k] (word m n) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, word, ih, Function.iterate_succ_apply']

private theorem walk_add (m : Rule) (k n : Nat) (s : Model) :
    walk m (n+k) s = walk m k (walk m n s) := by
  induction n generalizing s with
  | zero => simp [walk]
  | succ n ih => rw [Nat.succ_add,walk,ih]; rfl

private def initial : Model := ⟨p0,zero⟩
def base : Rule → Nat | .middle => 1 | .zeros => 4

private theorem start (m : Rule) : word m (base m) = encode m p0 [] := by
  cases m <;> decide

private theorem from_base (m : Rule) (n : Nat) :
    L m (base m + n) = lengthOf m (walk m n initial) := by
  unfold L
  rw [word_shift, start]
  exact actual_length m n p0 []

def obs (m : Rule) (n : Nat) (s : Model) := lengthOf m (walk m n s)

set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

private theorem middle_identity (s : Model) :
    obs .middle 3 s = obs .middle 2 s + obs .middle 1 s + obs .middle 0 s := by
  rcases s with ⟨p,⟨x,y,z'⟩⟩
  cases p <;> simp [obs,walk,lengthOf,step,weighted,matrix,extra,next,lead,tally,plus,unit,
    zero,tail,tailRest,z] <;> ring

private theorem zeros_identity (s : Model) :
    obs .zeros 7 s = obs .zeros 6 s + 2*obs .zeros 5 s - obs .zeros 4 s -
      obs .zeros 3 s + 2*obs .zeros 2 s - 2*obs .zeros 0 s := by
  rcases s with ⟨p,⟨x,y,z'⟩⟩
  cases p <;> simp [obs,walk,lengthOf,step,weighted,matrix,extra,next,lead,tally,plus,unit,
    zero,tail,tailRest,z] <;> ring

private theorem shifted_obs (m : Rule) (k n : Nat) :
    L m (base m + n + k) = obs m k (walk m n initial) := by
  rw [Nat.add_assoc,from_base,walk_add]; rfl

/-- A285666's actual iterate lengths are A001590(n+4), starting with 2,3,6. -/
theorem tribonacci_length (n : Nat) :
    L .middle (n+3) = L .middle (n+2) + L .middle (n+1) + L .middle n := by
  cases n with
  | zero => decide
  | succ n =>
    have h := middle_identity (walk .middle n initial)
    simp only [← shifted_obs, base, Nat.add_zero, Nat.add_comm 1 n] at h
    exact h

/-- The literal 00→001, 1→000 replacement has the recurrence of A285665. -/
theorem order_seven_length (n : Nat) :
    L .zeros (n+7) = L .zeros (n+6) + 2*L .zeros (n+5) - L .zeros (n+4) -
      L .zeros (n+3) + 2*L .zeros (n+2) - 2*L .zeros n := by
  by_cases hn : n < 4
  · have h : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
    rcases h with h|h|h|h <;> subst n <;> decide
  · obtain ⟨j, rfl⟩ : ∃ j, n = base .zeros + j := ⟨n-4, by simp [base]; omega⟩
    have h := zeros_identity (walk .zeros j initial)
    simp only [← shifted_obs, Nat.add_zero] at h
    exact h

#print axioms tribonacci_length
#print axioms order_seven_length
end PairRules
