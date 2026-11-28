import OMAStatements.S_oeis_a084481
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Max

/-!
# Fault-free L-tetromino tilings of a four-by-even strip

Credit: @blakestone-x (agent: Codex, model: GPT-6)
Sources: https://oeis.org/A084481 and https://oeis.org/A183304

A finite transfer enumerates all translated L-tetrominoes through the
first uncovered cell of each column. We prove its recurrence, reassemble
its paths as exact geometric covers, and identify them bijectively with
the tilings in the statement. The assumed binary-array recurrence then
gives the asserted identity at every n greater than three.
-/

/-
# Direct column enumeration for fault-free 4 x (2n) L-tetromino tilings

At the first unfilled cell, try each translated geometric L that contains the
cell and avoids occupied cells. After filling a column, shift the mask into
the next column. A zero mask at an interior cut is a fault. The positive-square
mask has at most 12 bits while filling, and at most 8 bits after shifting.
-/

namespace ProfileEnumeration

abbrev State := Fin 256
abbrev Shape := List (Nat × Nat)

/-- The eight orientations, in (column,row) coordinates, each translated to
the least column and row zero. -/
def shapes : List Shape :=
  [[(0,0),(0,1),(0,2),(1,0)],[(0,0),(0,1),(0,2),(1,2)],
   [(0,0),(0,1),(1,0),(2,0)],[(0,0),(0,1),(1,1),(2,1)],
   [(0,0),(1,0),(1,1),(1,2)],[(0,0),(1,0),(2,0),(2,1)],
   [(0,1),(1,1),(2,0),(2,1)],[(0,2),(1,0),(1,1),(1,2)]]

/-- All geometric placements whose leftmost column is the current column. -/
def placements : List Nat := shapes.flatMap fun t =>
  ((List.range 4).filter (fun r => t.all (fun c => c.2+r < 4))).map fun r =>
    (t.map (fun c => 2^(4*c.1+c.2+r))).sum

/-- Canonical first-unfilled-cell search. Four placements suffice to fill
a column, since each step fills at least one of its four cells. -/
def fill : Nat → Nat → List State
  | 0, m => if m % 16 = 15 then [Fin.ofNat 256 (m / 16)] else []
  | n+1, m =>
    match (List.range 4).find? (fun r => !m.testBit r) with
    | none => [Fin.ofNat 256 (m / 16)]
    | some r => (placements.filter (fun t => t.testBit r && (m &&& t == 0))).flatMap
        (fun t => fill n (m ||| t))

def next (s : State) : List State := fill 4 s.val

/-- Extend a partial packing across an interior cut; the zero state would
be a fault. The input weight counts completions after the chosen successor. -/
def step (v : State → Nat) (s : State) : Nat :=
  (((next s).filter (fun t => t.val != 0)).map v).sum

def tailWays (s : State) : Nat := (next s).count 0

/-- At n count completions of 2(n+1) columns from the given initial profile. -/
def evenWays : Nat → State → Nat
  | 0 => step tailWays
  | n+1 => step (step (evenWays n))

def tilingCount : Nat → Nat
  | 0 => 1
  | n+1 => evenWays n 0

/-- A recurrence residual can propagate through one column. -/
private theorem sum_linear (v w : State → Nat) (l : List State) :
    (l.map fun i => 2 * v i + w i).sum = 2 * (l.map v).sum + (l.map w).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem step_linear (v w : State → Nat) :
    step (fun s => 2*v s+w s) = fun s => 2*step v s+step w s := by
  funext s
  exact sum_linear v w _

private inductive Code where
  | s0 | s15 | s23 | s29 | s43 | s46 | s51 | s54 | s57 | s71 | s77 | s85 | s99 | s102 | s108 | s139 | s142 | s153 | s170 | s198 | s201 | s204 | s255
  deriving DecidableEq

private def mask : Code → State
  | .s0 => 0
  | .s15 => 15
  | .s23 => 23
  | .s29 => 29
  | .s43 => 43
  | .s46 => 46
  | .s51 => 51
  | .s54 => 54
  | .s57 => 57
  | .s71 => 71
  | .s77 => 77
  | .s85 => 85
  | .s99 => 99
  | .s102 => 102
  | .s108 => 108
  | .s139 => 139
  | .s142 => 142
  | .s153 => 153
  | .s170 => 170
  | .s198 => 198
  | .s201 => 201
  | .s204 => 204
  | .s255 => 255

private def children : Code → List Code
  | .s0 => [.s201, .s15, .s204, .s85, .s153, .s102, .s170, .s15, .s51, .s57]
  | .s15 => []
  | .s23 => [.s201, .s15]
  | .s29 => [.s15, .s99, .s51]
  | .s43 => [.s198, .s102]
  | .s46 => [.s51]
  | .s51 => [.s71, .s139]
  | .s54 => []
  | .s57 => [.s71]
  | .s71 => [.s204]
  | .s77 => [.s102, .s54]
  | .s85 => [.s255]
  | .s99 => [.s142]
  | .s102 => [.s255]
  | .s108 => [.s23]
  | .s139 => [.s204, .s108, .s15]
  | .s142 => [.s15, .s57]
  | .s153 => [.s43, .s77, .s255]
  | .s170 => [.s255]
  | .s198 => []
  | .s201 => [.s46]
  | .s204 => [.s29, .s46]
  | .s255 => [.s15]

private def finish : Code → Nat
  | .s0 => 0
  | .s15 => 1
  | .s23 => 0
  | .s29 => 0
  | .s43 => 0
  | .s46 => 0
  | .s51 => 0
  | .s54 => 0
  | .s57 => 0
  | .s71 => 0
  | .s77 => 0
  | .s85 => 0
  | .s99 => 0
  | .s102 => 0
  | .s108 => 0
  | .s139 => 0
  | .s142 => 0
  | .s153 => 0
  | .s170 => 0
  | .s198 => 0
  | .s201 => 0
  | .s204 => 0
  | .s255 => 0

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
private theorem geometry (s : Code) :
    ((next (mask s)).filter fun t => t.val != 0) = (children s).map mask ∧
    tailWays (mask s) = finish s := by
  cases s <;> decide

private def op (v : Code → Nat) (s : Code) := ((children s).map v).sum

private theorem step_code (v : State → Nat) (w : Code → Nat)
    (h : ∀ s, v (mask s) = w s) (s : Code) : step v (mask s) = op w s := by
  unfold step op
  rw [(geometry s).1, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun i _ => h i)

private def codeWays : Nat → Code → Nat
  | 0 => op finish
  | n+1 => op (op (codeWays n))

private theorem ways_match : ∀ n s, evenWays n (mask s) = codeWays n s := by
  intro n
  induction n with
  | zero => exact step_code _ _ (fun s => (geometry s).2)
  | succ n ih => exact step_code _ _ (step_code _ _ ih)

private theorem op_linear (v w : Code → Nat) :
    op (fun s => 2*v s+w s) = fun s => 2*op v s+op w s := by
  funext s
  unfold op
  generalize children s = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
private theorem seed : codeWays 6 = fun s => 2*codeWays 5 s + codeWays 3 s := by
  funext s
  cases s <;> decide

private theorem lift_rec (n : Nat) :
    codeWays (n+6) = fun s => 2*codeWays (n+5) s+codeWays (n+3) s := by
  induction n with
  | zero => exact seed
  | succ n ih =>
    change op (op (codeWays (n+6))) = fun s =>
      2*op (op (codeWays (n+5))) s+op (op (codeWays (n+3))) s
    rw [ih, op_linear, op_linear]

theorem count_recurrence (k : Nat) :
    tilingCount (k+7) = 2*tilingCount (k+6)+tilingCount (k+4) := by
  change evenWays (k+6) (mask .s0) = 2*evenWays (k+5) (mask .s0)+evenWays (k+3) (mask .s0)
  simp only [ways_match]
  exact congrFun (lift_rec k) .s0

theorem count_initial :
    tilingCount 4 = 18 ∧ tilingCount 5 = 38 ∧ tilingCount 6 = 84 := by
  change evenWays 3 (mask .s0) = 18 ∧ evenWays 4 (mask .s0) = 38 ∧ evenWays 5 (mask .s0) = 84
  simp only [ways_match]
  decide

end ProfileEnumeration

namespace BoardProfiles
open OMA.S_oeis_a084481

private theorem colOptions {n : Nat} {t : Finset (TileCell n)} {c u v : LatticePoint}
    (hi : t.image (fun a => ((a.1.val : ℤ), (a.2.val : ℤ))) =
      {c, (c.1 + u.1,c.2 + u.2), (c.1 + 2*u.1,c.2 + 2*u.2), (c.1 + v.1,c.2 + v.2)})
    {a : TileCell n} (ha : a ∈ t) :
    (a.2.val : ℤ) = c.2 ∨ (a.2.val : ℤ) = c.2 + u.2 ∨
    (a.2.val : ℤ) = c.2 + 2 * u.2 ∨ (a.2.val : ℤ) = c.2 + v.2 := by
  have h := Finset.mem_image_of_mem (fun a : TileCell n => ((a.1.val : ℤ), (a.2.val : ℤ))) ha
  rw [hi] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h
  · exact Or.inl (congrArg Prod.snd h)
  · exact Or.inr (Or.inl (congrArg Prod.snd h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Prod.snd h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Prod.snd h)))

theorem tile_span {n : Nat} {t : Finset (TileCell n)} (ht : isLTile t)
    {a b : TileCell n} (ha : a ∈ t) (hb : b ∈ t) :
    b.2.val ≤ a.2.val + 2 := by
  obtain ⟨c,u,v,hdir,hi⟩ := ht
  have hx := colOptions hi ha
  have hy := colOptions hi hb
  rcases hdir with ⟨⟨_,h | h⟩,hz,_⟩ | ⟨⟨hz,_⟩,_,h | h⟩ <;> omega

end BoardProfiles

/- Turn each geometric tile anchored in column k into the actual 12-bit
placement used by the column enumerator, and conversely. -/
namespace TileDictionary
open OMA.S_oeis_a084481
open ProfileEnumeration (placements)

def world {n : Nat} (a : TileCell n) : LatticePoint := (a.1.val,a.2.val)

def slide (h : ℤ) (a : LatticePoint) : LatticePoint := (a.1,a.2+h)

def offset (h : ℤ) (s : Finset LatticePoint) := s.image (slide h)

def picture {n : Nat} (k : Nat) (t : Finset (TileCell n)) :=
  offset (-(k:ℤ)) (t.image world)

def shape (c u v : LatticePoint) : Finset LatticePoint :=
  {c,(c.1+u.1,c.2+u.2),(c.1+2*u.1,c.2+2*u.2),(c.1+v.1,c.2+v.2)}

theorem offset_shape (h : ℤ) (c u v : LatticePoint) :
    offset h (shape c u v) = shape (slide h c) u v := by
  simp [offset,shape,slide,add_right_comm]

theorem offset_picture {n : Nat} (k : Nat) (t : Finset (TileCell n)) :
    offset k (picture k t) = t.image world := by
  simp [offset,picture,Finset.image_image,Function.comp_def,slide]

def dirs : Fin 8 → LatticePoint × LatticePoint
  | 0 => ((0,1),(1,0))
  | 1 => ((0,1),(-1,0))
  | 2 => ((0,-1),(1,0))
  | 3 => ((0,-1),(-1,0))
  | 4 => ((1,0),(0,1))
  | 5 => ((1,0),(0,-1))
  | 6 => ((-1,0),(0,1))
  | 7 => ((-1,0),(0,-1))

theorem dirs_complete {u v : LatticePoint} (hu : perpendicularUnits u v) :
    ∃ d : Fin 8, dirs d = (u,v) := by
  obtain ⟨u₀,u₁⟩ := u
  obtain ⟨v₀,v₁⟩ := v
  rcases hu with ⟨⟨hu,hu' | hu'⟩,hv,hv' | hv'⟩ | ⟨⟨hu,hu' | hu'⟩,hv,hv' | hv'⟩ <;>
    dsimp at * <;> subst_vars <;>
    first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ |
            exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩ | exact ⟨6,rfl⟩ | exact ⟨7,rfl⟩

theorem dirs_sound (d : Fin 8) : perpendicularUnits (dirs d).1 (dirs d).2 := by
  unfold perpendicularUnits
  revert d
  decide

def pattern (m : Nat) : Finset LatticePoint :=
  ((Finset.univ : Finset (Fin 12)).filter (fun i => m.testBit i.val)).image
    (fun i => ((i.val % 4 : Nat), (i.val / 4 : Nat)))

def good (s : Finset LatticePoint) : Prop :=
  (∀ p ∈ s, 0 ≤ p.1 ∧ p.1 < 4 ∧ 0 ≤ p.2 ∧ p.2 < 3) ∧ ∃ p ∈ s, p.2 = 0

instance (s : Finset LatticePoint) : Decidable (good s) := by
  unfold good
  infer_instance

def localShape (r : Fin 4) (c : Fin 3) (d : Fin 8) :=
  shape (r.val,c.val) (dirs d).1 (dirs d).2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem catalog_complete : ∀ (r : Fin 4) (c : Fin 3) (d : Fin 8),
    good (localShape r c d) → ∃ m ∈ placements, pattern m = localShape r c d := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem catalog_sound : ∀ m ∈ placements,
    good (pattern m) ∧ ∃ (r : Fin 4) (c : Fin 3) (d : Fin 8),
      pattern m = localShape r c d := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem pattern_inj : ∀ m ∈ placements, ∀ l ∈ placements, pattern m = pattern l → m = l := by
  decide

theorem placements_nodup : placements.Nodup := by decide

def anchored {n : Nat} (k : Nat) (t : Finset (TileCell n)) : Prop :=
  (∃ a ∈ t, a.2.val = k) ∧ ∀ a ∈ t, k ≤ a.2.val

theorem mem_picture {n : Nat} {t : Finset (TileCell n)} {k : Nat} {p : LatticePoint} :
    p ∈ picture k t ↔ ∃ a ∈ t, slide (-(k:ℤ)) (world a) = p := by
  simp [picture,offset,Finset.image_image,Function.comp_def]

theorem good_of_anchored {n : Nat} {k : Nat} {t : Finset (TileCell n)}
    (ht : isLTile t) (ha : anchored k t) : good (picture k t) := by
  obtain ⟨⟨a,hat,hak⟩,hlo⟩ := ha
  constructor
  · intro p hp
    obtain ⟨b,hbt,rfl⟩ := mem_picture.mp hp
    have hs := BoardProfiles.tile_span ht hat hbt
    have hl := hlo b hbt
    have hr := b.1.isLt
    simp only [slide,world]
    omega
  · exact ⟨_,mem_picture.mpr ⟨a,hat,rfl⟩, by simp [slide,world,hak]⟩

theorem anchored_of_good {n : Nat} {k : Nat} {t : Finset (TileCell n)}
    (hg : good (picture k t)) : anchored k t := by
  obtain ⟨h, p,hp,hcol⟩ := hg
  obtain ⟨a,hat,rfl⟩ := mem_picture.mp hp
  refine ⟨⟨a,hat,?_⟩,?_⟩
  · simp only [slide,world] at hcol
    omega
  · intro b hb
    have hh := (h _ (mem_picture.mpr ⟨b,hb,rfl⟩)).2.2.1
    simp only [slide,world] at hh
    omega

theorem tile_iff_placement {n : Nat} (k : Nat) (t : Finset (TileCell n)) :
    isLTile t ∧ anchored k t ↔ ∃ m ∈ placements, picture k t = pattern m := by
  constructor
  · rintro ⟨ht,ha⟩
    have hg := good_of_anchored ht ha
    obtain ⟨c,u,v,hu,hi⟩ := ht
    change t.image world = shape c u v at hi
    obtain ⟨d,hd⟩ := dirs_complete hu
    have hc : c ∈ t.image world := by rw [hi]; simp [shape]
    obtain ⟨a,hat,hac⟩ := Finset.mem_image.mp hc
    subst c
    have hpic : picture k t = shape (slide (-(k:ℤ)) (world a)) (dirs d).1 (dirs d).2 := by
      rw [picture,hi,offset_shape,hd]
    have hb := hg.1 _ (mem_picture.mpr ⟨a,hat,rfl⟩)
    simp only [slide,world] at hb
    have hlo := ha.2 a hat
    let c : Fin 3 := ⟨a.2.val-k,by omega⟩
    have he : slide (-(k:ℤ)) (world a) = ((a.1.val:ℤ),(c.val:ℤ)) := by
      apply Prod.ext
      · rfl
      · dsimp [slide,world,c]
        omega
    rw [he] at hpic
    change picture k t = localShape a.1 c d at hpic
    rw [hpic] at hg
    obtain ⟨m,hm,heq⟩ := catalog_complete a.1 c d hg
    exact ⟨m,hm,hpic.trans heq.symm⟩
  · rintro ⟨m,hm,he⟩
    obtain ⟨hg,r,c,d,hs⟩ := catalog_sound m hm
    have hp := he.trans hs
    refine ⟨⟨slide k (r.val,c.val),(dirs d).1,(dirs d).2,dirs_sound d,?_⟩,
      anchored_of_good (he.symm ▸ hg)⟩
    change t.image world = shape _ _ _
    rw [← offset_picture k t,hp,localShape,offset_shape]

end TileDictionary

/- Independent enumeration of unordered sets of pairwise disjoint placements
and an exact, multiplicity-sensitive comparison with the pivot algorithm. -/
namespace ColumnGroups
open ProfileEnumeration

def disjointGroup (g : Finset Nat) : Prop :=
  (∀ a ∈ g, a ∈ placements) ∧ ∀ a ∈ g, ∀ b ∈ g, a ≠ b → a &&& b = 0

instance (g : Finset Nat) : Decidable (disjointGroup g) := by
  unfold disjointGroup
  infer_instance

def groups : List (Finset Nat) :=
  [∅] ++ placements.map (fun a => {a}) ++ placements.flatMap (fun a =>
    (placements.filter (fun b => a < b ∧ a &&& b = 0)).map fun b => {a,b})

set_option maxRecDepth 8000 in
set_option maxHeartbeats 5000000 in
theorem no_three : ∀ a ∈ placements, ∀ b ∈ placements, ∀ c ∈ placements,
    a &&& b = 0 → a &&& c = 0 → b &&& c ≠ 0 := by decide

theorem at_most_two {g : Finset Nat} (hg : disjointGroup g) : g.card ≤ 2 := by
  by_contra! h
  obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩ := Finset.two_lt_card.mp h
  exact no_three a (hg.1 a ha) b (hg.1 b hb) c (hg.1 c hc)
    (hg.2 a ha b hb hab) (hg.2 a ha c hc hac) (hg.2 b hb c hc hbc)

theorem group_sound : ∀ g ∈ groups, disjointGroup g := by decide

theorem groups_nodup : groups.Nodup := by decide

theorem group_complete {g : Finset Nat} (hg : disjointGroup g) : g ∈ groups := by
  have hcard := at_most_two hg
  rcases Nat.eq_zero_or_pos g.card with h | h
  · simp [Finset.card_eq_zero.mp h,groups]
  · by_cases hone : g.card = 1
    · obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hone
      subst g
      have hmem := hg.1 a (Finset.mem_singleton_self _)
      simp only [groups,List.mem_append,List.mem_map]
      exact Or.inl (Or.inr ⟨a,hmem,rfl⟩)
    · have htwo : g.card = 2 := by omega
      obtain ⟨a,b,hab,hg'⟩ := Finset.card_eq_two.mp htwo
      subst g
      have ha : a ∈ ({a,b}:Finset Nat) := by simp
      have hb : b ∈ ({a,b}:Finset Nat) := by simp
      simp only [groups,List.mem_append,List.mem_flatMap,List.mem_map,List.mem_filter,
        decide_eq_true_eq]
      refine Or.inr ?_
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨a,hg.1 a ha,b,⟨hg.1 b hb,h,hg.2 a ha b hb hab⟩,rfl⟩
      · exact ⟨b,hg.1 b hb,a,⟨hg.1 a ha,h,hg.2 b hb a ha hab.symm⟩,Finset.pair_comm _ _⟩

def occupied (g : Finset Nat) := g.sum id

def successor (s : State) (g : Finset Nat) : State :=
  Fin.ofNat 256 ((s.val ||| occupied g) / 16)

def completes (s : State) (g : Finset Nat) : Bool :=
  s.val &&& occupied g == 0 && (s.val ||| occupied g) % 16 == 15

def groupSuccessors (s : State) : List State :=
  ((groups.filter (completes s)).map (successor s))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 25000000 in
theorem transition : ∀ s : State, (next s).Perm (groupSuccessors s) := by decide

end ColumnGroups

/- The numerical one-column transition is precisely the geometric rule:
incoming cells and the new tiles are disjoint, the current column is covered,
and translating the remaining cells left gives the outgoing profile. -/
namespace ColumnSemantics
open ProfileEnumeration (State)
open TileDictionary (pattern offset slide)
open ColumnGroups (groups occupied completes successor)

def raised (s : Finset (ℤ × ℤ)) := offset (-1) (s.filter fun a => 1 ≤ a.2)

noncomputable def blocks (g : Finset Nat) := g.biUnion pattern

set_option maxRecDepth 8000 in
set_option maxHeartbeats 5000000 in
theorem occupied_exact : ∀ g ∈ groups, occupied g < 4096 ∧ pattern (occupied g) = g.biUnion pattern := by
  decide

theorem mem_pattern (m r c : Nat) (hr : r < 4) (hc : c < 3) :
    ((r:ℤ),(c:ℤ)) ∈ pattern m ↔ m.testBit (4*c+r) = true := by
  simp only [pattern,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Prod.mk.injEq,
    Int.ofNat_inj]
  constructor
  · rintro ⟨i,hm,h₁,h₂⟩
    have he : i.val = 4*c+r := by omega
    rwa [← he]
  · intro h
    refine ⟨⟨4*c+r,by omega⟩,h,?_⟩
    dsimp
    omega

theorem coord_of_mem {p : ℤ × ℤ} {m : Nat} (h : p ∈ pattern m) :
    ∃ (r : Fin 4) (c : Fin 3), p = ((r.val:ℤ),(c.val:ℤ)) := by
  simp only [pattern,Finset.mem_image] at h
  obtain ⟨i,_,rfl⟩ := h
  have := i.isLt
  exact ⟨⟨i.val%4,by omega⟩,⟨i.val/4,by omega⟩,rfl⟩

theorem pattern_or (m l : Nat) : pattern (m ||| l) = pattern m ∪ pattern l := by
  ext p
  rw [Finset.mem_union]
  constructor
  · intro h
    obtain ⟨r,c,rfl⟩ := coord_of_mem h
    simpa only [mem_pattern _ _ _ r.isLt c.isLt, Nat.testBit_or, Bool.or_eq_true] using h
  · rintro (h|h) <;> obtain ⟨r,c,rfl⟩ := coord_of_mem h <;>
      simp only [mem_pattern _ _ _ r.isLt c.isLt, Nat.testBit_or, Bool.or_eq_true] at *
    · exact Or.inl h
    · exact Or.inr h

theorem disjoint_iff {m l : Nat} (hm : m < 4096) :
    Disjoint (pattern m) (pattern l) ↔ m &&& l = 0 := by
  constructor
  · intro hd
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and,Nat.zero_testBit]
    by_cases hb : m.testBit i = true
    · have hi : i < 12 := by
        by_contra! hi
        have hm' : m < 2^12 := hm
        have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hm' (Nat.pow_le_pow_right (by decide) hi))
        simp_all
      let r : Fin 4 := ⟨i%4,by omega⟩
      let c : Fin 3 := ⟨i/4,by omega⟩
      have he : 4*c.val+r.val = i := by dsimp [r,c]; omega
      have hpm : ((r.val:ℤ),(c.val:ℤ)) ∈ pattern m :=
        (mem_pattern _ _ _ r.isLt c.isLt).2 (he ▸ hb)
      have hpl := fun hpl => (Finset.disjoint_left.mp hd hpm) ((mem_pattern l _ _ r.isLt c.isLt).2 hpl)
      rw [he] at hpl
      simp_all
    · simp_all
  · intro h
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨r,c,rfl⟩ := coord_of_mem hp
    have hp' := (mem_pattern _ _ _ r.isLt c.isLt).1 hp
    have hq' := (mem_pattern _ _ _ r.isLt c.isLt).1 hq
    have ht : (m &&& l).testBit (4*c.val+r.val) = true := by simp [hp',hq']
    rw [h] at ht
    simp at ht

theorem full_iff (m : Nat) : (∀ r : Fin 4, ((r.val:ℤ),0) ∈ pattern m) ↔ m%16=15 := by
  have htest (r : Fin 4) : ((r.val:ℤ),0) ∈ pattern m ↔ m.testBit r.val = true := by
    simpa using mem_pattern m r.val 0 r.isLt (by decide)
  simp_rw [htest]
  have redu (r : Fin 4) : (m % 16).testBit r.val = m.testBit r.val := by
    change (m % 2^4).testBit _ = _
    rw [Nat.testBit_mod_two_pow]
    simp [r.isLt]
  have all : ∀ q : Fin 16, (∀ r : Fin 4, q.val.testBit r.val = true) ↔ q.val = 15 := by decide
  simpa only [redu] using all ⟨m%16,by omega⟩

private theorem bit_index_bound {m i : Nat} (hm : m < 4096) (hb : m.testBit i = true) :
    i < 12 := by
  by_contra! hi
  have := Nat.testBit_lt_two_pow (lt_of_lt_of_le (show m < 2^12 from hm)
    (Nat.pow_le_pow_right (by decide) hi))
  simp_all

theorem raised_pattern {m : Nat} (hm : m < 4096) :
    pattern (m/16) = raised (pattern m) := by
  ext p
  constructor
  · intro hp
    obtain ⟨r,c,rfl⟩ := coord_of_mem hp
    have hb := (mem_pattern _ _ _ r.isLt c.isLt).mp hp
    change (m / 2^4).testBit (4*c.val+r.val) = true at hb
    rw [Nat.testBit_div_two_pow] at hb
    have hi := bit_index_bound hm hb
    have hr := r.isLt
    have hc : c.val+1 < 3 := by omega
    apply Finset.mem_image.mpr
    refine ⟨((r.val:ℤ),((c.val+1:Nat):ℤ)),Finset.mem_filter.mpr ⟨?_,by simp⟩,?_⟩
    · apply (mem_pattern m r.val (c.val+1) r.isLt hc).2
      simpa [Nat.mul_add,Nat.add_right_comm] using hb
    · simp [slide]
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hmq,hlo⟩ := Finset.mem_filter.mp hq
    obtain ⟨r,c,rfl⟩ := coord_of_mem hmq
    have hb := (mem_pattern _ _ _ r.isLt c.isLt).mp hmq
    dsimp at hlo
    have hc := c.isLt
    have hc' : c.val-1 < 3 := by omega
    have he : slide (-1) ((r.val:ℤ),(c.val:ℤ)) = ((r.val:ℤ),((c.val-1:Nat):ℤ)) := by
      dsimp [slide]
      exact Prod.ext rfl (by omega)
    rw [he]
    apply (mem_pattern _ _ _ r.isLt hc').2
    change (m / 2^4).testBit _ = _
    rw [Nat.testBit_div_two_pow]
    have hf : 4*(c.val-1)+r.val+4 = 4*c.val+r.val := by omega
    rwa [hf]

theorem local_admissibility (s : State) {g : Finset Nat} (hg : g ∈ groups) :
    completes s g = true ↔ Disjoint (pattern s.val) (blocks g) ∧
      ∀ r : Fin 4, ((r.val:ℤ),0) ∈ pattern s.val ∪ blocks g := by
  have h := (occupied_exact g hg).2
  change pattern (occupied g) = blocks g at h
  rw [← h,← pattern_or, full_iff, disjoint_iff (by have := s.isLt; omega)]
  simp [completes]

theorem local_successor (s : State) {g : Finset Nat} (hg : g ∈ groups) :
    pattern (successor s g).val = raised (pattern s.val ∪ blocks g) := by
  obtain ⟨hg12,hp⟩ := occupied_exact g hg
  change pattern (occupied g) = blocks g at hp
  rw [← hp,← pattern_or]
  have hs : s.val < 2^12 := by have := s.isLt; omega
  have hh : (s.val ||| occupied g) < 2^12 := Nat.or_lt_two_pow hs hg12
  have hh' : (s.val ||| occupied g) / 16 < 256 := by omega
  change pattern (((s.val ||| occupied g) / 16) % 256) = _
  rw [Nat.mod_eq_of_lt hh',raised_pattern hh]

end ColumnSemantics

/- The transfer value counts distinct complete sequences of unordered column
groups, with the empty outgoing mask allowed exclusively at the right edge. -/
namespace LabeledPaths
open ColumnGroups ProfileEnumeration

def internal (s : State) :=
  (groups.filter (completes s)).filter (fun g => (successor s g).val != 0)

def terminal (s : State) :=
  (groups.filter (completes s)).filter (fun g => (successor s g).val == 0)

def paths : Nat → State → List (List (Finset Nat))
  | 0,s => (terminal s).map fun g => [g]
  | k+1,s => (internal s).flatMap fun g => (paths k (successor s g)).map (g :: ·)

theorem paths_nodup (k : Nat) : ∀ s, (paths k s).Nodup := by
  induction k with
  | zero =>
    intro s
    exact ((groups_nodup.filter _).filter _).map (fun a b h => (List.cons.inj h).1)
  | succ k ih =>
    intro s
    apply List.nodup_flatMap.mpr
    refine ⟨fun g _ => (ih _).map (fun _ _ h => (List.cons.inj h).2),?_⟩
    have hn : (internal s).Nodup := (groups_nodup.filter _).filter _
    apply hn.imp
    intro a b hab x ha hb
    obtain ⟨u,_,hu⟩ := List.mem_map.mp ha
    obtain ⟨v,_,hv⟩ := List.mem_map.mp hb
    exact hab (List.cons.inj (hu.trans hv.symm)).1

theorem mem_paths_length {k : Nat} {s : State} {p : List (Finset Nat)}
    (hp : p ∈ paths k s) : p.length = k+1 := by
  induction k generalizing s p with
  | zero =>
    obtain ⟨g,_,rfl⟩ := List.mem_map.mp hp
    rfl
  | succ k ih =>
    obtain ⟨g,_,hv⟩ := List.mem_flatMap.mp hp
    obtain ⟨v,hw,rfl⟩ := List.mem_map.mp hv
    simp [ih hw]

theorem internal_step (v : State → Nat) (s : State) :
    step v s = ((internal s).map fun g => v (successor s g)).sum := by
  have he := (transition s).filter (fun t => t.val != 0)
  have hd : (groupSuccessors s).filter (fun t => t.val != 0) =
      (internal s).map (successor s) := by simp [groupSuccessors,internal,List.filter_map,Function.comp_def]
  rw [hd] at he
  simpa [step,List.map_map,Function.comp_def] using (he.map v).sum_eq

theorem terminal_count (s : State) : (terminal s).length = tailWays s := by
  have he := (transition s).filter (fun t => t.val == 0)
  have hd : (groupSuccessors s).filter (fun t => t.val == 0) =
      (terminal s).map (successor s) := by simp [groupSuccessors,terminal,List.filter_map,Function.comp_def]
  rw [hd] at he
  have hlen := he.length_eq.symm
  have rem (l : List State) : (l.filter (fun t => t.val == 0)).length = l.count 0 := by
    induction l with
    | nil => rfl
    | cons t l ih =>
      by_cases hh : t = 0
      · subst t
        simp [ih]
      · have hn : t.val ≠ 0 := fun h => hh (Fin.ext h)
        simp [hh,hn,ih]
  simpa [tailWays,rem] using hlen

theorem length_paths_succ (k : Nat) (s : State) :
    (paths (k+1) s).length = step (fun t => (paths k t).length) s := by
  rw [internal_step]
  simp [paths,List.length_flatMap]

theorem even_path_count (k : Nat) : ∀ s, (paths (2*k+1) s).length = evenWays k s := by
  induction k with
  | zero =>
    intro s
    change (paths 1 s).length = step tailWays s
    rw [length_paths_succ]
    congr 1
    funext t
    simp [paths,terminal_count]
  | succ k ih =>
    intro s
    rw [show 2*(k+1)+1 = (2*k+1)+1+1 by omega,length_paths_succ]
    change _ = step (step (evenWays k)) s
    congr 1
    funext t
    rw [length_paths_succ]
    congr 1
    funext u
    exact ih u

theorem count_distinct_paths (n : Nat) :
    ((paths (2*n+1) 0).toFinset).card = ProfileEnumeration.tilingCount (n+1) := by
  rw [List.toFinset_card_of_nodup (paths_nodup _ _)]
  exact even_path_count n 0

end LabeledPaths

/- Reassembling a path covers a rectangle of exactly the requested width.
No generated tile can spill past the right edge. -/
namespace StripPacking
open OMA.S_oeis_a084481 (LatticePoint)
open ProfileEnumeration (State)
open TileDictionary (pattern offset slide)
open ColumnGroups (groups completes successor disjointGroup)
open ColumnSemantics (blocks raised)
open LabeledPaths (paths internal terminal)

def column : Finset LatticePoint := (Finset.univ : Finset (Fin 4)).image (fun r => ((r.val:ℤ),0))

def strip : Nat → Finset LatticePoint
  | 0 => ∅
  | k+1 => column ∪ offset 1 (strip k)

noncomputable def tilesArea : List (Finset Nat) → Finset LatticePoint
  | [] => ∅
  | g :: gs => blocks g ∪ offset 1 (tilesArea gs)

noncomputable def compatible : List (Finset Nat) → Prop
  | [] => True
  | g :: gs => disjointGroup g ∧ Disjoint (blocks g) (offset 1 (tilesArea gs)) ∧ compatible gs

theorem mem_offset {h : ℤ} {U : Finset LatticePoint} {p : LatticePoint} :
    p ∈ offset h U ↔ slide (-h) p ∈ U := by
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    simpa [slide] using hq
  · intro hp
    exact Finset.mem_image.mpr ⟨_,hp,by simp [slide]⟩

theorem offset_union {h : ℤ} {U V : Finset LatticePoint} :
    offset h (U ∪ V) = offset h U ∪ offset h V := Finset.image_union _ _

theorem offset_disjoint {h : ℤ} {U V : Finset LatticePoint} (hv : Disjoint U V) :
    Disjoint (offset h U) (offset h V) := by
  exact Finset.disjoint_left.mpr (fun _ hp hq => Finset.disjoint_left.mp hv (mem_offset.mp hp) (mem_offset.mp hq))

theorem mem_col {p : LatticePoint} : p ∈ column ↔ 0 ≤ p.1 ∧ p.1 < 4 ∧ p.2 = 0 := by
  constructor
  · intro hp
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hp
    have := r.isLt
    change 0 ≤ (r.val:ℤ) ∧ (r.val:ℤ) < 4 ∧ (0:ℤ) = 0
    exact ⟨Int.natCast_nonneg _, by omega,rfl⟩
  · rintro ⟨hr,hr',hc⟩
    refine Finset.mem_image.mpr ⟨⟨p.1.toNat,by omega⟩,Finset.mem_univ _,?_⟩
    exact Prod.ext (by dsimp; omega) (by simpa using hc.symm)

theorem mem_strip {p : LatticePoint} (w : Nat) :
    p ∈ strip w ↔ 0 ≤ p.1 ∧ p.1 < 4 ∧ 0 ≤ p.2 ∧ p.2 < w := by
  induction w generalizing p with
  | zero => simp [strip]
  | succ w ih =>
    simp only [strip,Finset.mem_union,mem_offset,mem_col,ih,slide]
    omega

theorem strip_join {s : State} {g : Finset Nat} (hg : g ∈ groups) (hc : completes s g = true) :
    pattern s.val ∪ blocks g = column ∪ offset 1 (pattern (successor s g).val) := by
  have hf := ((ColumnSemantics.local_admissibility s hg).mp hc).2
  rw [ColumnSemantics.local_successor s hg]
  ext p
  have hmem : p ∈ offset 1 (raised (pattern s.val ∪ blocks g)) ↔
      p ∈ pattern s.val ∪ blocks g ∧ 1 ≤ p.2 := by
    rw [mem_offset]
    change slide (-1) p ∈ offset (-1) _ ↔ _
    rw [mem_offset,Finset.mem_filter]
    simp [slide]
  rw [show p ∈ column ∪ offset 1 (raised (pattern s.val ∪ blocks g)) ↔
    p ∈ column ∨ p ∈ offset 1 (raised (pattern s.val ∪ blocks g)) from Finset.mem_union]
  rw [hmem,mem_col]
  constructor
  · intro hp
    by_cases h : 1 ≤ p.2
    · exact Or.inr ⟨hp,h⟩
    · have hpic : p ∈ pattern (s.val ||| ColumnGroups.occupied g) := by
        rw [ColumnSemantics.pattern_or,(ColumnSemantics.occupied_exact g hg).2]
        exact hp
      obtain ⟨r,c,rfl⟩ := ColumnSemantics.coord_of_mem hpic
      have := r.isLt
      exact Or.inl ⟨by omega,by omega,by omega⟩
  · rintro (⟨hr,hr',hc⟩ | ⟨hp,_⟩)
    · let r : Fin 4 := ⟨p.1.toNat,by omega⟩
      have hh : ((r.val:ℤ),0) = p := Prod.ext (by dsimp [r]; omega) hc.symm
      exact hh ▸ hf r
    · exact hp

theorem area_nonnegative {gs : List (Finset Nat)} {p : LatticePoint} (hp : p ∈ tilesArea gs) :
    0 ≤ p.2 := by
  induction gs generalizing p with
  | nil => simp [tilesArea] at hp
  | cons g gs ih =>
    obtain hp | hp := Finset.mem_union.mp hp
    · obtain ⟨m,_,hm⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨r,c,rfl⟩ := ColumnSemantics.coord_of_mem hm
      exact Int.natCast_nonneg _
    · have hq := ih (mem_offset.mp hp)
      dsimp [slide] at hq
      omega

private theorem area_disjoint_future {s : State} {g : Finset Nat} {gs : List (Finset Nat)}
    (hg : g ∈ groups) (hc : completes s g = true)
    (ht : Disjoint (pattern (successor s g).val) (tilesArea gs)) :
    Disjoint (pattern s.val ∪ blocks g) (offset 1 (tilesArea gs)) := by
  rw [strip_join hg hc]
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain h | h := Finset.mem_union.mp hp
  · have hzero := (mem_col.mp h).2.2
    have hpos := area_nonnegative (mem_offset.mp hq)
    dsimp [slide] at hpos
    omega
  · exact Finset.disjoint_left.mp (offset_disjoint ht) h hq

theorem step_pack {s : State} {g : Finset Nat} {gs : List (Finset Nat)}
    (hg : g ∈ groups) (hc : completes s g = true)
    (hd : Disjoint (pattern (successor s g).val) (tilesArea gs))
    (he : pattern (successor s g).val ∪ tilesArea gs = strip gs.length)
    (hcompat : compatible gs) :
    Disjoint (pattern s.val) (tilesArea (g::gs)) ∧
      pattern s.val ∪ tilesArea (g::gs) = strip (g::gs).length ∧ compatible (g::gs) := by
  have hj := strip_join hg hc
  have hab := ((ColumnSemantics.local_admissibility s hg).mp hc).1
  have hac := area_disjoint_future hg hc hd
  rw [Finset.disjoint_union_left] at hac
  refine ⟨Finset.disjoint_union_right.mpr ⟨hab,hac.1⟩,?_,ColumnGroups.group_sound g hg,hac.2,hcompat⟩
  change pattern s.val ∪ (blocks g ∪ offset 1 (tilesArea gs)) = column ∪ offset 1 (strip gs.length)
  rw [← Finset.union_assoc,hj,Finset.union_assoc,← offset_union,he]

theorem whole_path {k : Nat} {s : State} {p : List (Finset Nat)} (hp : p ∈ paths k s) :
    Disjoint (pattern s.val) (tilesArea p) ∧ pattern s.val ∪ tilesArea p = strip p.length ∧
    compatible p := by
  induction k generalizing s p with
  | zero =>
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hp
    obtain ⟨hg,hs⟩ := List.mem_filter.mp hg
    obtain ⟨hg,hc⟩ := List.mem_filter.mp hg
    have hz : (successor s g).val = 0 := beq_iff_eq.mp hs
    apply step_pack hg hc
    · simp [tilesArea]
    · rw [hz]
      decide
    · trivial
  | succ k ih =>
    obtain ⟨g,hg,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    obtain ⟨hg,_⟩ := List.mem_filter.mp hg
    obtain ⟨hg,hc⟩ := List.mem_filter.mp hg
    obtain ⟨hd,he,hcompat⟩ := ih hq
    exact step_pack hg hc hd he hcompat

end StripPacking

/- The accepted paths are exactly groupwise geometric packings that cover
the given strip and have a tile crossing every interior cut. -/
namespace StripConverse
open OMA.S_oeis_a084481 (LatticePoint)
open ProfileEnumeration (State)
open TileDictionary (pattern offset slide)
open ColumnGroups (groups completes successor disjointGroup)
open ColumnSemantics (blocks raised)
open LabeledPaths (paths internal terminal)
open StripPacking

def reaches (U : Finset LatticePoint) (j : Nat) : Prop := ∃ p ∈ U, (j:ℤ) ≤ p.2

def hits : List (Finset Nat) → Nat → Prop
  | [],_ => False
  | _::_,0 => False
  | g::gs,j+1 => reaches (blocks g) (j+1) ∨ hits gs j

@[simp] theorem not_hits_zero (gs : List (Finset Nat)) : ¬ hits gs 0 := by cases gs <;> simp [hits]

def noFault (U : Finset LatticePoint) (p : List (Finset Nat)) : Prop :=
  ∀ j, 0 < j → j < p.length → reaches U j ∨ hits p j

theorem reaches_union {U V : Finset LatticePoint} {j : Nat} :
    reaches (U ∪ V) j ↔ reaches U j ∨ reaches V j := by
  simp [reaches,or_and_right,exists_or]

theorem reaches_raised {U : Finset LatticePoint} {j : Nat} :
    reaches (raised U) j ↔ reaches U (j+1) := by
  constructor
  · rintro ⟨p,hp,hj⟩
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨q,(Finset.mem_filter.mp hq).1,?_⟩
    dsimp [slide] at hj
    omega
  · rintro ⟨p,hp,hj⟩
    exact ⟨slide (-1) p,Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,by omega⟩,rfl⟩,
      by dsimp [slide]; omega⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem reaches_zero : ∀ s : State, reaches (pattern s.val) 0 ↔ s.val ≠ 0 := by
  unfold reaches
  decide

theorem noFault_cons {s : State} {g : Finset Nat} {gs : List (Finset Nat)} (hg : g ∈ groups) :
    noFault (pattern s.val) (g::gs) ↔
      (0 < gs.length → (successor s g).val ≠ 0) ∧ noFault (pattern (successor s g).val) gs := by
  have hreach (j : Nat) : reaches (pattern (successor s g).val) j ↔
      reaches (pattern s.val) (j+1) ∨ reaches (blocks g) (j+1) := by
    rw [ColumnSemantics.local_successor s hg,reaches_raised,reaches_union]
  constructor
  · intro hf
    constructor
    · intro hn
      have h := hf 1 (by omega) (by simpa using hn)
      rw [← reaches_zero,hreach]
      simpa [hits] using h
    · intro j hj hlen
      have h := hf (j+1) (by omega) (by simpa using hlen)
      simpa [hits,hreach,or_assoc] using h
  · rintro ⟨hh,hn⟩ j hj hlen
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    cases i with
    | zero =>
      have hz := (reaches_zero _).2 (hh (by simpa using hlen))
      simpa [hits,hreach] using hz
    | succ i =>
      have hz := hn (i+1) (by omega) (by simpa using hlen)
      simpa [hits,hreach,or_assoc] using hz

private theorem step_unpack {s : State} {g : Finset Nat} {gs : List (Finset Nat)}
    (hd : Disjoint (pattern s.val) (tilesArea (g::gs)))
    (he : pattern s.val ∪ tilesArea (g::gs) = strip (g::gs).length)
    (hcomp : compatible (g::gs)) :
    g ∈ groups ∧ completes s g = true ∧ Disjoint (pattern (successor s g).val) (tilesArea gs) ∧
      pattern (successor s g).val ∪ tilesArea gs = strip gs.length ∧ compatible gs := by
  obtain ⟨hgroup,hbt,hct⟩ := hcomp
  have hg := ColumnGroups.group_complete hgroup
  change Disjoint (pattern s.val) (blocks g ∪ offset 1 (tilesArea gs)) at hd
  obtain ⟨hsb,hst⟩ := Finset.disjoint_union_right.mp hd
  change pattern s.val ∪ (blocks g ∪ offset 1 (tilesArea gs)) = column ∪ offset 1 (strip gs.length) at he
  rw [← Finset.union_assoc] at he
  have hc : completes s g = true := by
    apply (ColumnSemantics.local_admissibility s hg).mpr
    refine ⟨hsb,?_⟩
    intro r
    have hh : ((r.val:ℤ),0) ∈ column ∪ offset 1 (strip gs.length) :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩)
    rw [← he] at hh
    obtain h|h := Finset.mem_union.mp hh
    · exact h
    · have hq := area_nonnegative (mem_offset.mp h)
      dsimp [slide] at hq
      omega
  have hj := strip_join hg hc
  have hdis := Finset.disjoint_union_left.mpr ⟨hst,hbt⟩
  rw [hj] at hdis he
  have hds := (Finset.disjoint_union_left.mp hdis).2
  rw [Finset.union_assoc,← offset_union] at he
  have htx (p : LatticePoint) {U : Finset LatticePoint} : slide 1 p ∈ offset 1 U ↔ p ∈ U := by
    rw [mem_offset]
    simp [slide]
  have hnonnegative {p : LatticePoint} (h : p ∈ pattern (successor s g).val ∪ tilesArea gs) : 0 ≤ p.2 := by
    obtain h|h := Finset.mem_union.mp h
    · obtain ⟨r,c,rfl⟩ := ColumnSemantics.coord_of_mem h
      exact Int.natCast_nonneg _
    · exact area_nonnegative h
  refine ⟨hg,hc,Finset.disjoint_left.mpr (fun p hp hq =>
    Finset.disjoint_left.mp hds ((htx p).2 hp) ((htx p).2 hq)),?_,hct⟩
  ext p
  by_cases hzero : p.2 < 0
  · constructor
    · intro hp
      have := hnonnegative hp
      omega
    · intro hp
      have hh := ((mem_strip _).mp hp).2.2.1
      omega
  · have hnot : slide 1 p ∉ column := by rw [mem_col]; dsimp [slide]; omega
    have hh := congrArg (slide 1 p ∈ ·) he
    simpa only [Finset.mem_union,hnot,false_or,htx,eq_iff_iff] using hh

theorem paths_iff {k : Nat} {s : State} {p : List (Finset Nat)} (hlen : p.length = k+1) :
    p ∈ paths k s ↔ Disjoint (pattern s.val) (tilesArea p) ∧
      pattern s.val ∪ tilesArea p = strip p.length ∧ compatible p ∧ noFault (pattern s.val) p := by
  induction k generalizing s p with
  | zero =>
    obtain ⟨g,rfl⟩ := List.length_eq_one_iff.mp hlen
    constructor
    · intro hp
      obtain ⟨hd,he,hc⟩ := whole_path hp
      exact ⟨hd,he,hc,fun j hj hk => by simp at hk; omega⟩
    · rintro ⟨hd,he,hc,_⟩
      obtain ⟨hg,hc,_,ht,_⟩ := step_unpack hd he hc
      have hmask : (successor s g).val = 0 := by
        by_contra hn
        obtain ⟨q,hq,_⟩ := (reaches_zero _).2 hn
        have hempty : pattern (successor s g).val = ∅ := by simpa [tilesArea,strip] using ht
        simp [hempty] at hq
      exact List.mem_map.mpr ⟨g,List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hg,hc⟩,
        beq_iff_eq.mpr hmask⟩,rfl⟩
  | succ k ih =>
    cases p with
    | nil => simp at hlen
    | cons g gs =>
      have hlen' : gs.length = k+1 := by simpa using hlen
      constructor
      · intro hp
        obtain ⟨hd,he,hcompat⟩ := whole_path hp
        obtain ⟨g',hgm,v,hvp,hcons⟩ : ∃ g' ∈ internal s, ∃ v ∈ paths k (successor s g'), g'::v = g::gs := by
          obtain ⟨g',hgm,hres⟩ := List.mem_flatMap.mp hp
          obtain ⟨v,hvp,hcons⟩ := List.mem_map.mp hres
          exact ⟨g',hgm,v,hvp,hcons⟩
        cases hcons
        obtain ⟨hgc,hn⟩ := List.mem_filter.mp hgm
        obtain ⟨hg,_⟩ := List.mem_filter.mp hgc
        exact ⟨hd,he,hcompat,(noFault_cons hg).2 ⟨fun _ => by simpa using hn,
          ((ih hlen').1 hvp).2.2.2⟩⟩
      · rintro ⟨hd,he,hcomp,hf⟩
        obtain ⟨hg,hc,hdt,het,hct⟩ := step_unpack hd he hcomp
        obtain ⟨hn,hft⟩ := (noFault_cons hg).1 hf
        have hgm : g ∈ internal s := List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hg,hc⟩,
          by simpa using hn (by omega)⟩
        exact List.mem_flatMap.mpr ⟨g,hgm,List.mem_map.mpr ⟨gs,(ih hlen').2 ⟨hdt,het,hct,hft⟩,rfl⟩⟩

end StripConverse

/- Finite sets of globally translated tiles are equivalent to lists of
local tile sets indexed by the unique leftmost column. -/
namespace StackIndex
open OMA.S_oeis_a084481 (LatticePoint)
open ProfileEnumeration (placements)
open TileDictionary (pattern offset slide)
open StripPacking

def stamp (k m : Nat) := offset (k:ℤ) (pattern m)

def translated (h : ℤ) (T : Finset (Finset LatticePoint)) := T.image (offset h)

def stack : List (Finset Nat) → Finset (Finset LatticePoint)
  | [] => ∅
  | g::gs => g.image pattern ∪ translated 1 (stack gs)

def listed (p : List (Finset Nat)) : Prop := ∀ g ∈ p, ∀ m ∈ g, m ∈ placements

def supported (w : Nat) (T : Finset (Finset LatticePoint)) : Prop :=
  ∀ t ∈ T, ∃ (k : Fin w) (m : Nat), m ∈ placements ∧ t = stamp k.val m

theorem offset_add (h l : ℤ) (U : Finset LatticePoint) :
    offset h (offset l U) = offset (l+h) U := by
  ext p
  simp [mem_offset,slide,add_assoc,add_comm]

@[simp] theorem offset_zero (U : Finset LatticePoint) : offset 0 U = U := by
  ext p
  simp [mem_offset,slide]

theorem stamp_zero (m : Nat) : stamp 0 m = pattern m := by simp [stamp]

theorem stamp_succ (k m : Nat) : stamp (k+1) m = offset 1 (stamp k m) := by
  simp [stamp,offset_add]

theorem stamp_col {k m : Nat} (hm : m ∈ placements) :
    (∀ p ∈ stamp k m, (k:ℤ) ≤ p.2) ∧ ∃ p ∈ stamp k m, p.2 = k := by
  have hgood := (TileDictionary.catalog_sound m hm).1
  refine ⟨?_,?_⟩
  · intro p hp
    have hn := (hgood.1 _ (mem_offset.mp hp)).2.2.1
    dsimp [slide] at hn
    omega
  · obtain ⟨p,hp,hc⟩ := hgood.2
    refine ⟨slide k p, Finset.mem_image.mpr ⟨p,hp,rfl⟩,?_⟩
    simp [slide,hc]

theorem stamp_unique {k l a b : Nat} (ha : a ∈ placements) (hb : b ∈ placements)
    (he : stamp k a = stamp l b) : k = l ∧ a = b := by
  obtain ⟨hka,pa,hpa,hca⟩ := stamp_col (k:=k) ha
  obtain ⟨hlb,pb,hpb,hcb⟩ := stamp_col (k:=l) hb
  have hkl := hlb pa (he ▸ hpa)
  have hlk := hka pb (he.symm ▸ hpb)
  have h : k = l := by omega
  subst l
  have hi := congrArg (offset (-(k:ℤ))) he
  simp [stamp,offset_add] at hi
  exact ⟨rfl,TileDictionary.pattern_inj a ha b hb hi⟩

theorem mem_stack {p : List (Finset Nat)} {t : Finset LatticePoint} :
    t ∈ stack p ↔ ∃ (k : Fin p.length) (m : Nat), m ∈ p[k.val] ∧ t = stamp k.val m := by
  induction p generalizing t with
  | nil => simp [stack]
  | cons g gs ih =>
    constructor
    · intro h
      obtain h|h := Finset.mem_union.mp h
      · obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp h
        exact ⟨0,m,hm,(stamp_zero m).symm⟩
      · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
        obtain ⟨k,m,hm,rfl⟩ := ih.mp hu
        exact ⟨k.succ,m,hm,(stamp_succ k.val m).symm⟩
    · rintro ⟨k,m,hm,rfl⟩
      refine Fin.cases ?_ (fun j => ?_) k hm
      · intro h
        exact Finset.mem_union_left _ ((stamp_zero m).symm ▸ Finset.mem_image_of_mem pattern h)
      · intro h
        rw [Fin.val_succ,stamp_succ]
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem (offset 1) (ih.mpr ⟨j,m,h,rfl⟩))

theorem stack_supported {p : List (Finset Nat)} (hp : listed p) : supported p.length (stack p) := by
  intro t ht
  obtain ⟨k,m,hm,rfl⟩ := mem_stack.mp ht
  exact ⟨k,m,hp _ (List.getElem_mem k.isLt) m hm,rfl⟩

def decode (w : Nat) (T : Finset (Finset LatticePoint)) : List (Finset Nat) :=
  List.ofFn fun k : Fin w => placements.toFinset.filter (fun m => stamp k.val m ∈ T)

@[simp] theorem decode_length (w : Nat) (T : Finset (Finset LatticePoint)) : (decode w T).length = w := by
  simp [decode]

theorem decode_listed (w : Nat) (T : Finset (Finset LatticePoint)) : listed (decode w T) := by
  intro g hg m hm
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hg
  exact List.mem_toFinset.mp (Finset.mem_filter.mp hm).1

theorem stack_decode {w : Nat} {T : Finset (Finset LatticePoint)} (hs : supported w T) :
    stack (decode w T) = T := by
  ext t
  rw [mem_stack]
  constructor
  · rintro ⟨k,m,hm,rfl⟩
    simp only [decode,List.getElem_ofFn,Finset.mem_filter] at hm
    exact hm.2
  · intro ht
    obtain ⟨k,m,hm,rfl⟩ := hs t ht
    refine ⟨⟨k.val,by simp⟩,m,?_,rfl⟩
    simpa [decode,hm] using ht

theorem decode_stack {p : List (Finset Nat)} (hp : listed p) :
    decode p.length (stack p) = p := by
  apply List.ext_getElem (by simp)
  intro i hi hp'
  ext m
  simp only [decode,List.getElem_ofFn,Finset.mem_filter,List.mem_toFinset]
  constructor
  · rintro ⟨hm,ht⟩
    obtain ⟨k,l,hl,he⟩ := mem_stack.mp ht
    obtain ⟨hic,hmc⟩ := stamp_unique hm (hp _ (List.getElem_mem k.isLt) l hl) he
    simpa [hic,hmc] using hl
  · intro hm
    exact ⟨hp _ (List.getElem_mem hp') _ hm,mem_stack.mpr ⟨⟨i,hp'⟩,m,hm,rfl⟩⟩

end StackIndex

/- The covered cells, overlaps and cut crossings are invariant when
re-indexing tile sets by their leftmost column. -/
namespace StackGeometry
open OMA.S_oeis_a084481 (LatticePoint)
open ProfileEnumeration (placements)
open TileDictionary (pattern offset slide)
open ColumnSemantics (blocks)
open StripPacking StackIndex

def area (T : Finset (Finset LatticePoint)) := T.biUnion id
def packed (T : Finset (Finset LatticePoint)) := ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Disjoint a b

def split (t : Finset LatticePoint) (j : Nat) : Prop :=
  (∃ p ∈ t, p.2 < j) ∧ ∃ p ∈ t, (j:ℤ) ≤ p.2
def crosses (T : Finset (Finset LatticePoint)) (j : Nat) : Prop := ∃ t ∈ T, split t j

theorem area_union {A B : Finset (Finset LatticePoint)} :
    area (A ∪ B) = area A ∪ area B := by ext; simp [area,or_and_right,exists_or]

theorem area_translated (h : ℤ) (T : Finset (Finset LatticePoint)) :
    area (translated h T) = offset h (area T) := by
  ext p
  simp [area,translated,mem_offset]

theorem area_stack (p : List (Finset Nat)) : area (stack p) = tilesArea p := by
  induction p with
  | nil => simp [stack,area,tilesArea]
  | cons g gs ih =>
    rw [stack,area_union,area_translated,ih,tilesArea]
    congr 1
    ext
    simp [area,ColumnSemantics.blocks]

theorem disjoint_area {A B : Finset (Finset LatticePoint)} :
    Disjoint (area A) (area B) ↔ ∀ a ∈ A, ∀ b ∈ B, Disjoint a b := by
  simp [area,Finset.disjoint_left]
  grind

theorem packed_union {A B : Finset (Finset LatticePoint)} (hab : Disjoint A B) :
    packed (A ∪ B) ↔ packed A ∧ packed B ∧ Disjoint (area A) (area B) := by
  rw [disjoint_area]
  unfold packed
  simp only [Finset.mem_union]
  have hdis := Finset.disjoint_left.mp hab
  constructor
  · intro h
    exact ⟨fun a ha b hb => h a (.inl ha) b (.inl hb),
      fun a ha b hb => h a (.inr ha) b (.inr hb),
      fun a ha b hb => h a (.inl ha) b (.inr hb) (fun h' => hdis ha (h' ▸ hb))⟩
  · rintro ⟨hA,hB,hD⟩ a (ha|ha) b (hb|hb) hn
    · exact hA a ha b hb hn
    · exact hD a ha b hb
    · exact (hD b hb a ha).symm
    · exact hB a ha b hb hn

theorem offset_inj (h : ℤ) {A B : Finset LatticePoint} (he : offset h A = offset h B) : A = B := by
  have hi := congrArg (offset (-h)) he
  simpa [offset_add] using hi

theorem packed_translated (h : ℤ) (T : Finset (Finset LatticePoint)) :
    packed (translated h T) ↔ packed T := by
  constructor
  · intro ht a ha b hb hn
    have hh := ht _ (Finset.mem_image_of_mem (offset h) ha) _ (Finset.mem_image_of_mem (offset h) hb)
      (fun he => hn (offset_inj h he))
    apply Finset.disjoint_left.mpr
    intro q hqa hqb
    exact Finset.disjoint_left.mp hh (Finset.mem_image_of_mem (slide h) hqa)
      (Finset.mem_image_of_mem (slide h) hqb)
  · intro ht a ha b hb hn
    obtain ⟨a,ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
    exact offset_disjoint (ht a ha' b hb' (fun he => hn (he ▸ rfl)))

theorem packed_group {g : Finset Nat} (hg : ∀ m ∈ g, m ∈ placements) :
    packed (g.image pattern) ↔ ColumnGroups.disjointGroup g := by
  have hbnd : ∀ m ∈ placements, m < 4096 := by decide
  constructor
  · intro h
    refine ⟨hg,?_⟩
    intro a ha b hb hn
    have hd := h _ (Finset.mem_image_of_mem pattern ha) _ (Finset.mem_image_of_mem pattern hb)
      (fun he => hn (TileDictionary.pattern_inj a (hg a ha) b (hg b hb) he))
    exact (ColumnSemantics.disjoint_iff (hbnd a (hg a ha))).mp hd
  · intro h a ha b hb hn
    obtain ⟨a,ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
    exact (ColumnSemantics.disjoint_iff (hbnd a (hg a ha'))).mpr
      (h.2 a ha' b hb' (fun he => hn (he ▸ rfl)))

theorem listed_cons {g : Finset Nat} {p : List (Finset Nat)} (h : listed (g::p)) :
    (∀ m ∈ g, m ∈ placements) ∧ listed p := by
  exact ⟨h _ (by simp),fun u hu => h u (List.mem_cons_of_mem _ hu)⟩

theorem packed_stack {p : List (Finset Nat)} (hl : listed p) :
    packed (stack p) ↔ compatible p := by
  induction p with
  | nil => simp [stack,packed,compatible]
  | cons g gs ih =>
    obtain ⟨hg,hl⟩ := listed_cons hl
    have hdis : Disjoint (g.image pattern) (translated 1 (stack gs)) := by
      apply Finset.disjoint_left.mpr
      intro t ht hu
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hu
      obtain ⟨k,m,hm,rfl⟩ := mem_stack.mp hu
      rw [← stamp_succ,← stamp_zero a] at he
      have bad := (stamp_unique (hl _ (List.getElem_mem k.isLt) m hm) (hg a ha) he).1
      omega
    change packed (g.image pattern ∪ translated 1 (stack gs)) ↔ _
    rw [packed_union hdis,packed_group hg,packed_translated,ih hl,area_translated,area_stack]
    have he : area (g.image pattern) = blocks g := by ext; simp [area,ColumnSemantics.blocks]
    rw [he]
    simp [compatible,and_comm]

theorem split_stamp_iff {k m j : Nat} (hm : m ∈ placements) :
    split (stamp k m) j ↔ k < j ∧ StripConverse.reaches (stamp k m) j := by
  obtain ⟨hl,p,hp,hc⟩ := stamp_col (k:=k) hm
  refine and_congr_left (fun _ => ?_)
  constructor
  · rintro ⟨q,hq,h⟩
    have := hl q hq
    omega
  · exact fun h => ⟨p,hp,by omega⟩

theorem split_succ {t : Finset LatticePoint} (j : Nat) :
    split (offset 1 t) (j+1) ↔ split t j := by
  constructor
  · rintro ⟨⟨p,hp,hpc⟩,q,hq,hqc⟩
    exact ⟨⟨_,mem_offset.mp hp,by dsimp [slide]; omega⟩,_,mem_offset.mp hq,by dsimp [slide]; omega⟩
  · rintro ⟨⟨p,hp,hpc⟩,q,hq,hqc⟩
    exact ⟨⟨_,Finset.mem_image_of_mem (slide 1) hp,by dsimp [slide]; omega⟩,
      _,Finset.mem_image_of_mem (slide 1) hq,by dsimp [slide]; omega⟩

theorem crosses_stack {p : List (Finset Nat)} (hl : listed p) (j : Nat) :
    crosses (stack p) j ↔ StripConverse.hits p j := by
  induction p generalizing j with
  | nil => simp [stack,crosses,StripConverse.hits]
  | cons g gs ih =>
    obtain ⟨hg,hl⟩ := listed_cons hl
    cases j with
    | zero =>
      simp only [StripConverse.hits,iff_false]
      rintro ⟨t,ht,hs⟩
      obtain ⟨k,m,hm,rfl⟩ := mem_stack.mp ht
      have hlist : listed (g::gs) := fun u hu => by rcases List.mem_cons.mp hu with rfl|h <;> first | exact hg | exact hl _ h
      have := ((split_stamp_iff (hlist _ (List.getElem_mem k.isLt) m hm)).mp hs).1
      omega
    | succ j =>
      change (∃ t ∈ g.image pattern ∪ translated 1 (stack gs), split t (j+1)) ↔
        StripConverse.reaches (blocks g) (j+1) ∨ StripConverse.hits gs j
      rw [← ih hl]
      constructor
      · rintro ⟨t,ht,hs⟩
        obtain h|h := Finset.mem_union.mp ht
        · obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp h
          obtain ⟨q,hq,h⟩ := hs.2
          exact Or.inl ⟨q,Finset.mem_biUnion.mpr ⟨m,hm,hq⟩,h⟩
        · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp h
          exact Or.inr ⟨q,hq,(split_succ j).mp hs⟩
      · rintro (⟨q,hq,h⟩ | ⟨t,ht,hs⟩)
        · obtain ⟨m,hm,hq⟩ := Finset.mem_biUnion.mp hq
          obtain ⟨v,hv,hv0⟩ := (TileDictionary.catalog_sound _ (hg m hm)).1.2
          exact ⟨pattern m,Finset.mem_union_left _ (Finset.mem_image_of_mem pattern hm),
            ⟨v,hv,by omega⟩,q,hq,h⟩
        · exact ⟨offset 1 t,Finset.mem_union_right _ (Finset.mem_image_of_mem (offset 1) ht),(split_succ j).mpr hs⟩

end StackGeometry

namespace BoardLattice
open OMA.S_oeis_a084481 (LatticePoint TileCell isLTile faultFreeTiling)
open TileDictionary (world picture pattern offset)
open StripPacking (strip mem_strip)
open StackIndex (stamp supported)
open StackGeometry (packed area crosses split)

def liftTile {n : Nat} (t : Finset (TileCell n)) := t.image world
def liftTiles {n : Nat} (T : Finset (Finset (TileCell n))) := T.image liftTile

def lowerTile (n : Nat) (u : Finset LatticePoint) : Finset (TileCell n) :=
  Finset.univ.filter (fun a => world a ∈ u)
def lowerTiles (n : Nat) (U : Finset (Finset LatticePoint)) := U.image (lowerTile n)

theorem world_inj {n : Nat} : Function.Injective (@world n) := by
  intro a b h
  have hs := congrArg Prod.fst h
  have ht := congrArg Prod.snd h
  apply Prod.ext <;> apply Fin.ext <;> dsimp [world] at * <;> omega

theorem world_strip {n : Nat} (a : TileCell n) : world a ∈ strip (2*n) := by
  rw [mem_strip]
  have hr := a.1.isLt
  have hc := a.2.isLt
  dsimp [world]
  omega

theorem strip_world {n : Nat} {p : LatticePoint} (h : p ∈ strip (2*n)) :
    ∃ a : TileCell n, world a = p := by
  have he := (mem_strip _).mp h
  refine ⟨(⟨p.1.toNat,by omega⟩,⟨p.2.toNat,by omega⟩),?_⟩
  exact Prod.ext (by dsimp [world]; omega) (by dsimp [world]; omega)

@[simp] theorem in_lift {n : Nat} {a : TileCell n} {t : Finset (TileCell n)} :
    world a ∈ liftTile t ↔ a ∈ t := by
  constructor
  · intro h
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp h
    exact world_inj he ▸ hb
  · exact Finset.mem_image_of_mem _

theorem lower_lift {n : Nat} (t : Finset (TileCell n)) : lowerTile n (liftTile t) = t := by
  ext
  simp [lowerTile]

theorem lift_lower {n : Nat} {u : Finset LatticePoint} (hu : u ⊆ strip (2*n)) :
    liftTile (lowerTile n u) = u := by
  ext p
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp ha).2
  · intro h
    obtain ⟨a,rfl⟩ := strip_world (hu h)
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)

theorem lower_lift_tiles {n : Nat} (T : Finset (Finset (TileCell n))) : lowerTiles n (liftTiles T) = T := by
  simp [lowerTiles,liftTiles,Finset.image_image,Function.comp_def,lower_lift]

theorem lift_lower_tiles {n : Nat} {U : Finset (Finset LatticePoint)} (h : area U = strip (2*n)) :
    liftTiles (lowerTiles n U) = U := by
  ext t
  constructor
  · intro ht
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
    have hi : v ⊆ strip (2*n) := fun a ha => h ▸ Finset.mem_biUnion.mpr ⟨v,hv,ha⟩
    simpa [lift_lower hi] using hv
  · intro ht
    have hi : t ⊆ strip (2*n) := fun a ha => h ▸ Finset.mem_biUnion.mpr ⟨t,ht,ha⟩
    exact lift_lower hi ▸ Finset.mem_image_of_mem liftTile (Finset.mem_image_of_mem (lowerTile n) ht)

theorem liftTile_inj {n : Nat} {t v : Finset (TileCell n)} (h : liftTile t = liftTile v) : t = v := by
  simpa only [lower_lift] using congrArg (lowerTile n) h

theorem legal_iff {n : Nat} {t : Finset (TileCell n)} :
    isLTile t ↔ ∃ (k : Fin (2*n)) (m : Nat), m ∈ ProfileEnumeration.placements ∧
      liftTile t = stamp k.val m := by
  constructor
  · intro h
    have ht : t.Nonempty := by
      obtain ⟨c,u,v,_,hi⟩ := h
      have hc : c ∈ t.image world := by rw [show t.image world = _ from hi]; simp
      obtain ⟨a,ha,_⟩ := Finset.mem_image.mp hc
      exact ⟨a,ha⟩
    let cols := t.image (fun a => a.2.val)
    have hn : cols.Nonempty := ht.image _
    let k := cols.min' hn
    have hm := Finset.min'_mem cols hn
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hm
    change a.2.val = k at he
    have hbound : k < 2*n := by rw [← he]; exact a.2.isLt
    have hlow (b) (hb : b ∈ t) : k ≤ b.2.val := Finset.min'_le _ _ (Finset.mem_image_of_mem _ hb)
    obtain ⟨m,hm,hp⟩ := (TileDictionary.tile_iff_placement k t).1 ⟨h,⟨a,ha,he⟩,hlow⟩
    exact ⟨⟨k,hbound⟩,m,hm,(TileDictionary.offset_picture k t).symm.trans (congrArg (offset (k:ℤ)) hp)⟩
  · rintro ⟨k,m,hm,he⟩
    have hp : picture k.val t = pattern m := by
      change offset (-(k.val:ℤ)) (liftTile t) = _
      rw [he,stamp,StackIndex.offset_add]
      simp
    exact ((TileDictionary.tile_iff_placement k.val t).2 ⟨m,hm,hp⟩).1

theorem allLegal {n : Nat} {T : Finset (Finset (TileCell n))} :
    (∀ t ∈ T, isLTile t) ↔ supported (2*n) (liftTiles T) := by
  constructor
  · intro h t ht
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
    exact legal_iff.mp (h _ hu)
  · intro h t ht
    exact legal_iff.mpr (h _ (Finset.mem_image_of_mem liftTile ht))

theorem cut_lift {n : Nat} {T : Finset (Finset (TileCell n))} (k : Nat) :
    (∃ t ∈ T, (∃ a ∈ t, a.2.val < k) ∧ (∃ b ∈ t, k ≤ b.2.val)) ↔ crosses (liftTiles T) k := by
  simp [crosses,split,liftTiles,liftTile,world]

theorem coverage_lift {n : Nat} (T : Finset (Finset (TileCell n))) :
    (∀ a : TileCell n, ∃! t : Finset (TileCell n), t ∈ T ∧ a ∈ t) ↔
      packed (liftTiles T) ∧ area (liftTiles T) = strip (2*n) := by
  constructor
  · intro h
    constructor
    · intro u hu v hv hn
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
      apply Finset.disjoint_left.mpr
      intro p hp hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨b,_,uniq⟩ := h a
      have h' := (uniq t ⟨ht,ha⟩).trans (uniq q ⟨hq,in_lift.mp hz⟩).symm
      exact hn (congrArg liftTile h')
    · ext p
      constructor
      · intro hp
        obtain ⟨u,hu,hp⟩ := Finset.mem_biUnion.mp hp
        obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
        exact world_strip a
      · intro hp
        obtain ⟨a,rfl⟩ := strip_world hp
        obtain ⟨t,⟨ht,ha⟩,_⟩ := h a
        exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_image_of_mem liftTile ht,in_lift.mpr ha⟩
  · rintro ⟨hd,he⟩ a
    have hp : world a ∈ area (liftTiles T) := he.symm ▸ world_strip a
    obtain ⟨u,hu,hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hu
    refine ⟨t,⟨ht,in_lift.mp hp⟩,?_⟩
    rintro v ⟨hv,hav⟩
    by_contra hn
    have hdis := hd _ (Finset.mem_image_of_mem liftTile hv) _ (Finset.mem_image_of_mem liftTile ht)
      (fun h => hn (liftTile_inj h))
    exact Finset.disjoint_left.mp hdis (in_lift.mpr hav) hp

theorem board_iff {n : Nat} (T : Finset (Finset (TileCell n))) :
    faultFreeTiling T ↔ supported (2*n) (liftTiles T) ∧ packed (liftTiles T) ∧
      area (liftTiles T) = strip (2*n) ∧ ∀ j : Nat, 0 < j → j < 2*n → crosses (liftTiles T) j := by
  unfold faultFreeTiling
  simp_rw [allLegal,coverage_lift,cut_lift]
  tauto

end BoardLattice

namespace OMA.R_oeis_a084481_R1

open OMA.S_oeis_a084481

def H1 : Prop :=
  tilingCount 4 = 18 ∧ tilingCount 5 = 38 ∧ tilingCount 6 = 84

def H2 : Prop :=
  ∀ k : ℕ, tilingCount (k + 7) = 2 * tilingCount (k + 6) + tilingCount (k + 4)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a084481.main := by
  rintro ⟨hl4, hl5, hl6⟩ recL ⟨_, hb1, hb2, hb3, recB⟩
  have hb4 : arrayCount 4 = 2 * arrayCount 3 + arrayCount 1 := recB 0
  have hb5 : arrayCount 5 = 2 * arrayCount 4 + arrayCount 2 := recB 1
  have tri : ∀ k : ℕ, tilingCount (k+4) = 2 * arrayCount (k+3) ∧
      tilingCount (k+5) = 2 * arrayCount (k+4) ∧
      tilingCount (k+6) = 2 * arrayCount (k+5) := by
    intro k
    induction k with
    | zero =>
      change tilingCount 4 = 2 * arrayCount 3 ∧ tilingCount 5 = 2 * arrayCount 4 ∧
        tilingCount 6 = 2 * arrayCount 5
      exact ⟨by omega, by omega, by omega⟩
    | succ k ih =>
      obtain ⟨e0, e1, e2⟩ := ih
      refine ⟨e1, e2, ?_⟩
      change tilingCount (k+7) = 2 * arrayCount (k+6)
      have ht := recL k
      have hb : arrayCount (k+6) = 2 * arrayCount (k+5) + arrayCount (k+3) := recB (k+2)
      omega
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ n by omega)
  simpa [Nat.add_comm] using (tri k).1

end OMA.R_oeis_a084481_R1

namespace CompleteTiling
open OMA.S_oeis_a084481 (TileCell faultFreeTiling)
open TileDictionary (pattern)
open LabeledPaths (paths)
open StackIndex (stack listed decode)
open BoardLattice (liftTiles lowerTiles)
open StackGeometry (area packed crosses)
open StripPacking (strip compatible)

theorem listed_compatible {p : List (Finset Nat)} (hp : compatible p) : listed p := by
  induction p with
  | nil => simp [listed]
  | cons g gs ih =>
    obtain ⟨hg,_,hc⟩ := hp
    intro u hu
    rcases List.mem_cons.mp hu with rfl|hu
    · exact hg.1
    · exact ih hc _ hu

private theorem empty_pattern : pattern 0 = ∅ := by decide

theorem path_geometry {k : Nat} {p : List (Finset Nat)} (hlen : p.length = k+1) :
    p ∈ paths k 0 ↔ listed p ∧ packed (stack p) ∧ area (stack p) = strip p.length ∧
      ∀ j : Nat, 0 < j → j < p.length → crosses (stack p) j := by
  rw [StripConverse.paths_iff hlen]
  change Disjoint (pattern 0) _ ∧ pattern 0 ∪ _ = _ ∧ compatible p ∧ StripConverse.noFault (pattern 0) p ↔ _
  rw [empty_pattern]
  simp only [Finset.disjoint_empty_left,Finset.empty_union,true_and]
  constructor
  · rintro ⟨he,hc,hf⟩
    have hl := listed_compatible hc
    refine ⟨hl,(StackGeometry.packed_stack hl).mpr hc, by rw [StackGeometry.area_stack,he],?_⟩
    intro j hj hw
    apply (StackGeometry.crosses_stack hl j).2
    simpa [StripConverse.reaches] using hf j hj hw
  · rintro ⟨hl,hc,he,hf⟩
    refine ⟨by rwa [← StackGeometry.area_stack],(StackGeometry.packed_stack hl).1 hc,?_⟩
    exact fun j hj hw => Or.inr ((StackGeometry.crosses_stack hl j).mp (hf j hj hw))

theorem board_to_paths (n : Nat) {T : Finset (Finset (TileCell (n+1)))} (ht : faultFreeTiling T) :
    decode (2*(n+1)) (liftTiles T) ∈ paths (2*n+1) 0 := by
  obtain ⟨hs,hp,ha,hf⟩ := (BoardLattice.board_iff T).mp ht
  rw [path_geometry (by rw [StackIndex.decode_length]; omega),StackIndex.stack_decode hs,
    StackIndex.decode_length]
  exact ⟨StackIndex.decode_listed _ _,hp,ha,hf⟩

theorem paths_to_board (n : Nat) {p : List (Finset Nat)} (hp : p ∈ paths (2*n+1) 0) :
    faultFreeTiling (lowerTiles (n+1) (stack p)) := by
  have hlen := LabeledPaths.mem_paths_length hp
  have hw : p.length = 2*(n+1) := by omega
  obtain ⟨hl,hpack,ha,hf⟩ := (path_geometry hlen).mp hp
  have hs := StackIndex.stack_supported hl
  rw [hw] at ha hf hs
  rw [BoardLattice.board_iff,BoardLattice.lift_lower_tiles ha]
  exact ⟨hs,hpack,ha,hf⟩

noncomputable def bijection (n : Nat) :
    {T : Finset (Finset (TileCell (n+1))) // faultFreeTiling T} ≃
      ↥(paths (2*n+1) 0).toFinset where
  toFun T := ⟨_,List.mem_toFinset.mpr (board_to_paths n T.property)⟩
  invFun p := ⟨_,paths_to_board n (List.mem_toFinset.mp p.property)⟩
  left_inv T := by
    apply Subtype.ext
    change lowerTiles _ (stack (decode _ (liftTiles T.val))) = T.val
    rw [StackIndex.stack_decode ((BoardLattice.board_iff T.val).1 T.property).1,
      BoardLattice.lower_lift_tiles]
  right_inv p := by
    apply Subtype.ext
    have hm := List.mem_toFinset.mp p.property
    have len := LabeledPaths.mem_paths_length hm
    have hw : p.val.length = 2*(n+1) := by omega
    obtain ⟨hl,_,ha,_⟩ := (path_geometry len).mp hm
    rw [hw] at ha
    change decode _ (liftTiles (lowerTiles _ (stack p.val))) = p.val
    rw [BoardLattice.lift_lower_tiles ha,← hw,StackIndex.decode_stack hl]

theorem counts_agree (n : Nat) :
    OMA.S_oeis_a084481.tilingCount (n+1) = ProfileEnumeration.tilingCount (n+1) := by
  classical
  let s := (Finset.univ.filter (@faultFreeTiling (n+1)))
  let e : ↥s ≃ {T : Finset (Finset (TileCell (n+1))) // faultFreeTiling T} :=
    Equiv.subtypeEquivRight (fun T => by simp [s])
  change s.card = _
  rw [← LabeledPaths.count_distinct_paths,← Fintype.card_coe,← Fintype.card_coe]
  exact Fintype.card_congr (e.trans (bijection n))

theorem main : OMA.S_oeis_a084481.Target := by
  apply OMA.R_oeis_a084481_R1.main
  · unfold OMA.R_oeis_a084481_R1.H1
    rw [counts_agree 3,counts_agree 4,counts_agree 5]
    exact ProfileEnumeration.count_initial
  · intro k
    rw [counts_agree (k+6),counts_agree (k+5),counts_agree (k+3)]
    exact ProfileEnumeration.count_recurrence k

end CompleteTiling

theorem OMA.solution : type_of% @OMA.S_oeis_a084481.main := by
  exact CompleteTiling.main
