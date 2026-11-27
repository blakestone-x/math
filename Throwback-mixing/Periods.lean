import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring

/-! Exact first returns in the relative-position coordinates of a throwback queue.
The queue-to-coordinate conjugacy is proved in the accompanying manuscript. -/
namespace Throwback

inductive Levels where
  | empty
  | extend (lower : Levels) (radix : Nat)

def Admissible : Levels → Prop
  | .empty => True
  | .extend lower r => Admissible lower ∧ 2 ≤ r

/-- Number of steps on which all tracked levels let the next level advance.
The first incoming tick at a new level belongs to its tracked leader. -/
def passes : Levels → Nat → Nat
  | .empty, t => t
  | .extend lower r, t =>
    let h := passes lower t
    h - (h / r + if h % r = 0 then 0 else 1)

/-- The negative of each phase equals its relative queue position modulo its radix. -/
def AtOrigin : Levels → Nat → Prop
  | .empty, _ => True
  | .extend lower r, t => AtOrigin lower t ∧ r ∣ passes lower t

/-- The first coordinate is the period, the second the number of passes per period. -/
def cycle : Levels → Nat × Nat
  | .empty => (1,1)
  | .extend lower r =>
    let (p,h) := cycle lower
    let g := Nat.gcd r h
    (p * (r/g), h/g * (r-1))

private theorem rotation_order (r h k : Nat) (hr : 0 < r) :
    r ∣ k*h ↔ r / Nat.gcd r h ∣ k := by
  let g := Nat.gcd r h
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hr
  have he : (r/g)*g = r := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  rw [← Nat.dvd_mul_gcd_iff_dvd_mul]
  change r ∣ k*g ↔ r/g ∣ k
  conv_lhs => lhs; rw [← he]
  exact Nat.mul_dvd_mul_iff_right hg

theorem cycle_spec (s : Levels) (hs : Admissible s) :
    0 < (cycle s).1 ∧ 0 < (cycle s).2 ∧
    (∀ t, AtOrigin s t ↔ (cycle s).1 ∣ t) ∧
    (∀ k, passes s ((cycle s).1*k) = (cycle s).2*k) := by
  induction s with
  | empty => simp [cycle, AtOrigin, passes]
  | extend lower r ih =>
    rcases hs with ⟨hadm, hr⟩
    rcases ih hadm with ⟨hp, hh, hret, hpasses⟩
    let p := (cycle lower).1
    let h := (cycle lower).2
    let g := Nat.gcd r h
    have hr0 : 0 < r := by omega
    have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hr0
    have er : r/g*g = r := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
    have eh : h/g*g = h := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
    have hrg : 0 < r/g := Nat.div_pos (Nat.le_of_dvd hr0 (Nat.gcd_dvd_left _ _)) hg
    have hhg : 0 < h/g := Nat.div_pos (Nat.le_of_dvd hh (Nat.gcd_dvd_right _ _)) hg
    change 0 < p*(r/g) ∧ 0 < (h/g)*(r-1) ∧
      (∀ t, (AtOrigin lower t ∧ r ∣ passes lower t) ↔ p*(r/g) ∣ t) ∧
      (∀ k, passes (.extend lower r) (p*(r/g)*k) = h/g*(r-1)*k)
    refine ⟨Nat.mul_pos hp hrg, Nat.mul_pos hhg (by omega), ?_, ?_⟩
    · intro t
      constructor
      · rintro ⟨ha, hb⟩
        obtain ⟨k, rfl⟩ := (hret t).mp ha
        rw [hpasses, Nat.mul_comm] at hb
        obtain ⟨m, hm⟩ := (rotation_order r h k hr0).mp hb
        exact ⟨m, by rw [hm]; simp [p, g, Nat.mul_assoc]⟩
      · rintro ⟨k, rfl⟩
        rw [Nat.mul_assoc]
        refine ⟨(hret _).mpr ⟨_, rfl⟩, ?_⟩
        rw [show p = (cycle lower).1 from rfl, hpasses, Nat.mul_comm]
        exact (rotation_order r h _ hr0).mpr ⟨k, rfl⟩
    · intro k
      let v := h/g*k
      have count : h*(r/g*k) = v*r := by
        calc
          h*(r/g*k) = (h/g*g)*(r/g*k) := by rw [eh]
          _ = (h/g*k)*(r/g*g) := by ring
          _ = v*r := by rw [er]
      simp only [passes, Nat.mul_assoc p]
      rw [show p = (cycle lower).1 from rfl, hpasses]
      change h*(r/g*k) - (h*(r/g*k)/r + (if h*(r/g*k)%r = 0 then 0 else 1)) = _
      rw [count, Nat.mul_div_cancel _ hr0, Nat.mul_mod_left]
      simp only [if_true, Nat.add_zero]
      calc
        v*r-v = v*(r-1) := by rw [Nat.mul_sub, Nat.mul_one]
        _ = h/g*(r-1)*k := by dsimp [v]; ring


def capacity : Levels → Nat
  | .empty => 1
  | .extend lower r => capacity lower * r

def freeProduct : Levels → Nat
  | .empty => 1
  | .extend lower r => freeProduct lower * (r-1)

/-- Each new radix must be coprime to the product of all preceding radices minus
one per factor, namely ∏ (r_i - 1). -/
def Compatible : Levels → Prop
  | .empty => True
  | .extend lower r => Compatible lower ∧ Nat.Coprime r (freeProduct lower)

theorem perfect_mixing (s : Levels) (hs : Admissible s) :
    (cycle s).1 ≤ capacity s ∧
    ((cycle s).1 = capacity s ↔ Compatible s) ∧
    (Compatible s → (cycle s).2 = freeProduct s) := by
  induction s with
  | empty => simp [cycle, capacity, freeProduct, Compatible]
  | extend lower r ih =>
    rcases hs with ⟨ha, hr⟩
    obtain ⟨hcap, hiff, hfree⟩ := ih ha
    have hp := (cycle_spec lower ha).1
    let p := (cycle lower).1
    let h := (cycle lower).2
    let g := Nat.gcd r h
    have hq : r/g ≤ r := Nat.div_le_self _ _
    have eqr : r/g*g = r := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
    change p*(r/g) ≤ capacity lower*r ∧
      (p*(r/g) = capacity lower*r ↔ Compatible lower ∧ Nat.Coprime r (freeProduct lower)) ∧
      ((Compatible lower ∧ Nat.Coprime r (freeProduct lower)) →
        h/g*(r-1) = freeProduct lower*(r-1))
    refine ⟨Nat.mul_le_mul hcap hq, ⟨?_, ?_⟩, ?_⟩
    · intro he
      have ep : p = capacity lower := by
        apply Nat.le_antisymm hcap
        by_contra hn
        have lt : p*r < capacity lower*r := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        have le : capacity lower*r ≤ p*r := he ▸ Nat.mul_le_mul_left p hq
        exact (Nat.not_lt_of_ge le) lt
      have hqeq : r/g = r := by
        rw [← ep] at he
        exact Nat.eq_of_mul_eq_mul_left hp he
      have eg : g = 1 := by
        rw [hqeq] at eqr
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < r) (eqr.trans (Nat.mul_one r).symm)
      have hgood := hiff.mp ep
      refine ⟨hgood, ?_⟩
      change Nat.gcd r (freeProduct lower) = 1
      rw [← hfree hgood]
      exact eg
    · rintro ⟨hgood, hc⟩
      have eh : h = freeProduct lower := hfree hgood
      have eg : g = 1 := by dsimp [g]; rw [eh]; exact hc
      rw [eg, Nat.div_one, show p = capacity lower from hiff.mpr hgood]
    · rintro ⟨hgood, hc⟩
      have eh : h = freeProduct lower := hfree hgood
      have eg : g = 1 := by dsimp [g]; rw [eh]; exact hc
      rw [eg, Nat.div_one, eh]

#print axioms cycle_spec
#print axioms perfect_mixing
end Throwback
