import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Ring

/-!
# OEIS A087412: the cubic congruence modulo powers of three

Blake Stone, developed with OpenAI Astra 6.2. November 26, 2026.

This file proves Andrew Howroyd's July 17, 2018 conjecture that the number
of ordered residue pairs solving x^3 + y^3 = 1 modulo 3^e is 2 * 3^e
for every e > 1. The finite sum is explicitly identified with the
cardinality of the original solution set.
-/

open scoped BigOperators
open Finset
namespace A087412

def F {R : Type*} [Semiring R] (x : R) : R := x + 3*x^2 + 3*x^3

theorem F_injective (k : ℕ) : Function.Injective (F : ZMod (3^k) → ZMod (3^k)) := by
  intro x y hxy
  have hnil : IsNilpotent (3 : ZMod (3^k)) := by
    refine ⟨k, ?_⟩
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (3^k)
  have hu : IsUnit (1 + 3*(x+y+x^2+x*y+y^2)) :=
    ((Commute.all _ _).isNilpotent_mul_left hnil).isUnit_one_add
  have hf : (x-y)*(1 + 3*(x+y+x^2+x*y+y^2)) = 0 := by
    calc
      _ = F x - F y := by unfold F; ring
      _ = 0 := sub_eq_zero.mpr hxy
  exact sub_eq_zero.mp (hu.mul_left_injective (by simpa using hf))

theorem F_bijective (k : ℕ) : Function.Bijective (F : ZMod (3^k) → ZMod (3^k)) :=
  (Finite.injective_iff_bijective).mp (F_injective k)

theorem finEquiv_coe (M : ℕ) [NeZero M] (x : Fin M) :
    ZMod.finEquiv M x = (x.val : ZMod M) := by
  cases M with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact (Fin.cast_val_eq_self x).symm

theorem F_sum (k c : ℕ) :
    (∑ v : Fin (3^k), if (3*c^3 + F v.val) % (3^k) = 0 then 1 else 0) = 1 := by
  let M := 3^k
  haveI : NeZero M := ⟨pow_ne_zero _ (by decide)⟩
  have hf : ∀ v : Fin M,
      (3*c^3 + F v.val) % M = 0 ↔
      (3*(c : ZMod M)^3 + F (ZMod.finEquiv M v)) = 0 := by
    intro v
    rw [finEquiv_coe]
    rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_zmod_eq_zero_iff_dvd]
    simp only [F, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  change (∑ v : Fin M, if (3*c^3 + F v.val) % M = 0 then 1 else 0) = 1
  simp_rw [hf]
  trans (∑ z : ZMod M, if 3*(c : ZMod M)^3 + F z = 0 then 1 else 0)
  · exact Fintype.sum_equiv (ZMod.finEquiv M).toEquiv _ _ (fun _ => rfl)
  trans (∑ z : ZMod M, if 3*(c : ZMod M)^3 + z = 0 then 1 else 0)
  · exact (F_bijective k).sum_comp (fun z => if 3*(c : ZMod M)^3 + z = 0 then (1 : ℕ) else 0)
  simp [add_eq_zero_iff_neg_eq]

theorem cube_mod_nine (a u : ℕ) : (a+3*u)^3 ≡ a^3 [MOD 9] := by
  have he : (a+3*u)^3 = a^3 + 9*(a^2*u + 3*a*u^2 + 3*u^3) := by ring
  rw [he]
  simp [Nat.ModEq, Nat.add_mod]

theorem residue_cases (M u v : ℕ) (a b : Fin 3)
    (h : (a.val+3*u)^3 + (b.val+3*v)^3 ≡ 1 [MOD 9*M]) :
    (a.val=0 ∧ b.val=1) ∨ (a.val=1 ∧ b.val=0) := by
  have h9 : a.val^3+b.val^3 ≡ 1 [MOD 9] :=
    ((cube_mod_nine a.val u).add (cube_mod_nine b.val v)).symm.trans
      (h.of_dvd (dvd_mul_right 9 M))
  have ha := a.isLt
  have hb := b.isLt
  have ha0 : a.val=0 ∨ a.val=1 ∨ a.val=2 := by omega
  have hb0 : b.val=0 ∨ b.val=1 ∨ b.val=2 := by omega
  rcases ha0 with ha0 | ha0 | ha0 <;> rcases hb0 with hb0 | hb0 | hb0 <;>
    simp_all [Nat.ModEq]

theorem equation_normalized (M u v : ℕ) :
    (3*u)^3 + (1+3*v)^3 ≡ 1 [MOD 9*M] ↔
    3*u^3 + F v ≡ 0 [MOD M] := by
  have he : (3*u)^3 + (1+3*v)^3 = 9*(3*u^3+F v)+1 := by unfold F; ring
  rw [he]
  constructor
  · intro h
    have h' : 9*(3*u^3+F v) ≡ 9*0 [MOD 9*M] := by
      simpa using h.add_right_cancel' 1
    exact h'.mul_left_cancel' (by decide)
  · intro h
    simpa using (h.mul_left' 9).add_right 1

/-- The original count of ordered pairs of residues solving the cubic congruence. -/
def a (N : ℕ) : ℕ :=
  ∑ x : Fin N, ∑ y : Fin N,
    if x.val^3 + y.val^3 ≡ 1 [MOD N] then 1 else 0

theorem sum_fin_mul (M N : ℕ) (f : ℕ → ℕ) :
    (∑ x : Fin (M*N), f x.val) =
    ∑ u : Fin M, ∑ v : Fin N, f (v.val+N*u.val) := by
  calc
    _ = ∑ p : Fin M × Fin N, f (p.2.val+N*p.1.val) :=
      (finProdFinEquiv.sum_comp (fun x : Fin (M*N) => f x.val)).symm
    _ = _ := Fintype.sum_prod_type _

theorem solution_split (M u v : ℕ) (a b : Fin 3) :
    (a.val+3*u)^3+(b.val+3*v)^3 ≡ 1 [MOD 9*M] ↔
    (a.val=0 ∧ b.val=1 ∧ 3*u^3+F v ≡ 0 [MOD M]) ∨
    (a.val=1 ∧ b.val=0 ∧ 3*v^3+F u ≡ 0 [MOD M]) := by
  constructor
  · intro h
    rcases residue_cases M u v a b h with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨ha,hb,(equation_normalized M u v).mp (by simpa [ha,hb] using h)⟩
    · exact Or.inr ⟨ha,hb,(equation_normalized M v u).mp (by simpa [ha,hb,add_comm] using h)⟩
  · rintro (⟨ha,hb,h⟩ | ⟨ha,hb,h⟩)
    · simpa [ha,hb] using (equation_normalized M u v).mpr h
    · simpa [ha,hb,add_comm] using (equation_normalized M v u).mpr h

theorem residue_sum (M u v : ℕ) :
    (∑ a : Fin 3, ∑ b : Fin 3,
      if (a.val+3*u)^3+(b.val+3*v)^3 ≡ 1 [MOD 9*M] then 1 else 0) =
    (if 3*u^3+F v ≡ 0 [MOD M] then 1 else 0) +
    (if 3*v^3+F u ≡ 0 [MOD M] then 1 else 0) := by
  simp_rw [solution_split]
  simp_rw [Fin.sum_univ_succ]
  simp

theorem sum_fin_mul_two (M N : ℕ) (f : ℕ → ℕ → ℕ) :
    (∑ x : Fin (M*N), ∑ y : Fin (M*N), f x.val y.val) =
    ∑ u : Fin M, ∑ a : Fin N, ∑ v : Fin M, ∑ b : Fin N,
      f (a.val+N*u.val) (b.val+N*v.val) := by
  calc
    _ = ∑ u : Fin M, ∑ a : Fin N, ∑ y : Fin (M*N),
        f (a.val+N*u.val) y.val :=
      sum_fin_mul M N (fun x => ∑ y : Fin (M*N), f x y.val)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro a ha
      exact sum_fin_mul M N (f (a.val+N*u.val))

theorem count_normalized (M : ℕ) :
    a (9*M) =
    2 * ∑ u : Fin (3*M), ∑ v : Fin (3*M),
      if 3*u.val^3+F v.val ≡ 0 [MOD M] then 1 else 0 := by
  unfold a
  have he : 9*M = (3*M)*3 := by omega
  conv_lhs => rw [he]
  trans ∑ u : Fin (3*M), ∑ a : Fin 3, ∑ v : Fin (3*M), ∑ b : Fin 3,
      if (a.val+3*u.val)^3+(b.val+3*v.val)^3 ≡ 1 [MOD (3*M)*3] then 1 else 0
  · exact sum_fin_mul_two (3*M) 3
      (fun x y => if x^3+y^3 ≡ 1 [MOD (3*M)*3] then 1 else 0)
  simp only [← he]
  trans ∑ u : Fin (3*M), ∑ v : Fin (3*M), ∑ a : Fin 3, ∑ b : Fin 3,
      if (a.val+3*u.val)^3+(b.val+3*v.val)^3 ≡ 1 [MOD 9*M] then 1 else 0
  · apply Finset.sum_congr rfl
    intro u hu
    exact Finset.sum_comm
  simp_rw [residue_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun u v : Fin (3*M) =>
    if 3*v.val^3+F u.val ≡ 0 [MOD M] then 1 else 0)]
  omega

theorem normalized_period (M u v j : ℕ) :
    3*u^3+F (v+M*j) ≡ 0 [MOD M] ↔ 3*u^3+F v ≡ 0 [MOD M] := by
  simp [Nat.ModEq, F, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

theorem F_sum_lift (k u : ℕ) :
    (∑ v : Fin (3*3^k), if 3*u^3+F v.val ≡ 0 [MOD 3^k] then 1 else 0) = 3 := by
  rw [sum_fin_mul 3 (3^k) (fun v => if 3*u^3+F v ≡ 0 [MOD 3^k] then 1 else 0)]
  simp_rw [normalized_period]
  simp only [Nat.ModEq, Nat.zero_mod, F_sum]
  simp

/-- Howroyd's conjecture, in the equivalent nonnegative-exponent form. -/
theorem conjecture_shifted (k : ℕ) : a (3^(k+2)) = 2*3^(k+2) := by
  have he : 3^(k+2) = 9*3^k := by ring
  rw [he, count_normalized]
  simp only [F_sum_lift, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  ring

/-- Exactly the domain in the OEIS statement: every exponent greater than one. -/
theorem conjecture (e : ℕ) (he : 1 < e) : a (3^e) = 2*3^e := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k+2 := ⟨e-2, by omega⟩
  exact conjecture_shifted k

/-- The finite-sum definition equals the cardinality of the literal solution set. -/
theorem original_count (N : ℕ) :
    a N = Fintype.card {xy : Fin N × Fin N //
      xy.1.val^3+xy.2.val^3 ≡ 1 [MOD N]} := by
  rw [Fintype.card_subtype]
  unfold a
  rw [← Fintype.sum_prod_type' (fun x y : Fin N =>
    if x.val^3+y.val^3 ≡ 1 [MOD N] then (1 : ℕ) else 0)]
  exact Finset.sum_boole _ _

/-- The conjecture stated directly as the cardinality of its original solution set. -/
theorem original_conjecture (e : ℕ) (he : 1 < e) :
    Fintype.card {xy : Fin (3^e) × Fin (3^e) //
      xy.1.val^3+xy.2.val^3 ≡ 1 [MOD 3^e]} = 2*3^e :=
  (original_count (3^e)).symm.trans (conjecture e he)

#print axioms F_injective
#print axioms original_count
#print axioms conjecture
#print axioms original_conjecture
end A087412
