import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

/-!
# The literal orphan count and its divisor convolution

Blake Stone, developed with OpenAI Astra 6.2, November 26, 2026.

The orphan-counting function A274628 counts nonnegative integer solutions
`a*b-c*d=n` with `a>c` and `b>d`. This file defines exactly those solutions,
proves they form a finite type, and proves the classical divisor-convolution
formula using explicit bijections. The formula is established prior mathematics;
the purpose here is a complete original-definition bridge for the weighted
triangle conjecture A389524, with no generating-function assumption.
-/

open Finset

namespace Nathanson

/-- The literal integer solutions in the definition of the orphan-counting function. -/
@[ext] structure Orphan (n : ℕ) where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  ca : c < a
  db : d < b
  det : a * b = n + c * d

lemma Orphan.bounds {n : ℕ} (o : Orphan n) :
    o.a ≤ n ∧ o.b ≤ n ∧ o.c ≤ n ∧ o.d ≤ n := by
  have hca := o.ca
  have hdb := o.db
  have h1 := Nat.mul_le_mul_left o.a (show o.d + 1 ≤ o.b by omega)
  have h2 := Nat.mul_le_mul_right o.d (Nat.le_of_lt o.ca)
  have h3 := Nat.mul_le_mul_right o.b (show o.c + 1 ≤ o.a by omega)
  have h4 := Nat.mul_le_mul_left o.c (Nat.le_of_lt o.db)
  have h := o.det
  have ha : o.a ≤ n := by nlinarith
  have hb : o.b ≤ n := by nlinarith
  exact ⟨ha, hb, le_trans (Nat.le_of_lt o.ca) ha, le_trans (Nat.le_of_lt o.db) hb⟩

noncomputable instance (n : ℕ) : Fintype (Orphan n) := by
  let f : Orphan n → Fin (n+1) × Fin (n+1) × Fin (n+1) × Fin (n+1) := fun o =>
    (⟨o.a, by have := o.bounds; omega⟩, ⟨o.b, by have := o.bounds; omega⟩,
     ⟨o.c, by have := o.bounds; omega⟩, ⟨o.d, by have := o.bounds; omega⟩)
  have hf : Function.Injective f := by
    intro o p h
    have h1 := congrArg (fun z => z.1.val) h
    have h2 := congrArg (fun z => z.2.1.val) h
    have h3 := congrArg (fun z => z.2.2.1.val) h
    have h4 := congrArg (fun z => z.2.2.2.val) h
    exact Orphan.ext h1 h2 h3 h4
  haveI : Finite (Orphan n) := Finite.of_injective f hf
  exact Fintype.ofFinite _

noncomputable def orphanCount (n : ℕ) := Fintype.card (Orphan n)

@[ext] structure Pair (n : ℕ) where
  x : ℕ
  y : ℕ
  hx : 0 < x
  hy : 0 < y
  eqn : x * y = n

def pairDivisor (n : ℕ) : Pair n ≃ ↥n.divisors where
  toFun p := ⟨p.x, Nat.mem_divisors.mpr ⟨⟨p.y, p.eqn.symm⟩,
    by have := Nat.mul_pos p.hx p.hy; have := p.eqn; omega⟩⟩
  invFun d := {
    x := d.val
    y := n / d.val
    hx := Nat.pos_of_mem_divisors d.property
    hy := Nat.div_pos (Nat.divisor_le d.property) (Nat.pos_of_mem_divisors d.property)
    eqn := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors d.property) }
  left_inv p := by
    apply Pair.ext
    · rfl
    · dsimp
      calc
        n / p.x = (p.x * p.y) / p.x := congrArg (fun t => t / p.x) p.eqn.symm
        _ = p.y := Nat.mul_div_cancel_left _ p.hx
  right_inv d := by rfl

noncomputable instance (n : ℕ) : Fintype (Pair n) :=
  Fintype.ofEquiv ↥n.divisors (pairDivisor n).symm

lemma pair_card (n : ℕ) : Fintype.card (Pair n) = n.divisors.card := by
  simpa using Fintype.card_congr (pairDivisor n)

/-- Ordered decompositions into two positive products. -/
@[ext] structure Decomp (n : ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  w : ℕ
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  hw : 0 < w
  eqn : x * y + z * w = n

def decompPairs (n : ℕ) :
    Decomp n ≃ Σ t : ↥(Icc 1 (n-1)), Pair t.val × Pair (n-t.val) where
  toFun p := by
    have hxy := Nat.mul_pos p.hx p.hy
    have hzw := Nat.mul_pos p.hz p.hw
    have he := p.eqn
    refine ⟨⟨p.x*p.y, mem_Icc.mpr (by omega)⟩,
      ⟨⟨p.x,p.y,p.hx,p.hy,rfl⟩,
       ⟨p.z,p.w,p.hz,p.hw,by change p.z*p.w = n-p.x*p.y; omega⟩⟩⟩
  invFun p := {
    x := p.2.1.x, y := p.2.1.y, z := p.2.2.x, w := p.2.2.y
    hx := p.2.1.hx, hy := p.2.1.hy, hz := p.2.2.hx, hw := p.2.2.hy
    eqn := by
      have := mem_Icc.mp p.1.property
      rw [p.2.1.eqn, p.2.2.eqn]
      omega }
  left_inv p := by rfl
  right_inv p := by
    rcases p with ⟨⟨t,ht⟩,a,b⟩
    have ha := a.eqn
    cases a with | mk x y hx hy he =>
      dsimp at he
      subst t
      rfl

noncomputable instance (n : ℕ) : Fintype (Decomp n) :=
  Fintype.ofEquiv (Σ t : ↥(Icc 1 (n-1)), Pair t.val × Pair (n-t.val)) (decompPairs n).symm

def convolution (n : ℕ) : ℕ :=
  ∑ t ∈ Icc 1 (n-1), t.divisors.card * (n-t).divisors.card

lemma decomp_card (n : ℕ) : Fintype.card (Decomp n) = convolution n := by
  rw [Fintype.card_congr (decompPairs n), Fintype.card_sigma]
  simp only [Fintype.card_prod, pair_card]
  exact sum_coe_sort (Icc 1 (n-1)) (fun t => t.divisors.card * (n-t).divisors.card)

def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

def zeroBoundary (n : ℕ) :
    {o : Orphan n // o.c = 0} ≃ Σ b : ↥n.divisors, Fin b.val where
  toFun o := by
    have he : o.val.a * o.val.b = n := by simpa [o.property] using o.val.det
    have ha : 0 < o.val.a := by have := o.val.ca; omega
    have hb : 0 < o.val.b := by have := o.val.db; omega
    refine ⟨⟨o.val.b, Nat.mem_divisors.mpr ⟨?_, ?_⟩⟩, ⟨o.val.d, o.val.db⟩⟩
    · exact ⟨o.val.a, by nlinarith [he]⟩
    · have := Nat.mul_pos ha hb; omega
  invFun p := ⟨{
    a := n / p.1.val
    b := p.1.val
    c := 0
    d := p.2.val
    ca := Nat.div_pos (Nat.divisor_le p.1.property) (Nat.pos_of_mem_divisors p.1.property)
    db := p.2.isLt
    det := by simpa using Nat.div_mul_cancel (Nat.dvd_of_mem_divisors p.1.property)
  }, rfl⟩
  left_inv o := by
    apply Subtype.ext
    apply Orphan.ext
    · change n / o.val.b = o.val.a
      have he : o.val.a * o.val.b = n := by simpa [o.property] using o.val.det
      have hb : 0 < o.val.b := by have := o.val.db; omega
      calc
        n / o.val.b = (o.val.a * o.val.b) / o.val.b :=
          congrArg (fun t => t / o.val.b) he.symm
        _ = o.val.a := Nat.mul_div_cancel _ hb
    · rfl
    · exact o.property.symm
    · rfl
  right_inv p := by rfl

lemma zeroBoundary_card (n : ℕ) :
    Fintype.card {o : Orphan n // o.c = 0} = sigma n := by
  rw [Fintype.card_congr (zeroBoundary n), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact sum_coe_sort n.divisors (fun t => t)

def positiveInterior (n : ℕ) :
    {o : Orphan n // 0 < o.c} ≃ {p : Decomp n // p.w ≤ p.y} where
  toFun o := ⟨{
    x := o.val.a - o.val.c
    y := o.val.b
    z := o.val.c
    w := o.val.b - o.val.d
    hx := Nat.sub_pos_of_lt o.val.ca
    hy := lt_of_le_of_lt (Nat.zero_le _) o.val.db
    hz := o.property
    hw := Nat.sub_pos_of_lt o.val.db
    eqn := by
      rw [Nat.sub_mul, Nat.mul_sub]
      have h1 := Nat.mul_le_mul_right o.val.b (Nat.le_of_lt o.val.ca)
      have h2 := Nat.mul_le_mul_left o.val.c (Nat.le_of_lt o.val.db)
      have he := o.val.det
      omega
  }, Nat.sub_le _ _⟩
  invFun p := ⟨{
    a := p.val.x + p.val.z
    b := p.val.y
    c := p.val.z
    d := p.val.y - p.val.w
    ca := by have := p.val.hx; omega
    db := by have := p.val.hw; have := p.val.hy; omega
    det := by
      rw [Nat.add_mul, Nat.mul_sub]
      have h := Nat.mul_le_mul_left p.val.z p.property
      have he := p.val.eqn
      omega
  }, p.val.hz⟩
  left_inv o := by
    apply Subtype.ext
    apply Orphan.ext
    · dsimp
      exact Nat.sub_add_cancel (Nat.le_of_lt o.val.ca)
    · rfl
    · rfl
    · dsimp
      exact Nat.sub_sub_self (Nat.le_of_lt o.val.db)
  right_inv p := by
    apply Subtype.ext
    apply Decomp.ext
    · dsimp; omega
    · rfl
    · rfl
    · dsimp
      exact Nat.sub_sub_self p.property

lemma split_card {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    Fintype.card α = Fintype.card {x // P x} + Fintype.card {x // ¬ P x} := by
  simpa only [Fintype.card_sum] using (Fintype.card_congr (Equiv.sumCompl P)).symm

lemma orphan_card (n : ℕ) :
    orphanCount n = sigma n + Fintype.card {p : Decomp n // p.w ≤ p.y} := by
  classical
  have h := split_card (fun o : Orphan n => o.c = 0)
  have hne : Fintype.card {o : Orphan n // ¬ o.c = 0} =
      Fintype.card {o : Orphan n // 0 < o.c} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun o => Nat.pos_iff_ne_zero.symm)
  rw [hne, Fintype.card_congr (positiveInterior n), zeroBoundary_card] at h
  exact h

def decompSwap (n : ℕ) : Decomp n ≃ Decomp n where
  toFun p := {
    x := p.z, y := p.w, z := p.x, w := p.y
    hx := p.hz, hy := p.hw, hz := p.hx, hw := p.hy
    eqn := by simpa only [add_comm] using p.eqn }
  invFun p := {
    x := p.z, y := p.w, z := p.x, w := p.y
    hx := p.hz, hy := p.hw, hz := p.hx, hw := p.hy
    eqn := by simpa only [add_comm] using p.eqn }
  left_inv p := by rfl
  right_inv p := by rfl

def strictSwap (n : ℕ) :
    {p : Decomp n // p.y < p.w} ≃ {p : Decomp n // p.w < p.y} where
  toFun p := ⟨decompSwap n p.val, p.property⟩
  invFun p := ⟨decompSwap n p.val, p.property⟩
  left_inv p := by rfl
  right_inv p := by rfl

lemma half_card (n : ℕ) :
    2 * Fintype.card {p : Decomp n // p.w ≤ p.y} =
      Fintype.card (Decomp n) + Fintype.card {p : Decomp n // p.w = p.y} := by
  classical
  have ha := split_card (fun p : Decomp n => p.w ≤ p.y)
  have hb := split_card (fun p : {p : Decomp n // p.w ≤ p.y} => p.val.w = p.val.y)
  have hlt : Fintype.card {p : Decomp n // ¬ p.w ≤ p.y} =
      Fintype.card {p : Decomp n // p.w < p.y} := by
    calc
      _ = Fintype.card {p : Decomp n // p.y < p.w} :=
        Fintype.card_congr (Equiv.subtypeEquivRight (fun p => Nat.not_le))
      _ = _ := Fintype.card_congr (strictSwap n)
  have heq : Fintype.card {p : {p : Decomp n // p.w ≤ p.y} // p.val.w = p.val.y} =
      Fintype.card {p : Decomp n // p.w = p.y} := by
    apply Fintype.card_congr
    exact Equiv.subtypeSubtypeEquivSubtype
      (p := fun p : Decomp n => p.w ≤ p.y) (q := fun p => p.w = p.y)
      (fun {_} h => Nat.le_of_eq h)
  have hne : Fintype.card {p : {p : Decomp n // p.w ≤ p.y} // ¬ p.val.w = p.val.y} =
      Fintype.card {p : Decomp n // p.w < p.y} := by
    apply Fintype.card_congr
    exact (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun p : Decomp n => p.w ≤ p.y) (fun p => ¬ p.w = p.y)).trans
        (Equiv.subtypeEquivRight (fun p => by omega))
  rw [hlt] at ha
  rw [heq,hne] at hb
  omega

def equalProducts (n : ℕ) :
    {p : Decomp n // p.w = p.y} ≃ Σ d : ↥n.divisors, Fin (d.val-1) where
  toFun p := by
    have he : (p.val.x+p.val.z)*p.val.y = n := by
      rw [Nat.add_mul]
      simpa [p.property] using p.val.eqn
    have hsum : 0 < p.val.x+p.val.z := by have := p.val.hx; omega
    refine ⟨⟨p.val.x+p.val.z, Nat.mem_divisors.mpr ⟨⟨p.val.y,he.symm⟩,?_⟩⟩,
      ⟨p.val.x-1,?_⟩⟩
    · have := Nat.mul_pos hsum p.val.hy; omega
    · have := p.val.hx; have := p.val.hz
      change p.val.x-1 < p.val.x+p.val.z-1
      omega
  invFun p := ⟨{
    x := p.2.val+1
    y := n/p.1.val
    z := p.1.val-(p.2.val+1)
    w := n/p.1.val
    hx := by omega
    hy := Nat.div_pos (Nat.divisor_le p.1.property) (Nat.pos_of_mem_divisors p.1.property)
    hz := by have := p.2.isLt; omega
    hw := Nat.div_pos (Nat.divisor_le p.1.property) (Nat.pos_of_mem_divisors p.1.property)
    eqn := by
      rw [← Nat.add_mul, Nat.add_sub_of_le (by have := p.2.isLt; omega)]
      exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors p.1.property)
  }, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Decomp.ext
    · dsimp; have := p.val.hx; omega
    · change n/(p.val.x+p.val.z) = p.val.y
      have he : (p.val.x+p.val.z)*p.val.y = n := by
        rw [Nat.add_mul]; simpa [p.property] using p.val.eqn
      have hp : 0 < p.val.x+p.val.z := by have := p.val.hx; omega
      calc
        n/(p.val.x+p.val.z) = ((p.val.x+p.val.z)*p.val.y)/(p.val.x+p.val.z) :=
          congrArg (fun t => t/(p.val.x+p.val.z)) he.symm
        _ = p.val.y := Nat.mul_div_cancel_left _ hp
    · dsimp; have := p.val.hx; omega
    · change n/(p.val.x+p.val.z) = p.val.w
      have he : (p.val.x+p.val.z)*p.val.w = n := by
        rw [Nat.add_mul]; simpa [p.property] using p.val.eqn
      have hp : 0 < p.val.x+p.val.z := by have := p.val.hx; omega
      calc
        n/(p.val.x+p.val.z) = ((p.val.x+p.val.z)*p.val.w)/(p.val.x+p.val.z) :=
          congrArg (fun t => t/(p.val.x+p.val.z)) he.symm
        _ = p.val.w := Nat.mul_div_cancel_left _ hp
  right_inv p := by
    rcases p with ⟨⟨d,hd⟩,⟨i,hi⟩⟩
    dsimp at hi
    dsimp
    have he : i+1+(d-(i+1))=d := by omega
    apply Sigma.ext
    · exact Subtype.ext he
    · exact (Fin.heq_ext_iff (congrArg (fun t => t-1) he)).mpr rfl

lemma equal_card (n : ℕ) :
    Fintype.card {p : Decomp n // p.w = p.y} + n.divisors.card = sigma n := by
  classical
  rw [Fintype.card_congr (equalProducts n), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [sum_coe_sort n.divisors (fun d : ℕ => d-1)]
  have hs : (∑ d ∈ n.divisors, (d-1)) + (∑ _d ∈ n.divisors, 1) =
      ∑ d ∈ n.divisors, d := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro d hd
    have := Nat.pos_of_mem_divisors hd
    omega
  simpa [sigma] using hs

/-- The literal orphan count, expressed through two divisor statistics. -/
theorem orphan_formula (n : ℕ) :
    2 * orphanCount n + n.divisors.card = convolution n + 3 * sigma n := by
  have h1 := orphan_card n
  have h2 := half_card n
  have h3 := equal_card n
  have h4 := decomp_card n
  omega

#print axioms orphan_formula

end Nathanson
