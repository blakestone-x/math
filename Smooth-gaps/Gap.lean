import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace SmoothGaps

/-- Zero is excluded. The signed partner of an endpoint is represented by its magnitude. -/
def Smooth (S : Finset ℕ) (n : ℕ) : Prop := n ≠ 0 ∧ n.primeFactors ⊆ S

instance (S : Finset ℕ) (n : ℕ) : Decidable (Smooth S n) :=
  inferInstanceAs (Decidable (n ≠ 0 ∧ n.primeFactors ⊆ S))

theorem Smooth.of_dvd {S : Finset ℕ} {a b : ℕ} (hb : Smooth S b) (hab : a ∣ b) :
    Smooth S a :=
  ⟨by rintro rfl; exact hb.1 (by simpa using hab),
   (Nat.primeFactors_mono hab hb.1).trans hb.2⟩

theorem Smooth.mul {S : Finset ℕ} {a b : ℕ} (ha : Smooth S a) (hb : Smooth S b) :
    Smooth S (a * b) := by
  refine ⟨mul_ne_zero ha.1 hb.1, ?_⟩
  rw [Nat.primeFactors_mul ha.1 hb.1]
  exact Finset.union_subset ha.2 hb.2

theorem smooth_prime {S : Finset ℕ} {p : ℕ} (hp : p.Prime) (hm : p ∈ S) :
    Smooth S p := by
  exact ⟨hp.ne_zero, by simpa [hp.primeFactors] using hm⟩

theorem Smooth.pow {S : Finset ℕ} {m : ℕ} (hm : Smooth S m) (j : ℕ) :
    Smooth S (m^j) := by
  induction j with
  | zero => simp [Smooth]
  | succ j ih => simpa [pow_succ] using ih.mul hm

/-- The possible positive endpoints in the OEIS signed convention. -/
def Attains (S : Finset ℕ) (n x : ℕ) : Prop :=
  Smooth S x ∧ ∃ y, Smooth S y ∧ (x = n + y ∨ n = x + y)

/-- A primitive row before taking the maximum. Both orientations of a sum are allowed. -/
def Primitive (S : Finset ℕ) (d u v : ℕ) : Prop :=
  0 < d ∧ Smooth S u ∧ Smooth S v ∧ Nat.Coprime u v ∧ (u = d + v ∨ d = u + v)

theorem attain_iff_scaled_primitive {S : Finset ℕ} {n x : ℕ} (hn : 0 < n) :
    Attains S n x ↔ ∃ g d u v, Smooth S g ∧ Primitive S d u v ∧ n = g*d ∧ x = g*u := by
  constructor
  · rintro ⟨hx, y, hy, hxy⟩
    let g := x.gcd y
    let u := x / g
    let v := y / g
    have gx : g ∣ x := Nat.gcd_dvd_left x y
    have gy : g ∣ y := Nat.gcd_dvd_right x y
    have hg := hx.of_dvd gx
    have hu : Smooth S u := hx.of_dvd (Nat.div_dvd_of_dvd gx)
    have hv : Smooth S v := hy.of_dvd (Nat.div_dvd_of_dvd gy)
    have hcop : Nat.Coprime u v := Nat.gcd_div_gcd_div_gcd_of_pos_left (Nat.pos_of_ne_zero hx.1)
    have ex : x = g*u := (Nat.mul_div_cancel' gx).symm
    have ey : y = g*v := (Nat.mul_div_cancel' gy).symm
    rcases hxy with h | h
    · have ng : n = g*(u-v) := by rw [Nat.mul_sub, ← ex, ← ey]; omega
      have lt : v < u := by
        by_contra! q
        simp [Nat.sub_eq_zero_of_le q] at ng
        omega
      exact ⟨g, u-v, u, v, hg, ⟨by omega, hu, hv, hcop, Or.inl (by omega)⟩, ng, ex⟩
    · exact ⟨g, u+v, u, v, hg,
        ⟨Nat.add_pos_left (Nat.pos_of_ne_zero hu.1) v, hu, hv, hcop, Or.inr rfl⟩,
        by rw [Nat.mul_add, ← ex, ← ey, h], ex⟩
  · rintro ⟨g, d, u, v, hg, ⟨_, hu, hv, _, h⟩, rfl, rfl⟩
    refine ⟨hg.mul hu, g*v, hg.mul hv, ?_⟩
    rcases h with h | h
    · exact Or.inl (by rw [h, Nat.mul_add])
    · exact Or.inr (by rw [h, Nat.mul_add])

def Complete (S : Finset ℕ) (rows : List (ℕ × ℕ)) : Prop :=
  ∀ a b, Smooth S a → Smooth S b → Smooth S (a+b) → Nat.Coprime a b →
    (a,b) ∈ rows ∨ (b,a) ∈ rows

/-- A value of zero is allowed when the attainable set is empty. -/
def HasValue (S : Finset ℕ) (n m : ℕ) : Prop :=
  (m = 0 ∨ Attains S n m) ∧ ∀ x, Attains S n x → x ≤ m

theorem smooth_gap_maximum {S : Finset ℕ} {rows : List (ℕ × ℕ)} {K h : ℕ}
    (full : Complete S rows)
    (bound : ∀ r ∈ rows, r.1 + r.2 ≤ K*r.1 ∧ r.1 + r.2 ≤ K*r.2)
    (hK : 1 ≤ K) (w : Attains S 1 K) (hh : Smooth S h) : HasValue S h (h*K) := by
  constructor
  · right
    rcases w with ⟨hk, y, hy, hrel⟩
    refine ⟨hh.mul hk, h*y, hh.mul hy, ?_⟩
    rcases hrel with he | he
    · left; calc
        h*K = h*(1+y) := congrArg (h * ·) he
        _ = h + h*y := by ring
    · right; calc
        h = h*1 := by simp
        _ = h*(K+y) := congrArg (h * ·) he
        _ = h*K + h*y := Nat.mul_add _ _ _
  · intro x hx
    obtain ⟨g, d, u, v, _, ⟨_, hu, hv, cp, rel⟩, en, ex⟩ :=
      (attain_iff_scaled_primitive (Nat.pos_of_ne_zero hh.1)).mp hx
    have hd : Smooth S d := hh.of_dvd ⟨g, by simpa [Nat.mul_comm] using en⟩
    have ub : u ≤ K*d := by
      rcases rel with e | e
      · subst u
        have cop : Nat.Coprime d v := by simpa using cp
        rcases full d v hd hv hu cop with hm | hm
        · exact (bound (d,v) hm).1
        · simpa [Nat.add_comm] using (bound (v,d) hm).2
      · calc
          u ≤ d := by omega
          _ = 1*d := by simp
          _ ≤ K*d := Nat.mul_le_mul_right d hK
    rw [ex, en]
    calc
      g*u ≤ g*(K*d) := Nat.mul_le_mul_left _ ub
      _ = g*d*K := by ring

theorem Smooth.mono {S T : Finset ℕ} {n : ℕ} (h : Smooth S n) (ht : S ⊆ T) :
    Smooth T n := ⟨h.1, h.2.trans ht⟩

theorem missing_prime_power {S : Finset ℕ} {rows : List (ℕ × ℕ)} {p e : ℕ}
    (hp : p.Prime) (outside : p ∉ S) (full : Complete (insert p S) rows)
    (avoid : ∀ r ∈ rows, ¬p^e ∣ r.1 ∧ ¬p^e ∣ r.2 ∧ ¬p^e ∣ r.1+r.2)
    (k : ℕ) {h : ℕ} (hh : Smooth S h) : HasValue S (p^(e+k)*h) 0 := by
  have incl : S ⊆ insert p S := Finset.subset_insert _ _
  have hpp : Smooth (insert p S) p := smooth_prime hp (Finset.mem_insert_self _ _)
  have hn := (hpp.pow (e+k)).mul (hh.mono incl)
  refine ⟨Or.inl rfl, ?_⟩
  intro x hx
  obtain ⟨g, d, u, v, hg, ⟨_, hu, hv, cp, rel⟩, en, _⟩ :=
    (attain_iff_scaled_primitive (Nat.pos_of_ne_zero hn.1)).mp hx
  have pg : Nat.Coprime p g := hp.coprime_iff_not_dvd.mpr fun pd =>
    outside (hg.2 (Nat.mem_primeFactors.mpr ⟨hp, pd, hg.1⟩))
  have mdiv : p^e ∣ g*d := ⟨p^k*h, by rw [← en, pow_add, Nat.mul_assoc]⟩
  have dd := (pg.pow_left e).dvd_of_dvd_mul_left mdiv
  have hd := hn.of_dvd (show d ∣ p^(e+k)*h from ⟨g, by simpa [Nat.mul_comm] using en⟩)
  exfalso
  rcases rel with rel | rel
  · subst u
    rcases full d v hd (hv.mono incl) (hu.mono incl) (by simpa using cp) with m | m
    · exact (avoid (d,v) m).1 dd
    · exact (avoid (v,d) m).2.1 dd
  · subst d
    rcases full u v (hu.mono incl) (hv.mono incl) hd cp with m | m
    · exact (avoid (u,v) m).2.2 dd
    · exact (avoid (v,u) m).2.2 (by simpa [Nat.add_comm] using dd)

end SmoothGaps
