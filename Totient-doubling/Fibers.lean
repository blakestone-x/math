import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic

namespace TotientFibers
open Nat

def IsTotient (v : ℕ) := ∃ x : ℕ, x.totient=v

/-- Each even inverse is twice an odd inverse. The reverse matching on odd
    inverses is automatic from the odd doubling identity. -/
def Paired (v : ℕ) := 0<v ∧ IsTotient v ∧
  ∀ x : ℕ, x.totient=v → 2∣x → ∃ o, ¬2∣o ∧ x=2*o ∧ o.totient=v

theorem odd_double {a : ℕ} (ha : ¬2∣a) : (2*a).totient=a.totient := by
  simpa using totient_mul_of_prime_of_not_dvd prime_two ha

theorem even_double {a : ℕ} (ha : 2∣a) : (2*a).totient=2*a.totient :=
  totient_mul_of_prime_of_dvd prime_two ha

theorem even_inverse {v : ℕ} (hv : IsTotient v) : ∃ x, 2∣x ∧ x.totient=v := by
  obtain ⟨x,hx⟩ := hv
  by_cases e : 2∣x
  · exact ⟨x,e,hx⟩
  · exact ⟨2*x,dvd_mul_right _ _,(odd_double e).trans hx⟩

theorem doubling_closed {v : ℕ} (hv : IsTotient v) : IsTotient (2*v) := by
  obtain ⟨x,e,hx⟩ := even_inverse hv
  exact ⟨2*x,by rw [even_double e,hx]⟩

theorem criterion {v : ℕ} (hv : 0<v) :
    Paired v ↔ IsTotient v ∧ ¬∃ w, IsTotient w ∧ v=2*w := by
  constructor
  · rintro ⟨_,hit,matchAll⟩
    refine ⟨hit,?_⟩
    rintro ⟨w,hw,rfl⟩
    obtain ⟨x,xe,hx⟩ := even_inverse hw
    obtain ⟨o,odd,eq,_⟩ := matchAll (2*x) (by rw [even_double xe,hx]) (dvd_mul_right _ _)
    have eqo : x=o := by omega
    exact odd (eqo ▸ xe)
  · rintro ⟨hit,base⟩
    refine ⟨hv,hit,?_⟩
    rintro _ hx ⟨o,rfl⟩
    by_cases d : 2∣o
    · exact False.elim (base ⟨o.totient,⟨o,rfl⟩,by rw [←hx,even_double d]⟩)
    · exact ⟨o,d,rfl,(odd_double d).symm.trans hx⟩

theorem ray {s : ℕ} (hs : 0<s) (odd : ¬2∣s) (hit : ∃ a : ℕ, IsTotient (2^a*s)) :
    ∃ a : ℕ, (∀ j : ℕ, IsTotient (2^j*s) ↔ a≤j) ∧
      ∀ j : ℕ, Paired (2^j*s) ↔ j=a := by
  classical
  let a := Nat.find hit
  have start : IsTotient (2^a*s) := Nat.find_spec hit
  have classify (j : ℕ) : IsTotient (2^j*s) ↔ a≤j := by
    refine ⟨fun h => Nat.find_min' hit h,?_⟩
    intro hj
    obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hj
    clear hj
    induction t with
    | zero => simpa using start
    | succ t ih => simpa only [Nat.add_succ,pow_succ] using
        (show IsTotient ((2^(a+t)*2)*s) from by convert doubling_closed ih using 1; ring)
  refine ⟨a,classify,?_⟩
  intro j
  rw [criterion (by positivity)]
  constructor
  · rintro ⟨h,minimal⟩
    have le := (classify j).mp h
    by_cases eqj : j=a
    · exact eqj
    exfalso
    have prev : a≤j-1 := by omega
    have eq : j=(j-1)+1 := by omega
    apply minimal ⟨2^(j-1)*s,(classify _).mpr prev,?_⟩
    conv_lhs => rw [eq,pow_succ]
    ring
  · intro eqj
    refine ⟨by rw [eqj]; exact start,?_⟩
    rintro ⟨w,hw,eq⟩
    cases j with
    | zero =>
      simp only [pow_zero,one_mul] at eq
      exact odd ⟨w,eq⟩
    | succ j =>
      rw [pow_succ] at eq
      have ew : 2^j*s=w := by nlinarith
      rw [←ew] at hw
      have := (classify j).mp hw; omega

/-- The bound makes direct enumeration of an entire positive fiber finite. -/
theorem inverse_bound (x : ℕ) : x≤2*x.totient^2 ∧ (¬2∣x → x≤x.totient^2) := by
  induction x using Nat.recOnPosPrimePosCoprime with
  | hp p n pp hn =>
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [totient_prime_pow_succ pp,pow_succ]
    have pos : 0<p^j := pow_pos pp.pos _
    have sq : p^j≤(p^j)^2 := by nlinarith [Nat.mul_le_mul_left (p^j) (show 1≤p^j by omega)]
    by_cases e : p=2
    · subst p
      norm_num
      nlinarith
    have primeLo := pp.two_le
    have pbound : p≤(p-1)^2 := by
      have sub : p=(p-1)+1 := by omega
      nlinarith [Nat.mul_le_mul (show 2≤p-1 by omega) (show 2≤p-1 by omega),
        Nat.mul_le_mul_left (p-1) (show 2≤p-1 by omega)]
    have good := Nat.mul_le_mul sq pbound
    constructor <;> intros <;> nlinarith
  | h0 => simp
  | h1 => simp
  | h a b _ _ cop ia ib =>
    rw [totient_mul cop]
    have oneOdd : (¬2∣a) ∨ (¬2∣b) := by
      by_cases da : 2∣a
      · exact .inr (fun db => prime_two.not_dvd_one (cop ▸ Nat.dvd_gcd da db))
      · exact .inl da
    constructor
    · rcases oneOdd with ha | hb
      · have := Nat.mul_le_mul (ia.2 ha) ib.1; nlinarith
      · have := Nat.mul_le_mul ia.1 (ib.2 hb); nlinarith
    · intro h
      have ha : ¬2∣a := fun d => h (d.trans (dvd_mul_right _ _))
      have hb : ¬2∣b := fun d => h (d.trans (dvd_mul_left _ _))
      have := Nat.mul_le_mul (ia.2 ha) (ib.2 hb); nlinarith

theorem fiber_four (x : ℕ) : x.totient=4 ↔ x=5 ∨ x=8 ∨ x=10 ∨ x=12 := by
  have finite : ∀ i : Fin 33, i.val.totient=4 ↔ i.val=5 ∨ i.val=8 ∨ i.val=10 ∨ i.val=12 := by decide
  by_cases small : x<33
  · exact finite ⟨x,small⟩
  · have bound := (inverse_bound x).1
    constructor
    · intro e; rw [e] at bound; omega
    · omega

theorem four_unpaired : ¬Paired 4 := by
  rw [criterion (by decide)]
  push_neg
  exact fun _ => ⟨2,⟨3,by decide⟩,rfl⟩

#print axioms criterion
#print axioms ray
#print axioms inverse_bound
#print axioms fiber_four
#print axioms four_unpaired
end TotientFibers
