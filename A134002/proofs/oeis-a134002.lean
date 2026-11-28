import OMAStatements.S_oeis_a134002
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Layman's positivity conjecture

Credit: @blakestone-x (agent: Codex, model: GPT-6)
Source: https://oeis.org/A134002

All prime factors of the norm are one modulo four. If the norm is composite,
Fermat's two-square theorem and the product identity yield two different
representations. An alternate representation gives positive solutions after
completing squares. Jacobi's classical two-square theorem also gives the
exact number of ordered positive solutions as the divisor count minus two.
-/

private theorem layman_split (n p : ℕ) (hp : p.Prime) (hd : p ∣ n^2 + (n+5)^2) : p % 4 = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have htwo : p ≠ 2 := by
    rintro rfl
    have h := Nat.mod_eq_zero_of_dvd hd
    rw [Nat.add_mod, Nat.pow_mod, Nat.pow_mod (n+5), Nat.add_mod n 5] at h
    have hh : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hh with h0 | h1 <;> simp [*] at h
  obtain ⟨k,hk⟩ := hp.odd_of_ne_two htwo
  by_contra hgoal
  have h3 : p % 4 = 3 := by omega
  have hzero := (ZMod.natCast_eq_zero_iff _ p).mpr hd
  push_cast at hzero
  have hs : (n : ZMod p)^2 = -((n : ZMod p)+5)^2 := eq_neg_of_add_eq_zero_left hzero
  have hx : (n : ZMod p) = 0 := by
    by_contra h
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq h hs h3
  have hy : (n : ZMod p) + 5 = 0 := by
    by_contra h
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' h hs h3
  have h5 : (5 : ZMod p) = 0 := by simpa [hx] using hy
  have hd5 : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp h5
  have hp5 : p = 5 := (Nat.dvd_prime_two_le (by decide : Nat.Prime 5) hp.two_le).mp hd5
  omega

private theorem layman_composite_factors (m : ℕ) (hm : 1 < m) (h : ¬ m.Prime) :
    ∃ p q : ℕ, 1 < p ∧ 1 < q ∧ m = p*q := by
  obtain ⟨p,q,hp,hq,he⟩ := (Nat.not_prime_iff_exists_mul_eq hm).mp h
  refine ⟨p,q,?_,?_,he.symm⟩
  · by_contra! hh
    interval_cases p <;> simp_all
  · by_contra! hh
    interval_cases q <;> simp_all

private theorem order_split_rep {m x y : ℕ} (hs : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 1)
    (hx : 0 < x) (hy : 0 < y) (he : m = x^2 + y^2) :
    ∃ a b : ℕ, 0 < a ∧ a < b ∧ m = a^2 + b^2 := by
  rcases lt_trichotomy x y with h | h | h
  · exact ⟨x,y,hx,h,he⟩
  · obtain rfl := h
    have dvd : 2 ∣ m := ⟨x^2, by omega⟩
    have f := hs 2 Nat.prime_two dvd
    omega
  · exact ⟨y,x,hy,h,he.trans (Nat.add_comm _ _)⟩

private theorem positive_rep_of_split (m : ℕ) (hm : 1 < m)
    (hs : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 1) :
    ∃ x y : ℕ, 0 < x ∧ x < y ∧ m = x^2 + y^2 := by
  induction m using induction_on_primes with
  | zero => omega
  | one => omega
  | prime_mul p m hp ih =>
    have hps := fun q (hq : Nat.Prime q) (hd : q ∣ p) =>
      hs q hq (dvd_trans hd (dvd_mul_right p m))
    have hp4 := hps p hp dvd_rfl
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x,y,hxy⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
    have hx : 0 < x := by
      by_contra! hz
      have hx0 : x = 0 := by omega
      rw [hx0] at hxy
      simp only [zero_pow (by decide : 2 ≠ 0), zero_add] at hxy
      exact Nat.Prime.not_prime_pow (by decide : 2 ≤ 2) (hxy.symm ▸ hp)
    have hy : 0 < y := by
      by_contra! hz
      have hy0 : y = 0 := by omega
      rw [hy0] at hxy
      simp only [zero_pow (by decide : 2 ≠ 0), add_zero] at hxy
      exact Nat.Prime.not_prime_pow (by decide : 2 ≤ 2) (hxy.symm ▸ hp)
    obtain ⟨a,b,ha,hab,hpab⟩ := order_split_rep hps hx hy hxy.symm
    by_cases hm1 : m = 1
    · subst m
      simpa using (show ∃ x y : ℕ, 0 < x ∧ x < y ∧ p = x^2+y^2 from
        ⟨a,b,ha,hab,hpab⟩)
    have hm0 : m ≠ 0 := by
      intro h
      simp [h] at hm
    obtain ⟨u,v,hu,huv,hmuv⟩ := ih (by omega) (fun q hq hd =>
      hs q hq (dvd_trans hd (dvd_mul_left m p)))
    have he : a*u < b*v := (Nat.mul_lt_mul_of_pos_right hab hu).trans
      (Nat.mul_lt_mul_of_pos_left huv (by omega))
    have ht := Nat.sub_add_cancel he.le
    apply order_split_rep hs (Nat.sub_pos_of_lt he)
      (show 0 < a*v+b*u from Nat.add_pos_left (Nat.mul_pos ha (by omega)) _)
    rw [hpab,hmuv]
    generalize b*v-a*u = t at ht ⊢
    zify at ht ⊢
    linear_combination -(↑b*↑v-↑a*↑u+↑t) * ht

private lemma layman_sorted (a b : ℕ) :
    (min a b)^2 + (max a b)^2 = a^2+b^2 := by
  rcases le_total a b with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right h, max_eq_left h, Nat.add_comm]

private lemma layman_two_products (n x y s t : ℕ)
    (hx : 0 < x) (hxy : x < y) (hs : 0 < s) (hst : s < t)
    (hm : n^2+(n+5)^2 = (x^2+y^2)*(s^2+t^2)) :
    ∃ u v : ℕ, u ≤ v ∧ (u,v) ≠ (n,n+5) ∧ u^2+v^2 = n^2+(n+5)^2 := by
  let A := y*t-x*s
  let B := x*t+y*s
  let C := x*s+y*t
  let D := max (x*t) (y*s) - min (x*t) (y*s)
  have hxs : x*s ≤ y*t := Nat.mul_le_mul hxy.le hst.le
  have hac : A < C := by
    dsimp [A,C]
    have : 0 < x*s := Nat.mul_pos hx hs
    omega
  have hbc : B < C := by
    let u := y-x
    let v := t-s
    have hu : y=x+u := by dsimp [u]; omega
    have hv : t=s+v := by dsimp [v]; omega
    have hp : 0 < u*v := Nat.mul_pos (by omega) (by omega)
    dsimp [B,C]
    rw [hu,hv]
    nlinarith
  have hfirst : A^2+B^2 = n^2+(n+5)^2 := by
    rw [hm]
    dsimp [A,B]
    zify [hxs]
    ring
  have hsecond : D^2+C^2 = n^2+(n+5)^2 := by
    rw [hm]
    dsimp [D,C]
    rcases le_total (x*t) (y*s) with h | h
    · rw [min_eq_left h,max_eq_right h]
      zify [h]
      ring
    · rw [min_eq_right h,max_eq_left h]
      zify [h]
      ring
  by_cases hc : C = n+5
  · refine ⟨min A B, max A B, le_trans (min_le_left _ _) (le_max_left _ _), ?_, ?_⟩
    · intro he
      have he' := congrArg Prod.snd he
      have : max A B < C := max_lt hac hbc
      change max A B = n+5 at he'
      omega
    · exact (layman_sorted A B).trans hfirst
  · have hdc : D ≤ C := by
      have hlt : x*t ≤ y*t := Nat.mul_le_mul_right _ hxy.le
      have hrt : y*s ≤ y*t := Nat.mul_le_mul_left _ hst.le
      have he : max (x*t) (y*s) ≤ y*t := max_le hlt hrt
      dsimp [D,C]
      omega
    exact ⟨D,C,hdc,fun he => hc (congrArg Prod.snd he),hsecond⟩

private lemma layman_sq_parity (x : ℕ) : x^2 % 2 = x % 2 := by
  rw [Nat.pow_mod]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h]

private lemma layman_sum_parity (x y : ℕ) : (x^2+y^2)%2 = (x+y)%2 := by
  rw [Nat.add_mod, layman_sq_parity, layman_sq_parity, ← Nat.add_mod]

private theorem layman_from_alternate (n u v : ℕ) (hn : 0 < n) (huv : u ≤ v)
    (hneq : (u,v) ≠ (n,n+5)) (he : u^2 + v^2 = n^2 + (n+5)^2) :
    ∃ a b : ℕ, 0<a ∧ 0<b ∧ n*(n+5)=a*(a+5)+b*(b+5) := by
  let d := v-u
  let s := v+u
  have hdv : v = u+d := by dsimp [d]; omega
  have hsv : s = 2*u+d := by dsimp [s]; omega
  have hp := congrArg (fun x : ℕ => x % 2) he
  change (u^2+v^2)%2 = (n^2+(n+5)^2)%2 at hp
  rw [layman_sum_parity, layman_sum_parity] at hp
  have hdp : d%2=1 := by omega
  have hsp : s%2=1 := by omega
  have hnorm : s^2+d^2 = (2*n+5)^2+25 := by
    rw [hdv] at he
    rw [hsv]
    nlinarith [he]
  have hbig : 5 < d := by
    by_contra! hsmall
    have hdle := Nat.pow_le_pow_left hsmall 2
    have hlo : 2*n+5 ≤ s := by
      by_contra! hh
      have hl := Nat.pow_lt_pow_left hh (by decide : 2≠0)
      nlinarith
    have hhi : s ≤ 2*n+5 := by
      by_contra! hh
      have hl : 2*n+7 ≤ s := by omega
      have hq := Nat.pow_le_pow_left hl 2
      nlinarith [hn]
    have hse : s = 2*n+5 := by omega
    have hde : d=5 := by
      by_contra! hd
      have hl := Nat.pow_lt_pow_left (show d<5 by omega) (by decide : 2≠0)
      rw [hse] at hnorm
      nlinarith
    exact hneq (Prod.ext (by dsimp; omega) (by dsimp; omega))
  let a := (d-5)/2
  let b := (s-5)/2
  have ha : 2*a+5=d := by dsimp [a]; omega
  have hb : 2*b+5=s := by dsimp [b]; omega
  refine ⟨a,b,by omega,by omega,?_⟩
  rw [← ha, ← hb] at hnorm
  nlinarith [hnorm]

theorem OMA.solution : type_of% @OMA.S_oeis_a134002.main := by
  intro n hn hnone
  by_contra h
  have hm : 1 < n^2+(n+5)^2 := by nlinarith
  obtain ⟨p,q,hp,hq,hpq⟩ := layman_composite_factors _ hm h
  have hs : ∀ r : ℕ, r.Prime → r ∣ p*q → r%4=1 := by
    rw [← hpq]
    exact layman_split n
  obtain ⟨x,y,hx,hxy,hrep⟩ := positive_rep_of_split p hp (fun r hr hd =>
    hs r hr (dvd_trans hd (dvd_mul_right p q)))
  obtain ⟨s,t,hsp,hst,href⟩ := positive_rep_of_split q hq (fun r hr hd =>
    hs r hr (dvd_trans hd (dvd_mul_left q p)))
  obtain ⟨u,v,huv,hneq,hu⟩ := layman_two_products n x y s t hx hxy hsp hst
    (by rw [hpq,hrep,href])
  exact hnone (layman_from_alternate n u v hn huv hneq hu)
