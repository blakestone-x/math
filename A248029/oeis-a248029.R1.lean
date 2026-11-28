import OMAStatements.S_oeis_a248029

/-!
# Sun's A248029 divisibility conjecture

Write σ(n) for the sum of the divisors of n. A divisor d of σ(n) in (n,2n]
immediately gives the witness m=d−n. The main step constructs such a divisor
when n is any nonabundant base times a coprime odd squarefree integer.
For n=2^a*u with u odd, an interval divisor d of σ(u) with d−u≥2 also
lifts to a witness: 2^a divides φ(2^a*(d−u)). This covers every nonabundant
odd part, including the prime and unit cases. Finally, any divisor d of
2σ(n) with n+2<d≤2n works because φ(d−n) is even.
-/

namespace OMA.R_oeis_a248029_R1

private lemma nonabundant {b : ℕ} (hs : (∑ j ∈ b.divisors, j) ≤ 2*b) :
    (∃ d : ℕ, d ∣ (∑ j ∈ b.divisors, j) ∧ b ≤ d ∧ d ≤ 2*b ∧ (1 < b → b < d)) := by
  have ge : b ≤ (∑ j ∈ b.divisors, j) := by simp [Nat.sum_divisors_eq_sum_properDivisors_add_self]
  refine ⟨(∑ j ∈ b.divisors, j),dvd_refl _,ge,hs,?_⟩
  intro h
  have one := Finset.single_le_sum (f := fun d : ℕ => d) (fun _ _ => Nat.zero_le _)
    (Nat.one_mem_properDivisors_iff_one_lt.mpr h)
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

private lemma multiply_odd_prime {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (odd : Odd p)
    (hc : p.Coprime n)
    (prev : (∃ d : ℕ, d ∣ (∑ j ∈ n.divisors, j) ∧ n ≤ d ∧ d ≤ 2*n ∧ (1 < n → n < d))) :
    (∃ d : ℕ, d ∣ (∑ j ∈ (p*n).divisors, j) ∧ (p*n) ≤ d ∧ d ≤ 2*(p*n) ∧ (1 < (p*n) → (p*n) < d)) := by
  obtain ⟨d, hd, lower, upper, _⟩ := prev
  have sumP : (∑ j ∈ p.divisors, j) = p+1 := by
    rw [hp.divisors]
    simp [hp.ne_one.symm, Nat.add_comm]
  have prod : (∑ j ∈ (p*n).divisors, j) = (p+1)*(∑ j ∈ n.divisors, j) := by
    rw [← sumP]
    exact hc.sum_divisors_mul
  have div : (p+1)*d ∣ (∑ j ∈ (p*n).divisors, j) := by rw [prod]; exact Nat.mul_dvd_mul_left _ hd
  have pOne : 1 < p := hp.one_lt
  have lo : p*n < (p+1)*d := by nlinarith [Nat.mul_le_mul_left p lower]
  by_cases fits : (p+1)*d ≤ 2*(p*n)
  · exact ⟨(p+1)*d,div,lo.le,fits,fun _ => lo⟩
  · obtain ⟨k, hk⟩ := odd
    have eq : (p+1)*d = 2*((k+1)*d) := by rw [hk]; ring
    have bounded := Nat.mul_le_mul (show k+1 ≤ p by omega) upper
    refine ⟨(k+1)*d, dvd_trans ⟨2,by rw [eq]; ring⟩ div, ?_, ?_, ?_⟩
    · omega
    · nlinarith only [bounded]
    · intro; omega

private lemma squarefree_extension (b : ℕ) (hb : 0 < b)
    (base : (∃ d : ℕ, d ∣ (∑ j ∈ b.divisors, j) ∧ b ≤ d ∧ d ≤ 2*b ∧ (1 < b → b < d))) (t : ℕ)
    (odd : Odd t) (sq : Squarefree t) (hc : t.Coprime b) :
    (∃ d : ℕ, d ∣ (∑ j ∈ (b*t).divisors, j) ∧ (b*t) ≤ d ∧ d ≤ 2*(b*t) ∧ (1 < (b*t) → (b*t) < d)) := by
  induction t using induction_on_primes with
  | zero => simp at odd
  | one => simpa using base
  | prime_mul p a hp ih =>
    obtain ⟨op,oa⟩ := Nat.odd_mul.mp odd
    obtain ⟨cpa,_,sa⟩ := Nat.squarefree_mul_iff.mp sq
    obtain ⟨cpb,cab⟩ := Nat.coprime_mul_iff_left.mp hc
    have prev := ih oa sa cab
    have pos : 0 < b*a := Nat.mul_pos hb (Nat.pos_of_ne_zero sa.ne_zero)
    have lifted := multiply_odd_prime pos hp op (Nat.coprime_mul_iff_right.mpr ⟨cpb,cpa⟩) prev
    simpa only [Nat.mul_left_comm] using lifted

private lemma witness {n : ℕ} (hn : 1 < n) (hit : (∃ d : ℕ, d ∣ (∑ j ∈ n.divisors, j) ∧ n ≤ d ∧ d ≤ 2*n ∧ (1 < n → n < d))) :
    ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ (m+n) ∣ Nat.totient m * (∑ j ∈ n.divisors, j) := by
  obtain ⟨d, hd, ge, le, more⟩ := hit
  refine ⟨d-n,by have := more hn; omega,by omega,?_⟩
  rw [Nat.sub_add_cancel ge]
  exact dvd_mul_of_dvd_right hd _

private lemma two_power_totient (a k : ℕ) (hk : 1 < k) :
    2^a ∣ (2^a*k).totient := by
  cases a with
  | zero => simp
  | succ a =>
    induction a with
    | zero =>
      simp only [zero_add,pow_one]
      exact (Nat.totient_even (show 2 < 2*k by omega)).two_dvd
    | succ a ih =>
      have even : Even (2^(a+1)*k) := by
        rw [pow_succ']; exact ⟨2^a*k,by ring⟩
      rw [pow_succ' 2 (a+1),Nat.mul_assoc,Nat.totient_two_mul_of_even even]
      exact Nat.mul_dvd_mul_left _ ih

private lemma two_power_nonabundant (a : ℕ) : (∑ j ∈ (2^a).divisors, j) ≤ 2*2^a := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  have eq : (∑ i ∈ Finset.range (a+1), (2:ℕ)^i) + 1 = 2*2^a := by
    induction a with
    | zero => decide
    | succ a ih => rw [Finset.sum_range_succ, pow_succ]; omega
  omega

private lemma lift_divisor {a u d : ℕ} (ho : Odd u) (hd : d ∣ (∑ j ∈ u.divisors, j))
    (gap : u+1 < d) (bound : d ≤ 2*u) :
    ∃ m : ℕ, 0 < m ∧ m ≤ 2^a*u ∧ (m+2^a*u) ∣ Nat.totient m * (∑ j ∈ (2^a*u).divisors, j) := by
  let k := d-u
  have more : 1 < k := by dsimp [k]; omega
  have le : k ≤ u := by dsimp [k]; omega
  have sum : k+u = d := Nat.sub_add_cancel (by omega)
  have hc : (2^a).Coprime u := ho.coprime_two_left.pow_left _
  have prod : (∑ j ∈ (2^a*u).divisors, j) = (∑ j ∈ (2^a).divisors, j) * (∑ j ∈ u.divisors, j) := hc.sum_divisors_mul
  refine ⟨2^a*k,Nat.mul_pos (Nat.two_pow_pos a) (by omega),Nat.mul_le_mul_left _ le,?_⟩
  rw [← Nat.mul_add, sum]
  refine Nat.mul_dvd_mul (two_power_totient a k more) ?_
  rw [prod]
  exact dvd_mul_of_dvd_right hd _

private lemma odd_part_witness (a b : ℕ) (ho : Odd b) (hn : 1 < 2^a*b)
    (hs : (∑ j ∈ b.divisors, j) ≤ 2*b) :
    ∃ m : ℕ, 0 < m ∧ m ≤ 2^a*b ∧ (m+2^a*b) ∣ Nat.totient m * (∑ j ∈ (2^a*b).divisors, j) := by
  have ha : 0 < (2:ℕ)^a := Nat.two_pow_pos a
  have hc : (2^a).Coprime b := ho.coprime_two_left.pow_left _
  have base := nonabundant (two_power_nonabundant a)
  by_cases hb : 1 < b
  · by_cases prime : b.Prime
    · exact witness hn (squarefree_extension (2^a) ha base b ho prime.squarefree hc.symm)
    · let k := ∑ d ∈ b.properDivisors, d
      have ge : 1 ≤ k := Finset.single_le_sum (f := fun d : ℕ => d) (fun _ _ => Nat.zero_le _)
        (Nat.one_mem_properDivisors_iff_one_lt.mpr hb)
      have ne : k ≠ 1 := fun eq => prime (Nat.sum_properDivisors_eq_one_iff_prime.mp eq)
      have more : 1 < k := by omega
      have sum : (∑ j ∈ b.divisors, j) = k+b := Nat.sum_divisors_eq_sum_properDivisors_add_self
      exact lift_divisor (a := a) ho (dvd_refl ((∑ j ∈ b.divisors, j))) (by omega) hs
  · have eq : b = 1 := by obtain ⟨t,ht⟩ := ho; omega
    subst b
    simp only [Nat.mul_one] at hn ⊢
    exact witness hn base

/-- The residual problem for odd inputs. -/
def H1 : Prop := ∀ n : ℕ, 1 < n → Odd n →
    (∀ b t : ℕ, n = b*t → t.Coprime b → Odd t → Squarefree t → 2*b < (∑ j ∈ b.divisors, j)) ∧
    (∀ a u : ℕ, n = 2^a*u → Odd u → 2*u < (∑ j ∈ u.divisors, j)) ∧
    (∀ a u d : ℕ, n = 2^a*u → Odd u → d ∣ (∑ j ∈ u.divisors, j) → u+1 < d → 2*u < d) ∧
    (∀ d : ℕ, d ∣ 2*(∑ j ∈ n.divisors, j) → n+2 < d → 2*n < d) →
    ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ (m+n) ∣ Nat.totient m * (∑ j ∈ n.divisors, j)

/-- The residual problem for even inputs. -/
def H2 : Prop := ∀ n : ℕ, 1 < n → Even n →
    (∀ b t : ℕ, n = b*t → t.Coprime b → Odd t → Squarefree t → 2*b < (∑ j ∈ b.divisors, j)) ∧
    (∀ a u : ℕ, n = 2^a*u → Odd u → 2*u < (∑ j ∈ u.divisors, j)) ∧
    (∀ a u d : ℕ, n = 2^a*u → Odd u → d ∣ (∑ j ∈ u.divisors, j) → u+1 < d → 2*u < d) ∧
    (∀ d : ℕ, d ∣ 2*(∑ j ∈ n.divisors, j) → n+2 < d → 2*n < d) →
    ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ (m+n) ∣ Nat.totient m * (∑ j ∈ n.divisors, j)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a248029.main := by
  intro odd_case even_case n hn
  by_cases hit : ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ (m+n) ∣ Nat.totient m * (∑ j ∈ n.divisors, j)
  · exact hit
  have left : (∀ b t : ℕ, n = b*t → t.Coprime b → Odd t → Squarefree t → 2*b < (∑ j ∈ b.divisors, j)) ∧
    (∀ a u : ℕ, n = 2^a*u → Odd u → 2*u < (∑ j ∈ u.divisors, j)) ∧
    (∀ a u d : ℕ, n = 2^a*u → Odd u → d ∣ (∑ j ∈ u.divisors, j) → u+1 < d → 2*u < d) ∧
    (∀ d : ℕ, d ∣ 2*(∑ j ∈ n.divisors, j) → n+2 < d → 2*n < d) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro b t eq hc ho hs
      subst n
      by_contra! le
      have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      exact hit (witness hn (squarefree_extension b hb (nonabundant le) t ho hs hc))
    · intro a u eq ho
      subst n
      by_contra! le
      exact hit (odd_part_witness a u ho hn le)
    · intro a u d eq ho hd gap
      subst n
      by_contra! le
      exact hit (lift_divisor ho hd gap le)
    · intro d hd gap
      by_contra! le
      apply hit
      refine ⟨d-n,by omega,by omega,?_⟩
      rw [Nat.sub_add_cancel (by omega : n ≤ d)]
      exact hd.trans (Nat.mul_dvd_mul_right (Nat.totient_even (by omega : 2 < d-n)).two_dvd _)
  rcases Nat.even_or_odd n with he | ho
  · exact even_case n hn he left
  · exact odd_case n hn ho left

end OMA.R_oeis_a248029_R1
