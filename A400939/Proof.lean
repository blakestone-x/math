import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Prime division in the generalized halving Recamán walk

The original rule is A400939, with its divisor 2 replaced by a parameter k.
The zero index is an auxiliary value only: it is excluded from the visited set.
All theorems use the literal visited-value condition, including its asymmetry:
the addition branch may revisit a value.
-/

namespace PrimeDivisionRecaman

/-- The literal one-based walk. Index zero is an unused auxiliary zero. -/
def walk (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if n = 0 then 1
    else if k ∣ walk k n ∧
        (∀ i : Fin (n + 1), 0 < i.val → walk k i.val ≠ walk k n / k)
      then walk k n / k
      else walk k n + (n + 1)
termination_by n => n
decreasing_by all_goals omega

@[simp] theorem walk_one (k : ℕ) : walk k 1 = 1 := by
  rw [walk]; simp

/-- A natural-valued sequence obeys the exact source rule on positive indices. -/
def FollowsRule (k : ℕ) (a : ℕ → ℕ) : Prop := by
  classical
  exact a 1 = 1 ∧ ∀ n, 0 < n →
    a (n + 1) = if k ∣ a n ∧ (∀ i, 0 < i → i ≤ n → a i ≠ a n / k)
      then a n / k else a n + (n + 1)

/-- The branch condition for a division arriving at index d. -/
def DivisionAt (k : ℕ) (a : ℕ → ℕ) (d : ℕ) : Prop :=
  1 < d ∧ k ∣ a (d - 1) ∧
    ∀ i, 0 < i → i < d → a i ≠ a (d - 1) / k

theorem walk_followsRule (k : ℕ) : FollowsRule k (walk k) := by
  classical
  refine ⟨walk_one k, ?_⟩
  intro n hn
  rw [walk]
  simp only [Nat.ne_of_gt hn, ↓reduceIte]
  have h : (∀ i : Fin (n + 1), 0 < i.val → walk k i.val ≠ walk k n / k) ↔
      (∀ i, 0 < i → i ≤ n → walk k i ≠ walk k n / k) := by
    constructor
    · intro h i hi hin
      exact h ⟨i, by omega⟩ hi
    · intro h i hi
      exact h i.val hi (by omega)
  simp only [h]

/-- The standard triangular number, expressed recursively for transparent induction. -/
def triangle : ℕ → ℕ
  | 0 => 0
  | n + 1 => triangle n + (n + 1)

theorem two_mul_triangle (n : ℕ) : 2 * triangle n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [triangle]; nlinarith

@[simp] theorem triangle_one : triangle 1 = 1 := rfl

theorem triangle_strictMono : StrictMono triangle := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [triangle]
  omega

theorem no_consecutive_positive_triangles {u v t : ℕ} (hu : 0 < u) (_hv : 0 < v)
    (hut : triangle u = t) (hvt : triangle v = t + 1) : False := by
  have huv : u < v := by
    by_contra h
    have := triangle_strictMono.monotone (show v ≤ u by omega)
    omega
  have htu := two_mul_triangle u
  have htv := two_mul_triangle v
  rw [hut] at htu
  rw [hvt] at htv
  have : u + 1 ≤ v := by omega
  nlinarith

theorem prime_not_dvd_triangle {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hsmall : n + 1 < p) : ¬ p ∣ triangle n := by
  intro h
  have hm : p ∣ n * (n + 1) := by
    rw [← two_mul_triangle]
    exact dvd_mul_of_dvd_right h 2
  rcases hp.dvd_mul.mp hm with h | h
  · exact (Nat.not_dvd_of_pos_of_lt hn (by omega)) h
  · exact (Nat.not_dvd_of_pos_of_lt (by omega) hsmall) h

/-- No division can occur before index p in the walk with prime divisor p. -/
theorem prime_prefix {p : ℕ} (hp : p.Prime) {a : ℕ → ℕ} (ha : FollowsRule p a)
    {n : ℕ} (hn : 0 < n) (hsmall : n < p) : a n = triangle n := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · omega
    rcases n with _ | m
    · omega
    by_cases hm : m = 0
    · subst m; simpa using ha.1
    have hmpos : 0 < m := by omega
    have hpref : a m = triangle m := ih m (by omega) hmpos (by omega)
    have hnd : ¬ p ∣ a m := by
      rw [hpref]
      exact prime_not_dvd_triangle hp hmpos hsmall
    rw [ha.2 m hmpos, if_neg (by tauto), hpref, triangle]

/-- The first possible quotient and the second possible quotient cannot both
have already occurred in a positive triangular prefix. -/
theorem consecutive_quotients {p : ℕ} (hpodd : Odd p) :
    (p + 1) / 2 = (p - 1) / 2 + 1 := by
  obtain ⟨r, hr⟩ := hpodd
  omega

theorem triangle_before_prime {p : ℕ} (hpodd : Odd p) :
    triangle (p - 1) = p * ((p - 1) / 2) := by
  obtain ⟨r, hr⟩ := hpodd
  have h := two_mul_triangle (p - 1)
  have hdiv : (p - 1) / 2 = r := by omega
  rw [hdiv]
  have hsub : p - 1 = 2 * r := by omega
  rw [hsub] at h ⊢
  nlinarith

theorem triangle_at_prime {p : ℕ} (hpodd : Odd p) :
    triangle p = p * ((p + 1) / 2) := by
  obtain ⟨r, hr⟩ := hpodd
  have h := two_mul_triangle p
  have hdiv : (p + 1) / 2 = r + 1 := by omega
  rw [hdiv]
  nlinarith

/-- A triangular translate with doubled offset congruent to -1 can never
be divisible by p when 5 is a quadratic nonresidue modulo p. -/
theorem translate_not_dvd {p n v D : ℕ} (hfive : ¬ IsSquare (5 : ZMod p))
    (hD : (D : ZMod p) = 1) (h : 2 * v + D = n * (n + 1)) : ¬ p ∣ v := by
  intro hdvd
  have hz : (v : ZMod p) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd v p).2 hdvd
  have hc : (2 : ZMod p) * (v : ZMod p) + (D : ZMod p) =
      (n : ZMod p) * ((n : ZMod p) + 1) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      congrArg (fun x : ℕ => (x : ZMod p)) h
  rw [hz, hD] at hc
  apply hfive
  refine ⟨2 * (n : ZMod p) + 1, ?_⟩
  linear_combination 4 * hc

/-- Once such a translate is reached, all future steps take the addition branch. -/
theorem permanent_translate {p d D : ℕ} {a : ℕ → ℕ} (ha : FollowsRule p a)
    (hd : 0 < d) (hfive : ¬ IsSquare (5 : ZMod p)) (hD : (D : ZMod p) = 1)
    (hstart : 2 * a d + D = d * (d + 1)) :
    ∀ n, d ≤ n → 2 * a n + D = n * (n + 1) ∧
      ¬ p ∣ a n ∧ a (n + 1) = a n + (n + 1) := by
  classical
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    have hnd := translate_not_dvd hfive hD hstart
    refine ⟨hstart, hnd, ?_⟩
    rw [ha.2 d hd, if_neg (by tauto)]
  | succ n hdn ih =>
    have heq : 2 * a (n + 1) + D = (n + 1) * (n + 1 + 1) := by
      rw [ih.2.2]
      nlinarith [ih.1]
    have hnd := translate_not_dvd hfive hD heq
    refine ⟨heq, hnd, ?_⟩
    rw [ha.2 (n + 1) (by omega), if_neg (by tauto)]

/-- The initial dynamics for every odd prime: the first division occurs at p
or p+1, and the doubled triangular offset is then congruent to -1 modulo p. -/
theorem first_prime_division {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    {a : ℕ → ℕ} (ha : FollowsRule p a) :
    ∃ d D, (d = p ∧ D = p ^ 2 + 1 ∨ d = p + 1 ∧ D = (p + 1) ^ 2) ∧
      (∀ n, 0 < n → n < d → a n = triangle n) ∧ DivisionAt p a d ∧
      2 * a d + D = d * (d + 1) := by
  classical
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    obtain ⟨r, hr⟩ := hpodd
    omega
  let q := (p - 1) / 2
  have hprev : a (p - 1) = p * q := by
    rw [prime_prefix hp ha (by omega) (by omega), triangle_before_prime hpodd]
  have hdiv : p ∣ a (p - 1) := by rw [hprev]; exact dvd_mul_right p q
  have hquot : a (p - 1) / p = q := by rw [hprev, Nat.mul_div_right _ hp.pos]
  have hpstep := ha.2 (p - 1) (by omega)
  have hpidx : p - 1 + 1 = p := by omega
  rw [hpidx] at hpstep
  by_cases hfresh : ∀ i, 0 < i → i < p → a i ≠ q
  · have hcond : p ∣ a (p - 1) ∧
        ∀ i, 0 < i → i ≤ p - 1 → a i ≠ a (p - 1) / p := by
      refine ⟨hdiv, ?_⟩
      intro i hi hip
      rw [hquot]
      exact hfresh i hi (by omega)
    have hap : a p = q := by rw [hpstep, if_pos hcond, hquot]
    refine ⟨p, p ^ 2 + 1, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · exact fun n hn hnp => prime_prefix hp ha hn hnp
    · refine ⟨by omega, hdiv, ?_⟩
      intro i hi hip
      rw [hquot]
      exact hfresh i hi hip
    · obtain ⟨r, hr⟩ := hpodd
      have hq : q = r := by dsimp [q]; omega
      rw [hap, hq]
      nlinarith
  · push_neg at hfresh
    obtain ⟨j, hj, hjp, hjq⟩ := hfresh
    have hcond : ¬ (p ∣ a (p - 1) ∧
        ∀ i, 0 < i → i ≤ p - 1 → a i ≠ a (p - 1) / p) := by
      intro h
      exact h.2 j hj (by omega) (by rw [hquot]; exact hjq)
    have hap : a p = triangle p := by
      rw [hpstep, if_neg hcond,
        prime_prefix hp ha (by omega) (by omega)]
      have ht : triangle (p - 1 + 1) = triangle (p - 1) + (p - 1 + 1) := rfl
      simpa only [hpidx] using ht.symm
    have hall : ∀ i, 0 < i → i ≤ p → a i = triangle i := by
      intro i hi hip
      rcases lt_or_eq_of_le hip with hlt | heq
      · exact prime_prefix hp ha hi hlt
      · simpa only [heq] using hap
    have hqnext := consecutive_quotients hpodd
    have hnext : a p = p * (q + 1) := by
      rw [hap, triangle_at_prime hpodd, hqnext]
    have hnextquot : a p / p = q + 1 := by rw [hnext, Nat.mul_div_right _ hp.pos]
    have hfreshnext : ∀ i, 0 < i → i ≤ p → a i ≠ a p / p := by
      intro i hi hip heq
      have hjtri : triangle j = q := by rw [← hall j hj (by omega)]; exact hjq
      have hitri : triangle i = q + 1 := by rw [← hall i hi hip, heq, hnextquot]
      exact no_consecutive_positive_triangles hj hi hjtri hitri
    have hdivnext : p ∣ a p := by rw [hnext]; exact dvd_mul_right p (q + 1)
    have hapnext : a (p + 1) = q + 1 := by
      rw [ha.2 p (by omega), if_pos ⟨hdivnext, hfreshnext⟩, hnextquot]
    refine ⟨p + 1, (p + 1) ^ 2, Or.inr ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · exact fun n hn hnp => hall n hn (by omega)
    · refine ⟨by omega, ?_, ?_⟩
      · simpa using hdivnext
      · intro i hi hip
        simpa using hfreshnext i hi (by omega)
    · obtain ⟨r, hr⟩ := hpodd
      have hq : q = r := by dsimp [q]; omega
      rw [hapnext, hq]
      nlinarith

/-- An explicit criterion for which of the two possible first indices occurs.
The test involves only the finite triangular prefix, not the full walk history. -/
theorem division_at_prime_iff {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    {a : ℕ → ℕ} (ha : FollowsRule p a) :
    DivisionAt p a p ↔
      ¬ ∃ i, 0 < i ∧ i < p ∧ triangle i = (p - 1) / 2 := by
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    obtain ⟨r, hr⟩ := hpodd
    omega
  have hprev : a (p - 1) = p * ((p - 1) / 2) := by
    rw [prime_prefix hp ha (by omega) (by omega), triangle_before_prime hpodd]
  have hquot : a (p - 1) / p = (p - 1) / 2 := by
    rw [hprev, Nat.mul_div_right _ hp.pos]
  constructor
  · rintro hd ⟨i, hi, hip, htri⟩
    apply hd.2.2 i hi hip
    rw [hquot, prime_prefix hp ha hi hip, htri]
  · intro hn
    refine ⟨by omega, ?_, ?_⟩
    · rw [hprev]
      exact dvd_mul_right p ((p - 1) / 2)
    · intro i hi hip heq
      apply hn
      refine ⟨i, hi, hip, ?_⟩
      rw [← prime_prefix hp ha hi hip, heq, hquot]

theorem division_value {k d : ℕ} {a : ℕ → ℕ} (ha : FollowsRule k a)
    (hd : DivisionAt k a d) : a d = a (d - 1) / k := by
  classical
  have hstep := ha.2 (d - 1) (by have := hd.1; omega)
  have hidx : d - 1 + 1 = d := by have := hd.1; omega
  rw [hidx] at hstep
  rw [hstep, if_pos]
  refine ⟨hd.2.1, ?_⟩
  intro i hi hid
  exact hd.2.2 i hi (by omega)

theorem unique_division_from_tail {p d : ℕ} {a : ℕ → ℕ} (ha : FollowsRule p a)
    (hprefix : ∀ n, 0 < n → n < d → a n = triangle n)
    (hd : DivisionAt p a d) (htail : ∀ n, d ≤ n → ¬ p ∣ a n) :
    ∀ e, DivisionAt p a e ↔ e = d := by
  intro e
  constructor
  · intro he
    rcases lt_trichotomy e d with hlt | heq | hgt
    · have hepos := he.1
      have hv := division_value ha he
      have hle := Nat.div_le_self (a (e - 1)) p
      have hgrow := triangle_strictMono (show e - 1 < e by omega)
      rw [hprefix e (by omega) hlt,
          hprefix (e - 1) (by omega) (by omega)] at hv
      rw [hprefix (e - 1) (by omega) (by omega)] at hle
      omega
    · exact heq
    · exact False.elim (htail (e - 1) (by omega) he.2.1)
  · rintro rfl
    exact hd

/-- Full all-index classification for the odd-prime nonresidue family.

This is a partial result toward the generalized A400939 conjecture: it does
not assert the conclusion for every divisor that is not a power of two.
-/
theorem prime_nonsquare_classification {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hfive : ¬ IsSquare (5 : ZMod p)) {a : ℕ → ℕ} (ha : FollowsRule p a) :
    ∃ d D, (d = p ∧ D = p ^ 2 + 1 ∨ d = p + 1 ∧ D = (p + 1) ^ 2) ∧
      (∀ n, 0 < n → n < d → a n = triangle n) ∧
      (∀ e, DivisionAt p a e ↔ e = d) ∧
      (∀ n, d ≤ n → 2 * a n + D = n * (n + 1) ∧
        ¬ p ∣ a n ∧ a (n + 1) = a n + (n + 1)) := by
  obtain ⟨d, D, hcases, hprefix, hdiv, hstart⟩ := first_prime_division hp hpodd ha
  have hD : (D : ZMod p) = 1 := by
    rcases hcases with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  have ht := permanent_translate ha (by have := hdiv.1; omega) hfive hD hstart
  refine ⟨d, D, hcases, hprefix, ?_, ht⟩
  exact unique_division_from_tail ha hprefix hdiv (fun n hn => (ht n hn).2.1)

/-- The classification applies to the actual recursively defined source walk. -/
theorem walk_prime_nonsquare {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hfive : ¬ IsSquare (5 : ZMod p)) :
    ∃ d D, (d = p ∧ D = p ^ 2 + 1 ∨ d = p + 1 ∧ D = (p + 1) ^ 2) ∧
      (∀ n, 0 < n → n < d → walk p n = triangle n) ∧
      (∀ e, DivisionAt p (walk p) e ↔ e = d) ∧
      (∀ n, d ≤ n → 2 * walk p n + D = n * (n + 1) ∧
        ¬ p ∣ walk p n ∧ walk p (n + 1) = walk p n + (n + 1)) :=
  prime_nonsquare_classification hp hpodd hfive (walk_followsRule p)

/-- The relevant quadratic-nonresidue classes, using mathlib's quadratic
reciprocity theorem and the complete square table modulo five. -/
theorem five_nonsquare_of_mod_five {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : p % 5 = 2 ∨ p % 5 = 3) : ¬ IsSquare (5 : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro h
  have hr := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one
    (p := 5) (q := p) (by decide) hp2).mpr h
  rcases hmod with hm | hm
  · have hc : (p : ZMod 5) = 2 := by
      rw [← ZMod.natCast_mod p 5, hm]
      rfl
    rw [hc] at hr
    exact (show ¬ IsSquare (2 : ZMod 5) by decide) hr
  · have hc : (p : ZMod 5) = 3 := by
      rw [← ZMod.natCast_mod p 5, hm]
      rfl
    rw [hc] at hr
    exact (show ¬ IsSquare (3 : ZMod 5) by decide) hr

/-- Every odd prime p congruent to 2 or 3 modulo five has exactly one
division and an explicitly classified permanent triangular tail. -/
theorem walk_prime_residue_classes {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : p % 5 = 2 ∨ p % 5 = 3) :
    ∃ d D, (d = p ∧ D = p ^ 2 + 1 ∨ d = p + 1 ∧ D = (p + 1) ^ 2) ∧
      (∀ n, 0 < n → n < d → walk p n = triangle n) ∧
      (∀ e, DivisionAt p (walk p) e ↔ e = d) ∧
      (∀ n, d ≤ n → 2 * walk p n + D = n * (n + 1) ∧
        ¬ p ∣ walk p n ∧ walk p (n + 1) = walk p n + (n + 1)) :=
  walk_prime_nonsquare hp (hp.odd_of_ne_two hp2) (five_nonsquare_of_mod_five hp hp2 hmod)

/-- There are arbitrarily large prime divisors in the proved family.
Infinitude uses the existing, kernel-checked Dirichlet theorem in mathlib. -/
theorem arbitrarily_large_single_division (N : ℕ) :
    ∃ p > N, p.Prime ∧ p % 5 = 3 ∧
      (∃ d, (d = p ∨ d = p + 1) ∧ ∀ e, DivisionAt p (walk p) e ↔ e = d) ∧
      (∀ n, p + 1 ≤ n → walk p (n + 1) = walk p n + (n + 1)) := by
  obtain ⟨p, hpN, hp, hcast⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    (q := 5) (a := 3) (by decide) N
  have hmod : p % 5 = 3 := by
    have h := congrArg ZMod.val hcast
    simpa using h
  have hp2 : p ≠ 2 := by omega
  obtain ⟨d, D, hcases, _, honce, htail⟩ :=
    walk_prime_residue_classes hp hp2 (Or.inr hmod)
  have hd : d = p ∨ d = p + 1 := hcases.imp And.left And.left
  refine ⟨p, hpN, hp, hmod, ⟨d, hd, honce⟩, ?_⟩
  intro n hn
  exact (htail n (by rcases hd with rfl | rfl <;> omega)).2.2

#print axioms walk_prime_residue_classes
#print axioms arbitrarily_large_single_division

end PrimeDivisionRecaman
