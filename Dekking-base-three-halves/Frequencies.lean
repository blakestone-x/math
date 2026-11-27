import Decoding
import Estimates

namespace ThreeHalves.Frequency
open Phase

def sample (u : Nat → Bool) (a b : Nat) (w : List Bool) (j : Nat) :=
  hit u (2^a*j+b) w

/-- The conditional version of Cassaigne--Espinoza--Rigo--Stipulanti, Theorem 18. -/
def DyadicLetters := ∀ (a b : Nat) (c : Bool),
  HasFrequency (fun j => t (2^a*j+b) == c) (1/2)

theorem phase_values (n : Nat) :
    (phase n).value = n%3 ∧ 2*(n/3)+(phase n).offset = parent n := by
  unfold phase parent
  have := Nat.mod_lt n (by decide : 0<3)
  split_ifs <;> simp [Phase.value,Phase.offset] <;> omega

private theorem pow_two_mod (a : Nat) : 2^a%3=1 ∨ 2^a%3=2 := by
  induction a with
  | zero => decide
  | succ a ih => rw [pow_succ,Nat.mul_mod]; rcases ih with h|h <;> rw [h] <;> decide

theorem phase_sum (a b : Nat) (F : Phase → ℝ) :
    F (phase (2^a*0+b))+F (phase (2^a*1+b))+F (phase (2^a*2+b)) = F zero+F one+F two := by
  have hb := Nat.mod_lt b (by decide : 0<3)
  rcases pow_two_mod a with h|h <;> interval_cases e : b%3 <;>
    simp [phase,Nat.add_mod _ b 3,Nat.mul_mod (2^a) _ 3,h,e] <;> ring

private theorem decimate (w : List Bool) (a b j n : Nat) :
    sample t a b w (3*n+j) =
      optionHit t (2^(a+1)*n+parent (2^a*j+b)) (decode (phase (2^a*j+b)) w) := by
  let d := 2^a*j+b
  have vals := phase_values d
  have h : 2^a*(3*n+j)+b=3*(2^a*n+d/3)+(phase d).value := by
    rw [vals.1]
    calc 2^a*(3*n+j)+b = 3*(2^a*n)+d := by dsimp [d]; ring
         _ = _ := by omega
  unfold sample
  rw [h,decode_correct]
  congr 1
  change 2*(2^a*n+d/3)+(phase d).offset=2^(a+1)*n+parent d
  rw [← vals.2,pow_succ]; ring

private theorem combine (a b : Nat) (w : List Bool) (hm : 2≤w.length) (E : Phase → ℝ)
    (nonneg : ∀ r, 0 ≤ E r)
    (children : ∀ r B, ErrorBound (fun n => optionHit t (2^(a+1)*n+B) (decode r w))
                            (optFreq (decode r w) : ℝ) (E r)) :
    ErrorBound (sample t a b w) (freq w : ℝ) ((E zero+E one+E two)/3) := by
  let r (j : Nat) := phase (2^a*j+b)
  let v (r : Phase) : ℝ := optFreq (decode r w)
  have each (j : Nat) : ErrorBound (fun n => sample t a b w (3*n+j)) (v (r j)) (E (r j)) := by
    simp only [decimate]
    exact children _ _
  have h := three_bounds (each 0) (each 1) (each 2)
    (by have := nonneg (r 0); have := nonneg (r 1); have := nonneg (r 2); positivity)
  change ErrorBound _ ((v (r 0)+v (r 1)+v (r 2))/3) _ at h
  rw [show v (r 0)+v (r 1)+v (r 2)=_ from phase_sum a b v,
      show E (r 0)+E (r 1)+E (r 2)=_ from phase_sum a b E] at h
  have hf : (freq w : ℝ) = (v zero+v one+v two)/3 := by
    dsimp [v]; exact_mod_cast balance w hm
  rw [hf]; exact h

/-- Frequencies of arbitrary normalized words along every dyadic progression. -/
theorem all_t (letters : DyadicLetters) (w : List Bool) (a b : Nat) :
    HasFrequency (sample t a b w) (freq w : ℝ) := by
  suffices H : ∀ m (v : List Bool), v.length=m → ∀ a b,
      HasFrequency (sample t a b v) (freq v : ℝ) from H _ w rfl a b
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro v hv a b
    by_cases small : m<2
    · match v with
      | [] => simpa only [freq_nil,Rat.cast_one] using true_freq
      | [c] =>
        rw [freq_one]
        change HasFrequency (fun n => (t (2^a*n+b) == c) && true) _
        simpa using letters a b c
      | _::_::_ => simp at hv; omega
    intro ε he
    let δ := ε/2
    have hδ : 0<δ := by dsimp [δ]; linarith
    let R : ℝ := 2/3
    have hR : 0<R := by norm_num [R]
    have hsmall : R<1 := by norm_num [R]
    have improve (k : Nat) : ∀ (u : List Bool), u.length=m → ∀ A B,
        ErrorBound (sample t A B u) (freq u : ℝ) (δ+R^k) := by
      induction k with
      | zero =>
        intro u _ A B
        have unit := freq_unit u
        exact enlarge (coarse _ (by exact_mod_cast unit.1) (by exact_mod_cast unit.2)) (by simp; linarith)
      | succ k prev =>
        intro u hu A B
        let E : Phase → ℝ := fun r => if r=zero then δ else δ+R^k
        have rp : 0 < R^k := pow_pos hR _
        have epos (r : Phase) : 0<E r := by dsimp [E]; split_ifs <;> linarith
        have ch (r : Phase) (b' : Nat) : ErrorBound
            (fun n => optionHit t (2^(A+1)*n+b') (decode r u)) (optFreq (decode r u) : ℝ) (E r) := by
          cases hdec : decode r u with
          | none => simpa [optionHit,optFreq] using false_freq (E r) (epos r)
          | some z =>
            have hz := decoded_length r u z hdec
            have hlen := span_le r u.length
            change ErrorBound (sample t (A+1) b' z) (freq z : ℝ) (E r)
            by_cases hs : z.length<m
            · exact ih _ hs z rfl _ _ (E r) (epos r)
            · have hr : r≠zero := by
                intro heq; subst r; have := span_zero u.length (by omega); omega
              simp only [E,if_neg hr]
              exact prev z (by omega) _ _
        have hh := combine A B u (by omega) E (fun r => (epos r).le) ch
        have heq : (E zero+E one+E two)/3 = δ+R^(k+1) := by
          simp [E,pow_succ,R]; ring
        rwa [heq] at hh
    obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hδ hsmall
    apply enlarge (improve k v hv a b)
    dsimp [δ] at hk ⊢
    linarith

theorem t_word_limit (letters : DyadicLetters) (w : List Bool) (a b : Nat) :
    Filter.Tendsto (fun N : Nat => count (sample t a b w) N / N)
      Filter.atTop (nhds (freq w : ℝ)) := ordinary_limit (all_t letters w a b)

#print axioms t_word_limit
end ThreeHalves.Frequency
