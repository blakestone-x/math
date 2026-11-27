import Symmetry
import Mathlib.Data.Nat.ModEq

namespace ThreeHalves.Frequency

/-- This is the external theorem (CERS, Theorem 18) with the full prefix denominator. -/
def GlobalLetterTheorem := ∀ (a b : Nat) (c : Bool),
  Filter.Tendsto (fun N : Nat =>
    count (fun j => (j % (2^a) == b % (2^a)) && (t j == c)) N / N)
    Filter.atTop (nhds (1/(2*(2^a:Nat) : ℝ)))

private def masked (h b : Nat) (c : Bool) (j : Nat) := (j%h == b%h) && (t j == c)

private theorem one_per_block (h b : Nat) (c : Bool) (pos : 0<h) (k : Nat) :
    count (masked h b c) (b+h*k+h) = count (masked h b c) (b+h*k) + bit (t (b+h*k) == c) := by
  let s := b+h*k
  have hs : s%h=b%h := by simp [s,Nat.mul_comm h k]
  have term (i : Nat) (hi : i<h) (nz : i≠0) : masked h b c (s+i)=false := by
    have e : (s+i)%h≠b%h := by
      intro eq
      have mod : s+i ≡ s+0 [MOD h] := by simpa [Nat.ModEq,hs] using eq
      have mi := Nat.ModEq.add_left_cancel' s mod
      apply nz
      simpa [Nat.ModEq,Nat.mod_eq_of_lt hi] using mi
    simp [masked,e]
  have partial_block (i : Nat) (hi : i<h) :
      count (masked h b c) (s+i+1) = count (masked h b c) s + bit (t s == c) := by
    induction i with
    | zero => simp [count,masked,hs,bit]
    | succ i ih =>
      rw [count,term (i+1) hi (by omega)]
      simp only [bit,Bool.false_eq_true,if_false,add_zero]
      rw [show s+(i+1)=s+i+1 by omega]
      exact ih (by omega)
  have hh := partial_block (h-1) (by omega)
  simpa only [show s+(h-1)+1=s+h by omega] using hh

private theorem sample_counts (h b : Nat) (c : Bool) (pos : 0<h) (N : Nat) :
    count (masked h b c) (b+h*N) =
      count (masked h b c) b + count (fun j => t (h*j+b) == c) N := by
  induction N with
  | zero => simp [count]
  | succ N ih =>
    rw [Nat.mul_succ,← Nat.add_assoc,one_per_block h b c pos N,ih,count,
      Nat.add_comm (h*N) b,add_assoc]

theorem from_global (source : GlobalLetterTheorem) : LetterLimit := by
  intro a b c
  apply ordinary_limit
  intro ε he
  let h := 2^a
  have hp : 0<h := by dsimp [h]; positivity
  have hpr : (0:ℝ)<h := by exact_mod_cast hp
  let v : ℝ := 1/(2*(h:ℝ))
  have hh : HasFrequency (masked h b c) v := of_ordinary_limit (source a b c)
  obtain ⟨C,hC⟩ := hh (ε/h) (div_pos he hpr)
  let D := count (masked h b c) b - b*v
  refine ⟨C+b*(ε/h)+|D|,fun N => ?_⟩
  have e := hC (b+h*N)
  rw [sample_counts h b c hp] at e
  push_cast at e
  have norm : (h:ℝ)*v=1/2 := by unfold v; field_simp; ring
  have scale : (h:ℝ)*(ε/h)=ε := by field_simp
  have lhs : count (masked h b c) b + count (fun j => t (h*j+b) == c) N -
      (b+h*(N:ℝ))*v = (count (fun j => t (h*j+b) == c) N-N*(1/2))+D := by
    dsimp [D]; rw [← norm]; ring
  have rhs : ((b:ℝ)+h*N)*(ε/h)+C = N*ε+(C+b*(ε/h)) := by
    calc _ = (N:ℝ)*((h:ℝ)*(ε/h))+(C+b*(ε/h)) := by ring
         _ = _ := by rw [scale]
  rw [lhs,rhs] at e
  change |count (fun j => t (h*j+b) == c) N - ↑N*(1/2)| ≤ _
  have shift (u d k : ℝ) (bound : |u+d| ≤ k) : |u| ≤ k+|d| := by
    obtain ⟨lo,hi⟩ := abs_le.mp bound
    have dlo := neg_abs_le d
    have dhi := le_abs_self d
    rw [abs_le]; constructor <;> linarith
  simpa only [add_assoc] using shift _ _ _ e

/-- For every binary word, including nonfactors, both displayed rational numbers
are the limits on every dyadic progression, and are invariant under both symmetries. -/
theorem factor_frequencies (source : GlobalLetterTheorem) (w : Word) (a b : Nat) :
    Filter.Tendsto (fun N : Nat => count (sample t a b w) N / N)
      Filter.atTop (nhds (freq w : ℝ)) ∧
    Filter.Tendsto (fun N : Nat => count (sample x a b w) N / N)
      Filter.atTop (nhds (siblingFreq w : ℝ)) ∧
    (freq w.reverse=freq w ∧ freq (flip w)=freq w) ∧
    (siblingFreq w.reverse=siblingFreq w ∧ siblingFreq (flip w)=siblingFreq w) := by
  obtain ⟨ht,hx⟩ := both_word_limits (from_global source) w a b
  exact ⟨ht,hx,normalized_symmetries w,sibling_symmetries w⟩

theorem conjectured_values :
    siblingFreq [false,false]=1/10 ∧ siblingFreq [false,true]=2/5 := by
  norm_num [siblingFreq,optFreq,decodeX,freq,approx,shortValue]

theorem fifth_frequencies :
    siblingFreq ((List.replicate 5 [false,true,false]).flatten)=1/180 ∧
    siblingFreq ((List.replicate 5 [true,false,true]).flatten)=1/180 := by
  norm_num [List.replicate_succ,siblingFreq,optFreq,decodeX,freq,approx,shortValue,decode]

#print axioms factor_frequencies
#print axioms conjectured_values
#print axioms fifth_frequencies
end ThreeHalves.Frequency
