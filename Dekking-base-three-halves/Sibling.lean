import Frequencies

namespace ThreeHalves.Frequency
open Phase

/-- Decode a factor of A357448 into the consecutive t-bits it specifies. -/
def decodeX : Phase → List Bool → Option (List Bool)
  | _, [] => some []
  | zero, [a] => some [a]
  | zero, [a,b] => if a = !b then some [a] else none
  | zero, a::b::c::v =>
      if a = !b ∧ a=c then (decodeX zero v).map (a :: ·) else none
  | one, [a] => some [!a]
  | one, a::b::v => if a = !b then (decodeX zero v).map (b :: ·) else none
  | two, a::v => (decodeX zero v).map (a :: ·)

private theorem map_hit (a : Bool) (v : Option (List Bool)) (n : Nat) :
    optionHit t n (v.map (a :: ·)) = ((t n == a) && optionHit t (n+1) v) := by
  cases v <;> simp [optionHit,hit]

theorem sibling_decode_correct (r : Phase) (w : List Bool) (k : Nat) :
    hit x (3*k+r.value) w = optionHit t k (decodeX r w) := by
  generalize hn : w.length=m
  induction m using Nat.strong_induction_on generalizing r w k with
  | h m ih =>
    match r,w with
    | r,[] => cases r <;> rfl
    | zero,[a] => simp [hit,decodeX,Phase.value,optionHit,x0]
    | zero,[a,b] =>
      simp [hit,decodeX,Phase.value,optionHit,x0,x1]
      cases he : t k <;> cases a <;> cases b <;> simp [hit,he]
    | zero,a::b::c::v =>
      have next := ih v.length (by simp at hn; omega) zero v (k+1) rfl
      simp only [Phase.value,Nat.add_zero] at next ⊢
      simp only [hit,decodeX,x0,x1,x2,show 3*k+2+1=3*(k+1) by omega,next]
      cases hd : decodeX zero v <;> cases he : t k <;> cases a <;> cases b <;> cases c <;> simp [he,optionHit,hit]
    | one,[a] =>
      simp [hit,decodeX,Phase.value,optionHit,x1]
    | one,a::b::v =>
      have next := ih v.length (by simp at hn; omega) zero v (k+1) rfl
      simp only [Phase.value,Nat.add_zero] at next ⊢
      simp only [hit,decodeX,x1,x2,show 3*k+2+1=3*(k+1) by omega,next]
      cases hd : decodeX zero v <;> cases he : t k <;> cases a <;> cases b <;> simp [he,optionHit,hit]
    | two,a::v =>
      have next := ih v.length (by simp at hn; omega) zero v (k+1) rfl
      simp only [Phase.value,Nat.add_zero] at next ⊢
      simp only [hit,decodeX,map_hit,x2,show 3*k+2+1=3*(k+1) by omega,next]

def siblingFreq (w : List Bool) : ℚ :=
  (optFreq (decodeX zero w)+optFreq (decodeX one w)+optFreq (decodeX two w))/3

theorem all_x (letters : DyadicLetters) (w : List Bool) (a b : Nat) :
    HasFrequency (sample x a b w) (siblingFreq w : ℝ) := by
  intro ε hε
  let r (j : Nat) := phase (2^a*j+b)
  let v (r : Phase) : ℝ := optFreq (decodeX r w)
  have each (j : Nat) : ErrorBound (fun n => sample x a b w (3*n+j)) (v (r j)) ε := by
    let d := 2^a*j+b
    have eq (n : Nat) : sample x a b w (3*n+j) =
        optionHit t (2^a*n+d/3) (decodeX (r j) w) := by
      have vals := phase_values d
      unfold sample
      have arg : 2^a*(3*n+j)+b=3*(2^a*n+d/3)+(r j).value := by
        change _ = 3*(2^a*n+d/3)+(phase d).value
        rw [vals.1]
        calc 2^a*(3*n+j)+b = 3*(2^a*n)+d := by dsimp [d]; ring
             _ = _ := by omega
      rw [arg,sibling_decode_correct]
    simp only [eq]
    dsimp [v]
    cases he : decodeX (r j) w with
    | none => simpa [optionHit,optFreq] using false_freq ε hε
    | some z => exact all_t letters z a (d/3) ε hε
  have h := three_bounds (each 0) (each 1) (each 2) (by linarith)
  rw [show v (r 0)+v (r 1)+v (r 2)=_ from phase_sum a b v,
      show (ε+ε+ε)/3=ε by ring] at h
  simpa only [siblingFreq,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat,v] using h

/-- The cited external analytic input is stated as an ordinary progression-wise letter limit. -/
def LetterLimit := ∀ (a b : Nat) (c : Bool),
  Filter.Tendsto (fun N : Nat => count (fun j => t (2^a*j+b) == c) N / N)
    Filter.atTop (nhds (1/2 : ℝ))

theorem both_word_limits (letters : LetterLimit) (w : List Bool) (a b : Nat) :
    Filter.Tendsto (fun N : Nat => count (sample t a b w) N / N)
      Filter.atTop (nhds (freq w : ℝ)) ∧
    Filter.Tendsto (fun N : Nat => count (sample x a b w) N / N)
      Filter.atTop (nhds (siblingFreq w : ℝ)) := by
  have h : DyadicLetters := fun a b c => of_ordinary_limit (letters a b c)
  exact ⟨t_word_limit h w a b,ordinary_limit (all_x h w a b)⟩

#print axioms both_word_limits
end ThreeHalves.Frequency
