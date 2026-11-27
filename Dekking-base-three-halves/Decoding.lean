import Repetitions

namespace ThreeHalves.Frequency

inductive Phase | zero | one | two deriving DecidableEq
open Phase

def phase (n : Nat) := if n%3=0 then zero else if n%3=1 then one else two
def Phase.value : Phase → Nat | zero => 0 | one => 1 | two => 2
def Phase.offset : Phase → Nat | zero | one => 0 | two => 1

def decode : Phase → List Bool → Option (List Bool)
  | _, [] => some []
  | zero, [a] => some [a]
  | zero, a::b::v => if a=b then (decode two v).map (a :: ·) else none
  | one, a::v => (decode two v).map (a :: ·)
  | two, a::v => (decode zero v).map ((!a) :: ·)

def span : Phase → Nat → Nat
  | _, 0 => 0
  | zero, 1 => 1
  | zero, n+2 => 1+span two n
  | one, n+1 => 1+span two n
  | two, n+1 => 1+span zero n

theorem span_le (r : Phase) (n : Nat) : span r n ≤ n := by
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    cases n with
    | zero => cases r <;> decide
    | succ n =>
      cases r with
      | one => have := ih n (by omega) two; simp only [span]; omega
      | two => have := ih n (by omega) zero; simp only [span]; omega
      | zero =>
        cases n with
        | zero => decide
        | succ n => have := ih n (by omega) two; simp only [span]; omega

theorem span_zero (n : Nat) (hn : 2 ≤ n) : span zero n < n := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+2 := ⟨n-2, by omega⟩
  simp only [span]; have := span_le two m; omega

theorem span_short (r : Phase) (n : Nat) (hn : 4 ≤ n) : span r n < n := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+4 := ⟨n-4, by omega⟩
  cases r with
  | zero => exact span_zero _ (by omega)
  | one => change 1+(1+span zero (m+2)) < m+4
           have := span_zero (m+2) (by omega); omega
  | two => change 1+span zero (m+3) < m+4
           have := span_zero (m+3) (by omega); omega

theorem decoded_length (r : Phase) (w v : List Bool) (h : decode r w=some v) :
    v.length=span r w.length := by
  induction r,w using decode.induct generalizing v with
  | case1 r => simp [decode] at h; subst v; cases r <;> rfl
  | case2 a => simp [decode] at h; subst v; rfl
  | case3 a w ih =>
    simp [decode] at h
    obtain ⟨z,hz,rfl⟩ := h
    simp only [List.length_cons,span,ih _ hz]; omega
  | case4 a b w he => simp [decode,he] at h
  | case5 a w ih =>
    simp [decode] at h
    obtain ⟨z,hz,rfl⟩ := h
    simp only [List.length_cons,span,ih _ hz]; omega
  | case6 a w ih =>
    simp [decode] at h
    obtain ⟨z,hz,rfl⟩ := h
    simp only [List.length_cons,span,ih _ hz]; omega

def hit (u : Nat → Bool) (n : Nat) : List Bool → Bool
  | [] => true
  | a::v => (u n == a) && hit u (n+1) v

def optionHit (u : Nat → Bool) (n : Nat) (w : Option (List Bool)) := w.elim false (hit u n)

private theorem hit_map (a : Bool) (v : Option (List Bool)) (n : Nat) :
    optionHit t n (v.map (a :: ·)) = ((t n == a) && optionHit t (n+1) v) := by
  cases v <;> simp [optionHit,hit]

theorem decode_correct (r : Phase) (w : List Bool) (k : Nat) :
    hit t (3*k+r.value) w = optionHit t (2*k+r.offset) (decode r w) := by
  induction r,w using decode.induct generalizing k with
  | case1 r => cases r <;> rfl
  | case2 a => simp [hit,decode,Phase.value,Phase.offset,optionHit,t0]
  | case3 a w ih =>
    simp only [Phase.value,Phase.offset] at ih ⊢
    simp [hit,decode,hit_map,t0,t1,ih]
  | case4 a b w he =>
    simp [hit,decode,he,Phase.value,Phase.offset,optionHit,t0,t1]
    cases t (2*k) <;> cases a <;> cases b <;> simp_all
  | case5 a w ih =>
    simp only [Phase.value,Phase.offset] at ih ⊢
    simp [hit,decode,hit_map,t1,ih]
  | case6 a w ih =>
    have h := ih (k+1)
    simp only [Phase.value,Phase.offset,Nat.add_zero] at h ⊢
    rw [decode,hit_map,hit,t2,show 3*k+2+1=3*(k+1) by omega,h,
      show 2*(k+1)=2*k+1+1 by omega]
    cases t (2*k+1) <;> cases a <;> rfl

def shortValue : List Bool → ℚ
  | [] => 1
  | [_] => 1/2
  | [a,b] => if a=b then 3/10 else 1/5
  | [a,b,c] => if a=c ∧ a≠b then 1/20 else 3/20
  | _ => 0

/-- Fuel only limits the depth of strictly shortening words of length at least four. -/
def approx : Nat → List Bool → ℚ
  | 0, w => shortValue w
  | k+1, w => if w.length<4 then shortValue w else
      ((decode zero w).elim 0 (approx k) + (decode one w).elim 0 (approx k) +
        (decode two w).elim 0 (approx k))/3

private theorem stable (k : Nat) (w : List Bool) (hk : w.length ≤ k) :
    approx (k+1) w = approx k w := by
  induction k generalizing w with
  | zero => have : w=[] := List.length_eq_zero_iff.mp (by omega); subst w; rfl
  | succ k ih =>
    by_cases hs : w.length<4
    · simp [approx,hs]
    · have eq (r : Phase) : (decode r w).elim 0 (approx (k+1)) =
          (decode r w).elim 0 (approx k) := by
        cases h : decode r w with
        | none => rfl
        | some v =>
          apply ih
          have e := decoded_length r w v h
          have b := span_short r w.length (by omega)
          omega
      simp only [approx,if_neg hs]
      change ((decode zero w).elim 0 (approx (k+1)) + (decode one w).elim 0 (approx (k+1)) +
        (decode two w).elim 0 (approx (k+1)))/3 = _
      rw [eq,eq,eq]

def freq (w : List Bool) : ℚ := approx w.length w
def optFreq (w : Option (List Bool)) : ℚ := w.elim 0 freq

@[simp] theorem freq_nil : freq []=1 := by rfl
@[simp] theorem freq_one (c : Bool) : freq [c]=1/2 := by rfl

private theorem enough (w : List Bool) (k : Nat) (hk : w.length ≤ k) : approx k w = freq w := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero => rfl
  | succ j ih => rw [Nat.add_succ,stable _ _ (by omega)]; exact ih (by omega)

private theorem small_balance (w : List Bool) (lo : 2 ≤ w.length) (hi : w.length < 4) :
    freq w=(optFreq (decode zero w)+optFreq (decode one w)+optFreq (decode two w))/3 := by
  match w with
  | [a,b] => cases a <;> cases b <;> norm_num [freq,approx,shortValue,decode,optFreq]
  | [a,b,c] => cases a <;> cases b <;> cases c <;> norm_num [freq,approx,shortValue,decode,optFreq]
  | [] | [_] | _::_::_::_::_ => simp_all <;> omega

theorem balance (w : List Bool) (lo : 2 ≤ w.length) :
    freq w=(optFreq (decode zero w)+optFreq (decode one w)+optFreq (decode two w))/3 := by
  by_cases hs : w.length<4
  · exact small_balance w lo hs
  · have eq (r : Phase) : (decode r w).elim 0 (approx w.length) = optFreq (decode r w) := by
      cases h : decode r w with
      | none => rfl
      | some v =>
        apply enough
        rw [decoded_length r w v h]
        exact span_le _ _
    unfold freq
    rw [← stable w.length w le_rfl,approx,if_neg hs,eq,eq,eq]

theorem freq_unit (w : List Bool) : 0 ≤ freq w ∧ freq w ≤ 1 := by
  have h (k : Nat) (v : List Bool) : 0 ≤ approx k v ∧ approx k v ≤ 1 := by
    have sm (u : List Bool) : 0 ≤ shortValue u ∧ shortValue u ≤ 1 := by
      match u with
      | [] | [_] => norm_num [shortValue]
      | [a,b] => cases a <;> cases b <;> norm_num [shortValue]
      | [a,b,c] => cases a <;> cases b <;> cases c <;> norm_num [shortValue]
      | _::_::_::_::_ => norm_num [shortValue]
    induction k generalizing v with
    | zero => exact sm v
    | succ k ih =>
      by_cases hs : v.length<4
      · simpa [approx,hs] using sm v
      · have hh (r : Phase) :
            0 ≤ (decode r v).elim 0 (approx k) ∧ (decode r v).elim 0 (approx k) ≤ 1 := by
          cases decode r v with | none => norm_num | some z => exact ih z
        have h0 := hh zero; have h1 := hh one; have h2 := hh two
        simp [approx,hs]; constructor <;> linarith
  exact h _ _

end ThreeHalves.Frequency
