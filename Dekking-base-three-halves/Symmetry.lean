import Sibling

namespace ThreeHalves.Frequency
open Phase

abbrev Word := List Bool
abbrev OptionalWord := Option Word

private def joinW (A B : OptionalWord) : OptionalWord :=
  A.bind (fun a => B.map (fun b => a++b))

@[simp] private theorem join_nil (A : OptionalWord) : joinW (some []) A=A := by cases A <;> rfl
@[simp] private theorem join_none (A : OptionalWord) : joinW none A=none := rfl
@[simp] private theorem join_right_none (A : OptionalWord) : joinW A none=none := by cases A <;> rfl
private theorem join_pre (c : Bool) (A B : OptionalWord) :
    joinW (A.map (c :: ·)) B = (joinW A B).map (c :: ·) := by cases A <;> cases B <;> rfl
private theorem join_rev (c : Bool) (A : OptionalWord) :
    joinW (A.map List.reverse) (some [c]) = (A.map (c :: ·)).map List.reverse := by
  cases A <;> simp [joinW,List.reverse_cons]

def shift (r : Phase) (n : Nat) := phase (r.value+n)
def reflect (c : Nat) (r : Phase) (n : Nat) := phase (3+c-(r.value+n)%3)
private theorem phase_ext {r q : Phase} (h : r.value=q.value) : r=q := by cases r <;> cases q <;> simp_all [Phase.value]
private theorem phase_val (n : Nat) : (phase n).value=n%3 := (phase_values n).1

@[simp] private theorem shift0 (r : Phase) : shift r 0=r := by cases r <;> decide
@[simp] private theorem shift_z2 (n : Nat) : shift zero (n+1+1)=shift two n := by
  unfold shift; apply phase_ext; rw [phase_val,phase_val]; simp only [Phase.value]; omega
@[simp] private theorem shift_o1 (n : Nat) : shift one (n+1)=shift two n := by
  unfold shift; apply phase_ext; rw [phase_val,phase_val]; simp only [Phase.value]; omega
@[simp] private theorem shift_t1 (n : Nat) : shift two (n+1)=shift zero n := by
  unfold shift; apply phase_ext; rw [phase_val,phase_val]; simp only [Phase.value]; omega
@[simp] private theorem shift_z3 (n : Nat) : shift zero (n+1+1+1)=shift zero n := by
  unfold shift; apply phase_ext; rw [phase_val,phase_val]; simp only [Phase.value]; omega
@[simp] private theorem shift_o2 (n : Nat) : shift one (n+1+1)=shift zero n := by
  unfold shift; apply phase_ext; rw [phase_val,phase_val]; simp only [Phase.value]; omega

private theorem normal_append (r : Phase) (w v : Word) (bound : shift r w.length ≠ one) :
    decode r (w++v) = joinW (decode r w) (decode (shift r w.length) v) := by
  induction r,w using decode.induct with
  | case1 r => cases r <;> simp [decode]
  | case2 a => exact (bound rfl).elim
  | case3 a w ih =>
    simp only [List.length_cons,shift_z2] at bound ⊢
    simp [decode,ih bound,join_pre]
  | case4 a b w he => simp [decode,he]
  | case5 a w ih =>
    simp only [List.length_cons,shift_o1] at bound ⊢
    simp [decode,ih bound,join_pre]
  | case6 a w ih =>
    simp only [List.length_cons,shift_t1] at bound ⊢
    simp [decode,ih bound,join_pre]

private theorem sibling_append (r : Phase) (w v : Word) (bound : shift r w.length = zero) :
    decodeX r (w++v) = joinW (decodeX r w) (decodeX (shift r w.length) v) := by
  generalize hn : w.length=m
  induction m using Nat.strong_induction_on generalizing r w with
  | h m ih =>
    match r,w with
    | r,[] => rw [← hn]; cases r <;> simp [decodeX]
    | zero,[a] => contradiction
    | zero,[a,b] => contradiction
    | zero,a::b::c::u =>
      rw [← hn]
      simp only [List.length_cons,shift_z3] at bound ⊢
      have hh := ih u.length (by simp at hn; omega) zero u bound rfl
      cases a <;> cases b <;> cases c <;> simp [decodeX,hh,join_pre]
    | one,[a] => contradiction
    | one,a::b::u =>
      rw [← hn]
      simp only [List.length_cons,shift_o2] at bound ⊢
      have hh := ih u.length (by simp at hn; omega) zero u bound rfl
      cases a <;> cases b <;> simp [decodeX,hh,join_pre]
    | two,a::u =>
      rw [← hn]
      simp only [List.length_cons,shift_t1] at bound ⊢
      have hh := ih u.length (by simp at hn; omega) zero u bound rfl
      simp [decodeX,hh,join_pre]

/-- Phase after the reversed tail; the reflected head starts on a parent boundary. -/
private theorem reflected_boundary (c : Nat) (r : Phase) (k n : Nat)
    (hc : c=0 ∨ c=2) (hk : k≤3) :
    shift (reflect c r (n+k)) n = phase (9+c-r.value-k) := by
  apply phase_ext
  simp only [shift,phase_val,reflect]
  cases r <;> simp only [Phase.value] <;> rcases hc with rfl|rfl <;>
    interval_cases k <;> omega

private theorem reflected_tail (c : Nat) (r : Phase) (k n : Nat) :
    reflect c r (n+k) = reflect c (shift r k) n := by
  apply phase_ext; simp only [reflect,shift,phase_val]
  congr 2
  omega

private theorem reverse_normal (r : Phase) (w : Word) :
    decode (reflect 2 r w.length) w.reverse = (decode r w).map List.reverse := by
  induction r,w using decode.induct with
  | case1 r => cases r <;> rfl
  | case2 a => simp [reflect,phase,Phase.value,decode]
  | case3 a w ih =>
    let q := reflect 2 zero (w.length+2)
    have ht : q=reflect 2 two w.length := reflected_tail _ _ 2 _
    have hb : shift q w.reverse.length=zero := by
      rw [List.length_reverse]; exact reflected_boundary 2 zero 2 _ (by decide) (by decide)
    change decode q ((a::a::w).reverse) = _
    rw [List.reverse_cons,List.reverse_cons,List.append_assoc]; simp only [List.cons_append,List.nil_append]
    rw [normal_append q w.reverse [a,a] (by rw [hb]; decide),hb]
    rw [ht,ih]
    simpa [decode] using join_rev a (decode two w)
  | case4 a b w he =>
    let q := reflect 2 zero (w.length+2)
    have hb : shift q w.reverse.length=zero := by
      rw [List.length_reverse]; exact reflected_boundary 2 zero 2 _ (by decide) (by decide)
    change decode q ((a::b::w).reverse) = _
    rw [List.reverse_cons,List.reverse_cons,List.append_assoc]; simp only [List.cons_append,List.nil_append]
    rw [normal_append q w.reverse [b,a] (by rw [hb]; decide),hb]
    simp [decode,he,Ne.symm he]
  | case5 a w ih =>
    let q := reflect 2 one (w.length+1)
    have ht : q=reflect 2 two w.length := reflected_tail _ _ 1 _
    have hb : shift q w.reverse.length=zero := by
      rw [List.length_reverse]; exact reflected_boundary 2 one 1 _ (by decide) (by decide)
    change decode q ((a::w).reverse) = _
    rw [List.reverse_cons,normal_append q w.reverse [a] (by rw [hb]; decide),hb,ht,ih]
    simpa [decode] using join_rev a (decode two w)
  | case6 a w ih =>
    let q := reflect 2 two (w.length+1)
    have ht : q=reflect 2 zero w.length := reflected_tail _ _ 1 _
    have hb : shift q w.reverse.length=two := by
      rw [List.length_reverse]; exact reflected_boundary 2 two 1 _ (by decide) (by decide)
    change decode q ((a::w).reverse) = _
    rw [List.reverse_cons,normal_append q w.reverse [a] (by rw [hb]; decide),hb,ht,ih]
    simpa [decode] using join_rev (!a) (decode zero w)

private theorem reverse_sibling (r : Phase) (w : Word) :
    decodeX (reflect 0 r w.length) w.reverse = (decodeX r w).map List.reverse := by
  suffices H : ∀ m (r : Phase) (v : Word), v.length=m →
      decodeX (reflect 0 r v.length) v.reverse = (decodeX r v).map List.reverse from H _ r w rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro r v hv
    match r,v with
    | r,[] => cases r <;> rfl
    | zero,[a] => simp [reflect,phase,Phase.value,decodeX]
    | zero,[a,b] => cases a <;> cases b <;> decide +kernel
    | zero,a::b::c::u =>
      let q := reflect 0 zero (u.length+3)
      have ht : q=reflect 0 zero u.length := reflected_tail _ _ 3 _
      have hb : shift q u.reverse.length=zero := by
        rw [List.length_reverse]; exact reflected_boundary 0 zero 3 _ (by decide) (by decide)
      have rec := ih u.length (by simp at hv; omega) zero u rfl
      change decodeX q ((a::b::c::u).reverse) = _
      simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]
      rw [sibling_append q u.reverse [c,b,a] hb,hb,ht,rec]
      cases a <;> cases b <;> cases c <;> simp [decodeX,join_rev]
    | one,[a] => simp [reflect,phase,Phase.value,decodeX]
    | one,a::b::u =>
      let q := reflect 0 one (u.length+2)
      have ht : q=reflect 0 zero u.length := reflected_tail _ _ 2 _
      have hb : shift q u.reverse.length=zero := by
        rw [List.length_reverse]; exact reflected_boundary 0 one 2 _ (by decide) (by decide)
      have rec := ih u.length (by simp at hv; omega) zero u rfl
      change decodeX q ((a::b::u).reverse) = _
      simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]
      rw [sibling_append q u.reverse [b,a] hb,hb,ht,rec]
      cases a <;> cases b <;> simp [decodeX,join_rev]
    | two,a::u =>
      let q := reflect 0 two (u.length+1)
      have ht : q=reflect 0 zero u.length := reflected_tail _ _ 1 _
      have hb : shift q u.reverse.length=zero := by
        rw [List.length_reverse]; exact reflected_boundary 0 two 1 _ (by decide) (by decide)
      have rec := ih u.length (by simp at hv; omega) zero u rfl
      change decodeX q ((a::u).reverse) = _
      rw [List.reverse_cons,sibling_append q u.reverse [a] hb,hb,ht,rec]
      simpa [decodeX] using join_rev a (decodeX zero u)

def flip (w : Word) := w.map Bool.not

private theorem map_pre_flip (a : Bool) (A : OptionalWord) :
    (A.map flip).map ((!a) :: ·) = (A.map (a :: ·)).map flip := by cases A <;> rfl

private theorem complement_normal (r : Phase) (w : Word) :
    decode r (flip w)=(decode r w).map flip := by
  induction r,w using decode.induct with
  | case1 r => cases r <;> rfl
  | case2 a => simp [flip,decode]
  | case3 a w ih =>
    change decode zero ((!a)::(!a)::flip w)=_
    simp [decode,ih,map_pre_flip]; rfl
  | case4 a b w e => cases a <;> cases b <;> simp_all [flip,decode]
  | case5 a w ih =>
    change decode one ((!a)::flip w)=_
    simp [decode,ih,map_pre_flip]; rfl
  | case6 a w ih =>
    change decode two ((!a)::flip w)=_
    simpa [decode,ih] using map_pre_flip (!a) (decode zero w)

private theorem complement_sibling (r : Phase) (w : Word) :
    decodeX r (flip w)=(decodeX r w).map flip := by
  suffices H : ∀ m (r : Phase) (v : Word), v.length=m →
      decodeX r (flip v)=(decodeX r v).map flip from H _ r w rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro r v hv
    match r,v with
    | r,[] => cases r <;> rfl
    | zero,[a] => cases a <;> simp [decodeX,flip]
    | zero,[a,b] => cases a <;> cases b <;> simp [decodeX,flip]
    | zero,a::b::c::u =>
      have rec := ih u.length (by simp at hv; omega) zero u rfl
      change decodeX zero ((!a)::(!b)::(!c)::flip u)=_
      cases a <;> cases b <;> cases c <;> simp [decodeX,rec,map_pre_flip] <;> rfl
    | one,[a] => cases a <;> simp [decodeX,flip]
    | one,a::b::u =>
      have rec := ih u.length (by simp at hv; omega) zero u rfl
      change decodeX one ((!a)::(!b)::flip u)=_
      cases a <;> cases b <;> simp [decodeX,rec,map_pre_flip] <;> rfl
    | two,a::u =>
      have rec := ih u.length (by simp at hv; omega) zero u rfl
      change decodeX two ((!a)::flip u)=_
      simp [decodeX,rec,map_pre_flip]; rfl

private theorem perm_sum (c m : Nat) (hc : c=0 ∨ c=2) (f : Phase → ℚ) :
    f (reflect c zero m)+f (reflect c one m)+f (reflect c two m) = f zero+f one+f two := by
  have hh := Nat.mod_lt m (by decide : 0<3)
  rcases hc with rfl|rfl <;> interval_cases e : m%3 <;>
    simp [reflect,phase,Phase.value,Nat.add_mod _ m 3,e] <;> ring

theorem normalized_symmetries (w : Word) : freq w.reverse=freq w ∧ freq (flip w)=freq w := by
  suffices H : ∀ m (v : Word), v.length=m → freq v.reverse=freq v ∧ freq (flip v)=freq v
    from H _ w rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro v hv
    by_cases small : v.length<4
    · match v with
      | [] => exact ⟨rfl,rfl⟩
      | [a] => cases a <;> decide +kernel
      | [a,b] => cases a <;> cases b <;> decide +kernel
      | [a,b,c] => cases a <;> cases b <;> cases c <;> decide +kernel
      | _::_::_::_::_ => simp at small; omega
    have inv (r : Phase) :
        optFreq ((decode r v).map List.reverse)=optFreq (decode r v) ∧
        optFreq ((decode r v).map flip)=optFreq (decode r v) := by
      cases hd : decode r v with
      | none => exact ⟨rfl,rfl⟩
      | some u =>
        have eu := decoded_length r v u hd
        have hs := span_short r v.length (by omega)
        exact ih u.length (by omega) u rfl
    have rev (r : Phase) :
        optFreq (decode (reflect 2 r v.length) v.reverse)=optFreq (decode r v) := by
      rw [reverse_normal]; exact (inv r).1
    have co (r : Phase) : optFreq (decode r (flip v))=optFreq (decode r v) := by
      rw [complement_normal]; exact (inv r).2
    constructor
    · rw [balance v.reverse (by rw [List.length_reverse]; omega),balance v (by omega)]
      have perm := perm_sum 2 v.length (by decide) (fun r => optFreq (decode r v.reverse))
      rw [← perm,rev,rev,rev]
    · rw [balance (flip v) (by simp [flip]; omega),balance v (by omega),co,co,co]

theorem sibling_symmetries (w : Word) :
    siblingFreq w.reverse=siblingFreq w ∧ siblingFreq (flip w)=siblingFreq w := by
  have rev (r : Phase) : optFreq (decodeX (reflect 0 r w.length) w.reverse)=optFreq (decodeX r w) := by
    rw [reverse_sibling]; cases h : decodeX r w with
    | none => rfl
    | some u => exact (normalized_symmetries u).1
  have co (r : Phase) : optFreq (decodeX r (flip w))=optFreq (decodeX r w) := by
    rw [complement_sibling]; cases h : decodeX r w with
    | none => rfl
    | some u => exact (normalized_symmetries u).2
  constructor
  · unfold siblingFreq
    have perm := perm_sum 0 w.length (by decide) (fun r => optFreq (decodeX r w.reverse))
    rw [← perm,rev,rev,rev]
  · unfold siblingFreq; rw [co,co,co]

#print axioms normalized_symmetries
#print axioms sibling_symmetries
end ThreeHalves.Frequency
