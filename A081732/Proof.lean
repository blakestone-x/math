import Std

/-! # The ternary one-edit recurrence (OEIS A081732)

Words are written least significant digit first. Arithmetic appends on the
ordinary written numeral by prepending to this list. -/

namespace A081732

abbrev Digit := Fin 3
abbrev Word := List Digit

/-- Exactly one ordinary edit, with any initial segment left untouched. -/
inductive OneEdit : Word → Word → Prop where
  | insert (d : Digit) (w : Word) : OneEdit w (d :: w)
  | delete (d : Digit) (w : Word) : OneEdit (d :: w) w
  | replace {d e : Digit} (h : e ≠ d) (w : Word) : OneEdit (d :: w) (e :: w)
  | keep (d : Digit) {w v : Word} (h : OneEdit w v) : OneEdit (d :: w) (d :: v)

private theorem digit_options : ∀ d e : Digit, e ≠ d ↔ e = d + 1 ∨ e = d + 2 := by decide
private theorem distinct : ∀ d : Digit,
    d + 1 ≠ d ∧ d + 2 ≠ d ∧ d + 1 ≠ d + 2 := by decide

/-- Four edits with a different first digit, all with at least as many digits
as the source. Deletion is handled separately because it can repeat an edit. -/
private def front (d : Digit) (w : Word) : List Word :=
  [(d+1)::w, (d+2)::w, (d+1)::d::w, (d+2)::d::w]

private def dropHead (d : Digit) (w : Word) : List Word :=
  if w.head? = some d then [] else [w]

/-- A duplicate-free enumeration of one-edit outputs before checking leading zeros. -/
def edits : Word → List Word
  | [] => [[0], [1], [2]]
  | d :: w => front d w ++ dropHead d w ++ (edits w).map (d :: ·)

private theorem mem_front {v w : Word} {d : Digit} :
    v ∈ front d w ↔ ∃ e : Digit, e ≠ d ∧ (v = e :: w ∨ v = e :: d :: w) := by
  simp only [front, List.mem_cons, List.not_mem_nil, or_false, digit_options]
  constructor
  · rintro (h | h | h | h)
    · exact ⟨d+1, Or.inl rfl, Or.inl h⟩
    · exact ⟨d+2, Or.inr rfl, Or.inl h⟩
    · exact ⟨d+1, Or.inl rfl, Or.inr h⟩
    · exact ⟨d+2, Or.inr rfl, Or.inr h⟩
  · rintro ⟨e, (rfl | rfl), (rfl | rfl)⟩ <;> simp

private theorem mem_drop {v w : Word} {d : Digit} :
    v ∈ dropHead d w ↔ w.head? ≠ some d ∧ v = w := by
  by_cases h : w.head? = some d <;> simp [dropHead, h]

theorem mem_edits {w v : Word} : v ∈ edits w ↔ OneEdit w v := by
  induction w generalizing v with
  | nil =>
    constructor
    · simp only [edits, List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl) <;> exact OneEdit.insert _ []
    · intro h
      cases h with
      | insert d =>
        have allDigits : ∀ e : Digit, e = 0 ∨ e = 1 ∨ e = 2 := by decide
        rcases allDigits d with rfl | rfl | rfl <;> simp [edits]
  | cons d w ih =>
    simp only [edits, List.mem_append, mem_front, mem_drop, List.mem_map]
    constructor
    · rintro ((⟨e, he, (rfl | rfl)⟩ | ⟨_, rfl⟩) | ⟨u, hu, rfl⟩)
      · exact OneEdit.replace he w
      · exact OneEdit.insert _ _
      · exact OneEdit.delete _ _
      · exact OneEdit.keep _ (ih.mp hu)
    · intro h
      cases h with
      | insert e =>
        by_cases he : e = d
        · subst e
          exact Or.inr ⟨d :: w, ih.mpr (.insert d w), rfl⟩
        · exact Or.inl (Or.inl ⟨e, he, Or.inr rfl⟩)
      | delete =>
        by_cases hd : w.head? = some d
        · obtain ⟨s, rfl⟩ := List.head?_eq_some_iff.mp hd
          exact Or.inr ⟨s, ih.mpr (.delete d s), rfl⟩
        · exact Or.inl (Or.inr ⟨hd, rfl⟩)
      | replace he => exact Or.inl (Or.inl ⟨_, he, Or.inl rfl⟩)
      | keep _ he => exact Or.inr ⟨_, ih.mpr he, rfl⟩

private theorem drop_separate (d : Digit) (w : Word) (rest : List Word)
    (hr : rest.Nodup) : (dropHead d w ++ rest.map (d :: ·)).Nodup := by
  have hm : (rest.map (d :: ·)).Nodup := by
    simpa [List.Nodup, List.pairwise_map] using hr
  by_cases h : w.head? = some d
  · simpa [dropHead, h] using hm
  · simp only [dropHead, h, if_false, List.singleton_append, List.nodup_cons]
    refine ⟨?_, hm⟩
    rintro hy
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hy
    exact h rfl

theorem edits_nodup (w : Word) : (edits w).Nodup := by
  induction w with
  | nil => decide
  | cons d w ih =>
    obtain ⟨ha, hb, hab⟩ := distinct d
    have tailND := drop_separate d w (edits w) ih
    have outside (e : Digit) (he : e ≠ d) (s : Word) (hs : w.length ≤ s.length) :
        e :: s ∉ dropHead d w ++ (edits w).map (d :: ·) := by
      intro hv
      rcases List.mem_append.mp hv with hv | hv
      · have eq := (mem_drop.mp hv).2
        have hl := congrArg List.length eq
        simp at hl
        omega
      · obtain ⟨u, _, eq⟩ := List.mem_map.mp hv
        exact he (List.cons.inj eq).1.symm
    simp [edits, List.append_assoc, front, List.nodup_cons, hab, ha, hb,
      outside, tailND, List.cons_ne_self]

/-- A reversed numeral represents zero by [0] and otherwise has a nonzero last digit. -/
def canonical (w : Word) : Bool :=
  w == [0] || w.getLast?.getD 0 != 0

def neighbors (w : Word) : List Word := (edits w).filter canonical

theorem neighbors_spec {w v : Word} :
    v ∈ neighbors w ↔ OneEdit w v ∧ canonical v = true := by
  simp [neighbors, mem_edits]

theorem neighbors_nodup (w : Word) : (neighbors w).Nodup :=
  List.Pairwise.filter canonical (edits_nodup w)

private theorem length_bound {w v : Word} (h : OneEdit w v) :
    w.length ≤ v.length + 1 := by
  induction h <;> simp_all <;> omega

private theorem canonical_cons (d : Digit) (w : Word) (h : 2 ≤ w.length) :
    canonical (d :: w) = canonical w := by
  match w with
  | [] | [_] => simp at h
  | a :: b :: s => simp [canonical]

/-- The word form of the recurrence, counted from actual distinct edit outcomes. -/
theorem append_digit (d x : Digit) (s : Word) (hlen : 3 ≤ (x :: s).length)
    (hc : canonical (x :: s) = true) :
    (neighbors (d :: x :: s)).length =
      (neighbors (x :: s)).length + (if d = x then 4 else 5) := by
  let w := x :: s
  have hw : 2 ≤ w.length := by change 2 ≤ (x :: s).length; omega
  have hfront : (front d w).filter canonical = front d w := by
    apply List.filter_eq_self.mpr
    intro v hv
    obtain ⟨e, _, (rfl | rfl)⟩ := mem_front.mp hv
    · rw [canonical_cons e w hw]; exact hc
    · rw [canonical_cons e (d :: w) (by simp; omega), canonical_cons d w hw]; exact hc
  have hmap : ((edits w).map (d :: ·)).filter canonical =
      ((edits w).filter canonical).map (d :: ·) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro v hv
    have hb := length_bound (mem_edits.mp hv)
    exact canonical_cons d v (by change (x :: s).length ≤ v.length + 1 at hb; omega)
  change ((front d w ++ dropHead d w ++ (edits w).map (d :: ·)).filter canonical).length = _
  simp only [List.filter_append, hfront, hmap, List.length_append, List.length_map]
  by_cases eq : d = x
  · subst d; simp [front, dropHead, w, neighbors, hc]; omega
  · simp [front, dropHead, w, neighbors, eq, Ne.symm eq, hc]; omega


/-- Numeric value of a least-significant-first ternary word. -/
def value : Word → Nat
  | [] => 0
  | d :: w => d.val + 3 * value w

def trit (n : Nat) : Digit := ⟨n % 3, by omega⟩

/-- Standard base-three conversion by repeated division. -/
def digits (n : Nat) : Word :=
  if n < 3 then [trit n] else trit n :: digits (n / 3)
termination_by n
decreasing_by omega

private theorem digits_cons (n : Nat) : ∃ w, digits n = trit n :: w := by
  rw [digits]; split <;> exact ⟨_, rfl⟩

theorem value_digits (n : Nat) : value (digits n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [digits]; split
    · simp [value, trit, Nat.mod_eq_of_lt ‹n < 3›]
    · simp only [value, trit]
      rw [ih (n / 3) (by omega)]
      omega

private theorem last_nonzero (n : Nat) (hn : 0 < n) : (digits n).getLast?.getD 0 ≠ 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [digits]; split
    · simp [trit, Nat.mod_eq_of_lt ‹n < 3›, Fin.ext_iff]; omega
    · have ht := ih (n / 3) (by omega) (by omega)
      obtain ⟨w, hw⟩ := digits_cons (n / 3)
      simpa [hw] using ht

theorem canonical_digits (n : Nat) : canonical (digits n) = true := by
  by_cases hn : n = 0
  · subst n; rw [digits, if_pos (by decide)]; decide
  · simp [canonical, last_nonzero n (by omega)]

private theorem positive_value (w : Word) (h : w.getLast?.getD 0 ≠ 0) : 0 < value w := by
  induction w with
  | nil => simp at h
  | cons d w ih =>
    cases w with
    | nil =>
      simp only [List.getLast?_singleton, Option.getD_some] at h
      have hd := d.isLt
      simp [value, Fin.ext_iff] at *; omega
    | cons e s =>
      simp only [List.getLast?_cons_cons] at h
      have := ih h
      simp [value]; simp [value] at this; omega

/-- Canonical words and natural numbers describe the same possible outcomes. -/
theorem digits_value (w : Word) (hc : canonical w = true) : digits (value w) = w := by
  induction w with
  | nil => simp [canonical] at hc
  | cons d w ih =>
    have hd := d.isLt
    cases w with
    | nil =>
      simp only [value, Nat.mul_zero, Nat.add_zero]
      rw [digits, if_pos hd]
      simp [trit, Nat.mod_eq_of_lt hd]
    | cons e s =>
      have ht : (e :: s).getLast?.getD 0 ≠ 0 := by simpa [canonical] using hc
      have hcan : canonical (e :: s) = true := by simp [canonical, ht]
      have hp := positive_value (e :: s) ht
      change digits (d.val + 3 * value (e :: s)) = _
      rw [digits, if_neg (by omega)]
      have hm : trit (d.val + 3 * value (e :: s)) = d := Fin.ext (by dsimp [trit]; omega)
      have hq : (d.val + 3 * value (e :: s)) / 3 = value (e :: s) := by omega
      rw [hm, hq, ih hcan]

/-- The actual neighboring integers, each represented once. -/
def integerNeighbors (n : Nat) : List Nat := (neighbors (digits n)).map value

theorem integerNeighbors_spec {n k : Nat} :
    k ∈ integerNeighbors n ↔ OneEdit (digits n) (digits k) := by
  simp only [integerNeighbors, List.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨he, hc⟩ := neighbors_spec.mp hv
    rwa [digits_value v hc]
  · intro he
    exact ⟨digits k, neighbors_spec.mpr ⟨he, canonical_digits k⟩, value_digits k⟩

theorem integerNeighbors_nodup (n : Nat) : (integerNeighbors n).Nodup := by
  have nd := neighbors_nodup (digits n)
  refine List.pairwise_map.mpr ?_
  apply nd.imp_of_mem
  intro u v hu hv huv eq
  apply huv
  rw [← digits_value u (neighbors_spec.mp hu).2, ← digits_value v (neighbors_spec.mp hv).2, eq]

def a (n : Nat) : Nat := (integerNeighbors n).length

private theorem three_digits {n : Nat} (h : 9 ≤ n) : 3 ≤ (digits n).length := by
  rw [digits, if_neg (by omega), digits.eq_def (n / 3), if_neg (by omega)]
  obtain ⟨w, hw⟩ := digits_cons (n / 3 / 3)
  simp [hw]

theorem recurrence (n : Nat) (d : Digit) (hn : 9 ≤ n) :
    a (3 * n + d.val) = a n + (if d.val = n % 3 then 4 else 5) := by
  have hd := d.isLt
  have hm : trit (3 * n + d.val) = d := Fin.ext (by dsimp [trit]; omega)
  have hq : (3 * n + d.val) / 3 = n := by omega
  have hword : digits (3 * n + d.val) = d :: digits n := by
    rw [digits, if_neg (by omega), hm, hq]
  obtain ⟨s, hs⟩ := digits_cons n
  have ans := append_digit d (trit n) s (hs ▸ three_digits hn) (hs ▸ canonical_digits n)
  simpa only [a, integerNeighbors, List.length_map, hword, hs, Fin.ext_iff, trit] using ans

/-- All nine identities together. -/
theorem nine_cases (m : Nat) (i j : Digit) (hm : 3 ≤ m) :
    a (9*m + 3*i.val + j.val) = a (3*m + i.val) + (if j = i then 4 else 5) := by
  have hi := i.isLt
  have h := recurrence (3*m + i.val) j (by omega)
  have hidx : 3*(3*m + i.val) + j.val = 9*m + 3*i.val + j.val := by omega
  have hrem : (3*m + i.val) % 3 = i.val := by omega
  simpa only [hidx, hrem, Fin.ext_iff] using h

end A081732

-- The three examples 100, 1000, and 1001 in ordinary ternary notation.
#guard A081732.a 9 == 14
#guard A081732.a 27 == 18
#guard A081732.a 28 == 19

#print axioms A081732.integerNeighbors_spec
#print axioms A081732.integerNeighbors_nodup
#print axioms A081732.recurrence
#print axioms A081732.nine_cases
