import Blocks

namespace CeilingArray

def CommonGap (d : ℕ) := d = 3 ∨ d = 5 ∨ d = 10 ∨ d = 13

theorem allowed_spec (d : ℕ) : allowed d = true ↔ CommonGap d := by
  simp [allowed,CommonGap,or_assoc]

private def sample (b : Kind) (n : ℕ) := ((word b 9 none)[n]?).getD false

private theorem sample_correct (b : Kind) {n : ℕ} (hn : n < 89) : sample b n = true ↔ target b n := by
  have e : (List.range 89).map (bit b) = word b 9 none := word_root b 9
  simpa only [sample, ← e, List.getElem?_map, List.getElem?_range hn, Option.map_some,
    Option.getD_some] using (bit_correct b n)

private def sampleGap (b : Kind) (x y : ℕ) : Bool :=
  decide (x < y) && sample b x && sample b y &&
    (List.range y).all (fun z => decide (z ≤ x) || !sample b z)

private theorem sample_gap {b : Kind} {x y : ℕ} (hy : y < 89) (h : sampleGap b x y = true) :
    Consecutive (target b) x y := by
  simp only [sampleGap,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range] at h
  obtain ⟨⟨⟨lt,hx⟩,he⟩,m⟩ := h
  refine ⟨lt,(sample_correct _ (lt.trans hy)).mp hx,(sample_correct _ hy).mp he,?_⟩
  intro z xz zy hz
  have a := m z zy
  have t := (sample_correct _ (zy.trans hy)).mpr hz
  simp [t,show ¬z≤x by omega] at a

def GapOf (P : ℕ → Prop) (d : ℕ) := ∃ x y, Consecutive P x y ∧ y-x = d

theorem common_occurs (b : Kind) {d : ℕ} (h : CommonGap d) : GapOf (target b) d := by
  rcases h with rfl|rfl|rfl|rfl <;> cases b
  · exact ⟨23,26,sample_gap (by decide) (by decide),rfl⟩
  · exact ⟨8,11,sample_gap (by decide) (by decide),rfl⟩
  · exact ⟨26,31,sample_gap (by decide) (by decide),rfl⟩
  · exact ⟨3,8,sample_gap (by decide) (by decide),rfl⟩
  · exact ⟨68,78,sample_gap (by decide) (by decide),rfl⟩
  · exact ⟨11,21,sample_gap (by decide) (by decide),rfl⟩
  · exact ⟨10,23,sample_gap (by decide) (by decide),rfl⟩
  · exact ⟨32,45,sample_gap (by decide) (by decide),rfl⟩

theorem target_gaps (b : Kind) (d : ℕ) : GapOf (target b) d ↔ CommonGap d := by
  refine ⟨?_,common_occurs b⟩
  rintro ⟨x,y,h,rfl⟩
  exact (allowed_spec _).mp (gap_bound h)

/-- Kimberling's A341261 conjecture for exactly two array positions. -/
theorem doubled_gaps (d : ℕ) : GapOf Doubled d ↔ CommonGap d := target_gaps .twice d

theorem tail_min {n : ℕ} (h : target .omittedTail n) : 3 ≤ n := by
  by_contra! e
  have q := (sample_correct .omittedTail (show n<89 by omega)).mpr h
  interval_cases n <;> contradiction

theorem missing_one : Missing 1 := by
  rw [← value_one, missing_choices]
  exact ⟨value_pos 0 [], rfl, rfl⟩

theorem tail_three : target .omittedTail 3 := (sample_correct _ (by decide)).mp (by decide)

theorem first_missing_gap : Consecutive Missing 1 3 := by
  refine ⟨by decide,missing_one,tail_three.1,?_⟩
  intro z a b hz
  have t := tail_min (n := z) ⟨hz,by omega⟩
  omega

theorem tail_to_missing {x y : ℕ} (h : Consecutive (target .omittedTail) x y) :
    Consecutive Missing x y := by
  obtain ⟨lt,hx,hy,m⟩ := h
  have start := tail_min hx
  exact ⟨lt,hx.1,hy.1,fun z a b hz => m z a b ⟨hz,by omega⟩⟩

theorem missing_split {x y : ℕ} (h : Consecutive Missing x y) :
    (x = 1 ∧ y = 3) ∨ Consecutive (target .omittedTail) x y := by
  obtain ⟨lt,hx,hy,m⟩ := h
  have pos := hx.1
  have ty : target .omittedTail y := ⟨hy,by omega⟩
  by_cases eq : x=1
  · left
    have lb := tail_min ty
    have ub : ¬3<y := fun e => m 3 (by omega) e tail_three.1
    exact ⟨eq,by omega⟩
  · exact Or.inr ⟨lt,⟨hx,eq⟩,ty,fun z a b hz => m z a b hz.1⟩

/-- Kimberling's A341262 conjecture for the omitted positive integers. -/
theorem missing_gaps (d : ℕ) : GapOf Missing d ↔ d = 2 ∨ CommonGap d := by
  constructor
  · rintro ⟨x,y,h,rfl⟩
    rcases missing_split h with ⟨rfl,rfl⟩ | ht
    · exact Or.inl rfl
    · exact Or.inr ((allowed_spec _).mp (gap_bound ht))
  · rintro (rfl|h)
    · exact ⟨1,3,first_missing_gap,rfl⟩
    · obtain ⟨x,y,ht,e⟩ := common_occurs .omittedTail h
      exact ⟨x,y,tail_to_missing ht,e⟩

theorem unique_gap_two (x y : ℕ) :
    Consecutive Missing x y ∧ y-x = 2 ↔ x = 1 ∧ y = 3 := by
  constructor
  · rintro ⟨h,e⟩
    rcases missing_split h with h | ht
    · exact h
    · have ha := gap_bound ht
      rw [e] at ha
      contradiction
  · rintro ⟨rfl,rfl⟩
    exact ⟨first_missing_gap,rfl⟩

#print axioms doubled_gaps
#print axioms missing_gaps
#print axioms unique_gap_two

end CeilingArray
