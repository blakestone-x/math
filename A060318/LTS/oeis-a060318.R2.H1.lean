import OMAReductions.R_oeis_a060318_R2

-- Credit: @blakestone-x
namespace A060318Certificate

structure Row where
  a : ℕ
  b : ℕ
  c : ℕ
  n : ℕ
  deriving DecidableEq, Repr

/-- The progression with first element lo and difference d. -/
def Fits (lo d x : ℕ) : Prop := ∃ q, x = lo + d*q

def Covers (r : Row) (L T : ℕ) (x : Row) : Prop :=
  Fits r.a L x.a ∧ Fits r.b L x.b ∧ Fits r.c L x.c ∧ Fits r.n T x.n

def residues (base lo d m : ℕ) : List ℕ :=
  let first := base^lo % m
  let step := base^d % m
  if step = 1 then [first] else if step = 0 then [first, 0]
  else if first = 0 then [0] else List.range m

theorem residue_mem (base lo d x m : ℕ) (hm : 0 < m) (h : Fits lo d x) :
    base^x % m ∈ residues base lo d m := by
  obtain ⟨q,rfl⟩ := h
  have e : base^(lo+d*q) % m = (base^lo % m * (base^d % m)^q) % m := by
    rw [pow_add, pow_mul]
    exact ((Nat.mod_modEq _ _).symm.mul ((Nat.mod_modEq _ _).symm.pow q))
  rw [e]
  unfold residues
  dsimp only
  split
  · rename_i he
    simp [he]
  split
  · rename_i he
    cases q <;> simp [he]
  split
  · rename_i he
    simp [he]
  exact List.mem_range.mpr (Nat.mod_lt _ hm)

def compatible (r : Row) (L T m : ℕ) : Bool :=
  m == 0 || (residues 2 r.n T m).any (fun v =>
    (residues 3 r.a L m).any (fun a => (residues 3 r.b L m).any (fun b =>
      (residues 3 r.c L m).any (fun c => v == (1+a+b+c)%m))))

theorem compatible_of_eq (r x : Row) (L T m : ℕ) (h : Covers r L T x)
    (he : 2^x.n = 1+3^x.a+3^x.b+3^x.c) : compatible r L T m = true := by
  rcases h with ⟨ha,hb,hc,hn⟩
  by_cases hm : m=0
  · simp [compatible, hm]
  simp only [compatible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
  right
  refine ⟨_, residue_mem _ _ _ _ _ (by omega) hn, _, residue_mem _ _ _ _ _ (by omega) ha,
    _, residue_mem _ _ _ _ _ (by omega) hb, _, residue_mem _ _ _ _ _ (by omega) hc, ?_⟩
  rw [he]
  exact (((Nat.ModEq.refl 1).add (Nat.mod_modEq _ _).symm).add (Nat.mod_modEq _ _).symm).add
    (Nat.mod_modEq _ _).symm

def lifts (lo d f : ℕ) : List ℕ := (List.range f).map (fun j => lo+d*j)

theorem lift_exists (lo d f x : ℕ) (hf : 0 < f) (h : Fits lo d x) :
    ∃ l ∈ lifts lo d f, Fits l (d*f) x := by
  obtain ⟨q,rfl⟩ := h
  refine ⟨_, List.mem_map.mpr ⟨q%f, List.mem_range.mpr (Nat.mod_lt _ hf), rfl⟩, q/f, ?_⟩
  have eq := Nat.mod_add_div q f
  calc
    lo+d*q = lo+d*(q%f + f*(q/f)) := by rw [eq]
    _ = _ := by ring

structure Stage where
  l : ℕ
  t : ℕ
  moduli : List ℕ

def children (r : Row) (L T : ℕ) (s : Stage) : List Row := do
  let a ← lifts r.a L s.l
  let b ← lifts r.b L s.l
  let c ← lifts r.c L s.l
  let n ← lifts r.n T s.t
  let u := Row.mk a b c n
  if s.moduli.all (compatible u (L*s.l) (T*s.t)) then pure u else []

theorem child_exists (r x : Row) (L T : ℕ) (s : Stage) (hl : 0 < s.l) (ht : 0 < s.t)
    (h : Covers r L T x) (he : 2^x.n = 1+3^x.a+3^x.b+3^x.c) :
    ∃ u ∈ children r L T s, Covers u (L*s.l) (T*s.t) x := by
  obtain ⟨ha,hb,hc,hn⟩ := h
  obtain ⟨a,am,af⟩ := lift_exists _ _ _ _ hl ha
  obtain ⟨b,bm,bf⟩ := lift_exists _ _ _ _ hl hb
  obtain ⟨c,cm,cf⟩ := lift_exists _ _ _ _ hl hc
  obtain ⟨n,nm,nf⟩ := lift_exists _ _ _ _ ht hn
  let u := Row.mk a b c n
  have cover : Covers u (L*s.l) (T*s.t) x := ⟨af,bf,cf,nf⟩
  have ok : s.moduli.all (compatible u (L*s.l) (T*s.t)) = true :=
    List.all_eq_true.mpr (fun m _ => compatible_of_eq u x _ _ m cover he)
  refine ⟨u, ?_, cover⟩
  unfold children
  simp only [List.bind_eq_flatMap, List.mem_flatMap]
  exact ⟨a,am,b,bm,c,cm,n,nm,by simpa [u] using ok⟩

def run (L T : ℕ) (rows : List Row) : List Stage → List Row
  | [] => rows
  | s::ss => run (L*s.l) (T*s.t) (rows.flatMap (fun r => children r L T s)) ss

theorem run_covers (x : Row) (he : 2^x.n = 1+3^x.a+3^x.b+3^x.c)
    (L T : ℕ) (rows : List Row) (ss : List Stage) (hs : ∀ s ∈ ss, 0 < s.l ∧ 0 < s.t)
    (h : ∃ r ∈ rows, Covers r L T x) : ∃ r, r ∈ run L T rows ss := by
  induction ss generalizing L T rows with
  | nil =>
    obtain ⟨r,hr,_⟩ := h
    exact ⟨r,hr⟩
  | cons s ss ih =>
    obtain ⟨r,hr,cover⟩ := h
    obtain ⟨hl,ht⟩ := hs s (by simp)
    obtain ⟨u,hu,hu'⟩ := child_exists r x L T s hl ht cover he
    exact ih _ _ _ (fun j hj => hs j (by simp [hj])) ⟨u,List.mem_flatMap.mpr ⟨r,hr,hu⟩,hu'⟩

def stages : List Stage := [
  ⟨2,1,[8]⟩, ⟨2,4,[16,5]⟩, ⟨3,3,[7,13]⟩, ⟨1,3,[73]⟩,
  ⟨4,4,[17,97,577]⟩, ⟨1,5,[41]⟩, ⟨1,9,[6481,243]⟩,
  ⟨2,1,[128]⟩, ⟨2,1,[256]⟩, ⟨2,1,[512]⟩, ⟨2,1,[257,243]⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem sieve_empty : run 1 1 [⟨0,0,0,9⟩] stages = [] := by decide +kernel

theorem no_three (n a b c : ℕ) (hn : 8 < n) : 2^n ≠ 1+3^a+3^b+3^c := by
  intro e
  let x := Row.mk a b c n
  have pos : ∀ s ∈ stages, 0 < s.l ∧ 0 < s.t := by
    intro s hs
    simp only [stages, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h|h|h|h|h|h|h|h|h|h|h <;> subst s <;> decide
  have h : Covers ⟨0,0,0,9⟩ 1 1 x :=
    ⟨⟨a, by simp [x]⟩, ⟨b,by simp [x]⟩, ⟨c,by simp [x]⟩, ⟨n-9, by dsimp [x]; omega⟩⟩
  obtain ⟨r, hr⟩ := run_covers x e 1 1 [⟨0,0,0,9⟩] stages pos ⟨_,by simp,h⟩
  rw [sieve_empty] at hr
  exact List.not_mem_nil hr

theorem three_powers_excluded (s : Finset ℕ) (n : ℕ) (hs : s.card = 3) (hn : 8 < n) :
    2^n ≠ 1 + ∑ i ∈ s, 3^i := by
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hs
  simpa [Finset.sum_insert, hab, hac, hbc, Nat.add_assoc] using no_three n a b c hn

end A060318Certificate

theorem OMA.solution : OMA.R_oeis_a060318_R2.H1 := by
  intro s n hs hn
  exact A060318Certificate.three_powers_excluded s n hs hn
