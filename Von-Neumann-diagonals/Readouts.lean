import Cross
import Checkerboard

namespace VonNeumann

private theorem bg62 (n : ℕ) : background 62 n=false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [background,ih]; decide

private def diagTest (n i : ℕ) := cell 62 n i i == decide (0 < i ∧ 2*i ≤ n)

private theorem diag_mask (n i : ℕ) (hn : 2 ≤ n) :
    description n i i=some (decide (0 < i ∧ 2*i ≤ n)) := by
  have even : (i+i)%2=0 := by omega
  have strip : i ≤ i+2 := by omega
  simp only [description,mask,location,strip,even,and_self,decide_true,Bool.and_true]
  split_ifs <;> congr 1 <;> first | (apply decide_eq_decide.mpr; omega) | (symm; apply decide_eq_true; omega) | (symm; apply decide_eq_false; omega)

theorem diagonal62 (n i : ℕ) (hn : 2 ≤ n) : cell 62 n i i=decide (0 < i ∧ 2*i ≤ n) := by
  by_cases large : 7 ≤ n
  · have h := invariant62 n large i i
    rw [diag_mask n i hn] at h
    simpa [fits,eq_comm] using h
  by_cases far : n < i
  · rw [outside 62 n i i (Or.inl far),bg62]
    simp [show ¬(0 < i ∧ 2*i ≤ n) by omega]
  have cert : (List.range 5).all (fun n => (List.range 7).all (diagTest (n+2)))=true := by decide +kernel
  have p := checked cert (show n-2 < 5 by omega) (show i < 7 by omega)
  rw [show n-2+2=n by omega] at p
  exact beq_iff_eq.mp p

theorem diagonal65_even (rule m i : ℕ) (hr : rule=65 ∨ rule=321 ∨ rule=323) (hm : 3 ≤ m) :
    cell rule (2*m) i i=decide (i ≤ 1) := by
  rw [(cross_shapes rule m hr hm).1]
  by_cases z : i=0 <;> by_cases o : i=1 <;> simp_all [even65,evenShape,axis]; omega

theorem diagonal65_odd (rule m i : ℕ) (hr : rule=65 ∨ rule=321 ∨ rule=323) (hm : 2 ≤ m) :
    cell rule (2*m+1) i i=decide (1 < i) := by
  by_cases high : 3 ≤ m
  · rw [(cross_shapes rule m hr high).2]
    by_cases z : i=0 <;> by_cases o : i=1 <;> simp_all [odd65,oddDefects,axis] <;> omega
  have em : m=2 := by omega
  subst m
  by_cases far : 5 < i
  · rw [outside rule 5 i i (Or.inl far)]
    rw [show decide (1 < i)=true from decide_eq_true (by omega)]
    rcases hr with rfl|rfl|rfl <;> decide
  have cert : (List.range 6).all (fun x => cell rule 5 x x == decide (1 < x))=true := by
    rcases hr with rfl|rfl|rfl <;> decide +kernel
  exact beq_iff_eq.mp (List.all_eq_true.mp cert i (List.mem_range.mpr (by omega)))

def diagonal (rule n : ℕ) := (List.range (n+1)).map (fun i => cell rule n i i)

def runs (front ones back : ℕ) : List Bool :=
  (List.replicate front false ++ List.replicate ones true) ++ List.replicate back false

theorem runs_eq (rule n f w b : ℕ) (h : f+w+b=n+1)
    (bits : ∀ i < n+1, cell rule n i i=decide (f ≤ i ∧ i < f+w)) : diagonal rule n=runs f w b := by
  apply List.ext_getElem
  · simp [diagonal,runs]; omega
  · intro i h₁ _
    have hi : i < n+1 := by simpa [diagonal] using h₁
    simp only [diagonal,List.getElem_map,List.getElem_range,bits i hi,runs,List.getElem_append,
      List.length_append,List.length_replicate,List.getElem_replicate]
    split_ifs <;> simp_all

theorem word62 (n : ℕ) (hn : 2 ≤ n) : diagonal 62 n=runs 1 (n/2) ((n+1)/2) := by
  apply runs_eq <;> try omega
  intro i _; rw [diagonal62 n i hn]; apply decide_eq_decide.mpr; omega

theorem word65_even (m : ℕ) (hm : 3 ≤ m) : diagonal 65 (2*m)=runs 0 2 (2*m-1) := by
  apply runs_eq <;> try omega
  intro i _; rw [diagonal65_even 65 m i (Or.inl rfl) hm]; apply decide_eq_decide.mpr; omega

theorem word65_odd (m : ℕ) (hm : 2 ≤ m) : diagonal 65 (2*m+1)=runs 2 (2*m) 0 := by
  apply runs_eq <;> try omega
  intro i _; rw [diagonal65_odd 65 m i (Or.inl rfl) hm]; apply decide_eq_decide.mpr; omega

theorem word73 (n : ℕ) (hn : 4 ≤ n) : diagonal 73 n=List.replicate (n+1) (decide (n%2=1)) := by
  simp [diagonal,uniform73 n hn]

def repunit (base : ℕ) : ℕ → ℕ | 0 => 0 | k+1 => base*repunit base k+1

def readWord (base : ℕ) (digits : List Bool) (start : ℕ) :=
  digits.foldl (fun a d => base*a+d.toNat) start

private theorem constant_digits (b : ℕ) (d : Bool) (n a : ℕ) :
    readWord b (List.replicate n d) a=b^n*a+d.toNat*repunit b n := by
  induction n with
  | zero => simp [readWord,repunit]
  | succ n ih =>
    rw [List.replicate_succ']
    simp only [readWord,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change b*(readWord b (List.replicate n d) a)+d.toNat=_
    rw [ih,repunit,pow_succ]; ring

theorem read_runs (b f w t : ℕ) : readWord b (runs f w t) 0=b^t*repunit b w := by
  unfold runs readWord
  rw [List.foldl_append,List.foldl_append]
  change readWord b _ (readWord b _ (readWord b _ 0))=_
  simp [constant_digits]

theorem reverse_runs (f w t : ℕ) : (runs f w t).reverse=runs t w f := by simp [runs,List.append_assoc]

#print axioms word62
#print axioms word65_even
#print axioms word65_odd
#print axioms word73
#print axioms read_runs
end VonNeumann
