import PellOrbits
import FloorBridge

/-!
# The ordered solution sequence

The zero-based `term j` is the `(j+1)`-st positive integer in A081097.
Its four residue classes are the four explicitly classified Pell orbits.
-/
namespace A081097

def orbitValue (i : Fin 4) (k : ℕ) : ℤ := ((pellOrbit i k).1 + 1) / 5

def term (j : ℕ) : ℤ := orbitValue ⟨j % 4, Nat.mod_lt _ (by decide)⟩ (j / 4)

theorem five_orbitValue (i : Fin 4) (k : ℕ) :
    5 * orbitValue i k = (pellOrbit i k).1 + 1 := by
  have hp := pellOrbit_admissible i k
  obtain ⟨hx, hy, hm, hn⟩ := hp
  dsimp [orbitValue]
  omega

theorem orbitValue_pos (i : Fin 4) (k : ℕ) : 0 < orbitValue i k := by
  have hp := pellOrbit_admissible i k
  have h5 := five_orbitValue i k
  rcases hp with ⟨hx, hy, hm, hn⟩
  omega

theorem term_pos (j : ℕ) : 0 < term j := orbitValue_pos _ _

theorem orbitValue_recurrence (i : Fin 4) (k : ℕ) :
    orbitValue i (k+2) = 322 * orbitValue i (k+1) - orbitValue i k - 64 := by
  have h0 := five_orbitValue i k
  have h1 := five_orbitValue i (k+1)
  have h2 := five_orbitValue i (k+2)
  have hrec : (pellOrbit i (k+2)).1 =
      322 * (pellOrbit i (k+1)).1 - (pellOrbit i k).1 := by
    simp only [pellOrbit, Function.iterate_succ_apply', pellStep]
    ring
  omega

theorem term_block (i : Fin 4) (k : ℕ) :
    term (4*k+i) = orbitValue i k := by
  unfold term
  have hi : (i : ℕ) < 4 := i.isLt
  have hm : (4*k+(i : ℕ)) % 4 = i := by omega
  have hd : (4*k+(i : ℕ)) / 4 = k := by omega
  simp only [hd]
  congr 1
  exact Fin.ext hm

theorem term_recurrence (j : ℕ) :
    term (j+8) = 322 * term (j+4) - term j - 64 := by
  have h0 := orbitValue_recurrence ⟨j%4, Nat.mod_lt _ (by decide)⟩ (j/4)
  have hm4 : (j+4)%4 = j%4 := by omega
  have hm8 : (j+8)%4 = j%4 := by omega
  have hd4 : (j+4)/4 = j/4+1 := by omega
  have hd8 : (j+8)/4 = j/4+2 := by omega
  simpa only [term, hm4, hm8, hd4, hd8] using h0

theorem term_homogeneous_recurrence (j : ℕ) :
    term (j+9) = term (j+8) + 322*term (j+5) -
      322*term (j+4) - term (j+1) + term j := by
  have h0 := term_recurrence j
  have h1 := term_recurrence (j+1)
  simp only [show j+1+8=j+9 by omega, show j+1+4=j+5 by omega] at h1
  omega

theorem initial_terms : List.ofFn (fun i : Fin 9 => term i) =
    [1, 6, 23, 40, 273, 1870, 7343, 12816, 87841] := by
  decide +kernel

private theorem pellStep_strict {p q : ℤ × ℤ}
    (hx : p.1 < q.1) (hy : p.2 < q.2) :
    (pellStep p).1 < (pellStep q).1 ∧ (pellStep p).2 < (pellStep q).2 := by
  dsimp [pellStep]
  constructor <;> omega

private theorem iterate_strict {p q : ℤ × ℤ}
    (hx : p.1 < q.1) (hy : p.2 < q.2) (k : ℕ) :
    (pellStep^[k] p).1 < (pellStep^[k] q).1 ∧
    (pellStep^[k] p).2 < (pellStep^[k] q).2 := by
  induction k with
  | zero => exact ⟨hx, hy⟩
  | succ k ih =>
    simpa only [Function.iterate_succ_apply'] using pellStep_strict ih.1 ih.2

theorem orbitValue_lt_next_seed (i : Fin 3) (k : ℕ) :
    orbitValue i.castSucc k < orbitValue i.succ k := by
  have hx : (pellSeed i.castSucc).1 < (pellSeed i.succ).1 := by
    fin_cases i <;> decide +kernel
  have hy : (pellSeed i.castSucc).2 < (pellSeed i.succ).2 := by
    fin_cases i <;> decide +kernel
  have hi := iterate_strict hx hy k
  change (pellOrbit i.castSucc k).1 < (pellOrbit i.succ k).1 ∧ _ at hi
  have h1 := five_orbitValue i.castSucc k
  have h2 := five_orbitValue i.succ k
  omega

theorem orbitValue_last_lt_first (k : ℕ) :
    orbitValue 3 k < orbitValue 0 (k+1) := by
  have hx : (pellSeed 3).1 < (pellStep (pellSeed 0)).1 := by
    decide +kernel
  have hy : (pellSeed 3).2 < (pellStep (pellSeed 0)).2 := by
    decide +kernel
  have hi := (iterate_strict hx hy k).1
  have h1 := five_orbitValue 3 k
  have h2 := five_orbitValue 0 (k+1)
  have hshift : pellStep^[k] (pellStep (pellSeed 0)) = pellOrbit 0 (k+1) := by
    simp only [pellOrbit, Function.iterate_succ_apply]
  rw [hshift] at hi
  change (pellOrbit 3 k).1 < _ at hi
  omega

theorem term_strictMono : StrictMono term := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hj : j = 4*(j/4) + j%4 := by omega
  have hm : j%4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases h : j%4
  · have h0 := orbitValue_lt_next_seed (0 : Fin 3) (j/4)
    have e0 : j = 4*(j/4) + (0 : Fin 4) := by omega
    have e1 : j+1 = 4*(j/4) + (1 : Fin 4) := by omega
    have t0 := congrArg term e0
    have t1 := congrArg term e1
    rw [term_block] at t0 t1
    rw [t0, t1]
    exact h0
  · have h0 := orbitValue_lt_next_seed (1 : Fin 3) (j/4)
    have e0 : j = 4*(j/4) + (1 : Fin 4) := by omega
    have e1 : j+1 = 4*(j/4) + (2 : Fin 4) := by omega
    have t0 := congrArg term e0
    have t1 := congrArg term e1
    rw [term_block] at t0 t1
    rw [t0, t1]
    exact h0
  · have h0 := orbitValue_lt_next_seed (2 : Fin 3) (j/4)
    have e0 : j = 4*(j/4) + (2 : Fin 4) := by omega
    have e1 : j+1 = 4*(j/4) + (3 : Fin 4) := by omega
    have t0 := congrArg term e0
    have t1 := congrArg term e1
    rw [term_block] at t0 t1
    rw [t0, t1]
    exact h0
  · have h0 := orbitValue_last_lt_first (j/4)
    have e0 : j = 4*(j/4) + (3 : Fin 4) := by omega
    have e1 : j+1 = 4*(j/4+1) + (0 : Fin 4) := by omega
    have t0 := congrArg term e0
    have t1 := congrArg term e1
    rw [term_block] at t0 t1
    rw [t0, t1]
    exact h0

/-- Every orbit entry satisfies the literal nested-floor definition. -/
theorem term_is_source (j : ℕ) : Source (term j).toNat := by
  let i : Fin 4 := ⟨j%4, Nat.mod_lt _ (by decide)⟩
  let k := j/4
  have ht : (term j).toNat > 0 := by have := term_pos j; omega
  apply (source_iff_pell _ ht).mpr
  have hp := pellOrbit_admissible i k
  have h5 : 5 * term j = (pellOrbit i k).1+1 := five_orbitValue i k
  have hcast : ((term j).toNat : ℤ) = term j := Int.toNat_of_nonneg (term_pos j).le
  refine ⟨(pellOrbit i k).2, hp.2.1, ?_⟩
  rw [hcast]
  have he : 5*term j-1 = (pellOrbit i k).1 := by omega
  rw [he]
  exact hp.2.2.2

/-- The increasing orbit list exhausts all positive literal solutions. -/
theorem source_iff_term (n : ℕ) (hn : 0 < n) :
    Source n ↔ ∃ j : ℕ, term j = (n : ℤ) := by
  constructor
  · intro hs
    obtain ⟨y, hy, hnorm⟩ := (source_iff_pell n hn).mp hs
    have hp : PellAdmissible (5*(n : ℤ)-1, y) := by
      refine ⟨by dsimp; omega, hy, by dsimp; omega, hnorm⟩
    obtain ⟨i, k, hik⟩ := pell_classification hp
    refine ⟨4*k+i, ?_⟩
    rw [term_block]
    have hfst := congrArg Prod.fst hik
    have hv := five_orbitValue i k
    dsimp only at hfst
    omega
  · rintro ⟨j, hj⟩
    have h := term_is_source j
    simpa only [hj, Int.toNat_natCast] using h

/-- An exact enumeration theorem, including uniqueness of each index. -/
theorem source_iff_unique_term (n : ℕ) (hn : 0 < n) :
    Source n ↔ ∃! j : ℕ, term j = (n : ℤ) := by
  rw [source_iff_term n hn]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, hj, ?_⟩
    intro k hk
    exact term_strictMono.injective (hk.trans hj.symm)
  · rintro ⟨j, hj, _⟩
    exact ⟨j, hj⟩

#print axioms term_strictMono
#print axioms term_recurrence
#print axioms source_iff_unique_term
end A081097
