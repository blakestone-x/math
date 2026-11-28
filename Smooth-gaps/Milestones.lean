import Families

namespace SmoothGaps

def RowCap (n m : ℕ) (r : ℕ × ℕ) : Prop :=
  (n = r.1 → r.1+r.2 ≤ m) ∧ (n = r.2 → r.1+r.2 ≤ m) ∧
  (n = r.1+r.2 → r.1 ≤ m ∧ r.2 ≤ m)

instance (n m : ℕ) (r : ℕ × ℕ) : Decidable (RowCap n m r) := by
  unfold RowCap
  infer_instance

/-- For a gap coprime to S the gcd scale is 1. Every candidate can therefore
    be tested on rows that contain the gap as one of their three entries. -/
theorem rough_gap_value {S T : Finset ℕ} {n m : ℕ} {rows : List (ℕ × ℕ)}
    (st : S ⊆ T) (ht : Smooth T n) (rough : ∀ p ∈ S, ¬p ∣ n)
    (full : Complete T rows) (caps : ∀ r ∈ rows, RowCap n m r)
    (w : m = 0 ∨ Attains S n m) : HasValue S n m := by
  refine ⟨w, ?_⟩
  intro x hx
  obtain ⟨g, d, u, v, hg, ⟨_, hu, hv, cp, rel⟩, en, ex⟩ :=
    (attain_iff_scaled_primitive (Nat.pos_of_ne_zero ht.1)).mp hx
  have gone : g = 1 := by
    by_contra h
    obtain ⟨p, pp, pd⟩ := Nat.exists_prime_and_dvd h
    exact rough p (hg.2 (Nat.mem_primeFactors.mpr ⟨pp, pd, hg.1⟩)) (pd.trans ⟨d, en⟩)
  subst g
  simp only [one_mul] at en ex
  subst d
  subst u
  rcases rel with e | e
  · subst x
    rcases full n v ht (hv.mono st) (hu.mono st) (by simpa using cp) with hm | hm
    · exact (caps (n,v) hm).1 rfl
    · simpa [Nat.add_comm] using (caps (v,n) hm).2.1 rfl
  · subst n
    rcases full x v (hu.mono st) (hv.mono st) ht cp with hm | hm
    · exact ((caps (x,v) hm).2.2 rfl).1
    · exact ((caps (v,x) hm).2.2 (Nat.add_comm _ _)).2

def tfive31 : Finset ℕ := {2, 3, 5, 31}
def rfive31 : List (ℕ × ℕ) :=
  [(1, 1), (1, 2), (1, 3), (1, 8), (1, 4), (1, 5),
   (1, 9), (1, 15), (1, 24), (1, 80), (2, 3), (2, 25),
   (3, 5), (3, 125), (4, 5), (5, 27), (9, 16), (1, 31),
   (4, 27), (1, 124), (1, 30), (1, 960), (5, 31), (5, 243),
   (6, 25), (9, 31), (15, 16), (27, 128), (31, 50), (31, 225),
   (32, 93)]

set_option maxRecDepth 4096 in
theorem five31 (full : Complete tfive31 rfive31) : HasValue primesFive 31 256 := by
  have p31 : Smooth tfive31 31 := smooth_prime (by decide) (by decide)
  apply rough_gap_value (T := tfive31) (by decide) (p31) (by decide) full (by decide)
  have p2 : Smooth primesFive 2 := smooth_prime (by decide) (by decide)
  have p3 : Smooth primesFive 3 := smooth_prime (by decide) (by decide)
  have p5 : Smooth primesFive 5 := smooth_prime (by decide) (by decide)
  exact Or.inr ⟨p2.pow 8, 225, (p3.pow 2).mul (p5.pow 2), Or.inl rfl⟩

#print axioms five31

def tseven31 : Finset ℕ := {2, 3, 5, 7, 31}
def rseven31 : List (ℕ × ℕ) :=
  [(1, 1), (1, 2), (1, 3), (1, 8), (1, 4), (1, 7),
   (1, 5), (1, 9), (1, 15), (1, 24), (1, 80), (2, 3),
   (2, 25), (3, 5), (3, 125), (4, 5), (5, 27), (9, 16),
   (1, 6), (1, 27), (1, 48), (1, 63), (2, 7), (3, 4),
   (7, 9), (32, 49), (1, 31), (1, 49), (2, 5), (7, 25),
   (4, 27), (1, 14), (1, 20), (1, 35), (1, 125), (1, 224),
   (1, 2400), (1, 4374), (2, 243), (3, 7), (3, 25), (3, 32),
   (4, 21), (4, 45), (5, 7), (5, 9), (5, 16), (5, 49),
   (5, 1024), (7, 8), (7, 18), (7, 20), (7, 128), (7, 243),
   (8, 27), (9, 40), (15, 49), (24, 25), (25, 56), (27, 98),
   (32, 343), (49, 576), (64, 125), (81, 175), (100, 243), (1, 124),
   (1, 30), (1, 960), (5, 31), (5, 243), (6, 25), (9, 31),
   (15, 16), (27, 128), (31, 50), (31, 225), (32, 93), (1, 62),
   (1, 216), (1, 3968), (3, 28), (7, 24), (18, 31), (31, 32),
   (31, 81), (63, 961), (64, 279), (217, 512), (4, 31), (25, 31),
   (31, 49), (1, 279), (1, 6075), (1, 15624), (3, 245), (3, 4802),
   (5, 93), (7, 93), (7, 155), (7, 768), (8, 147), (8, 217),
   (9, 775), (10, 21), (14, 31), (16, 945), (25, 192), (27, 35),
   (31, 144), (31, 3969), (35, 93), (49, 75), (49, 2511), (62, 63),
   (62, 343), (81, 1519), (93, 250), (125, 3844), (243, 625), (279, 4096),
   (336, 625), (343, 432), (496, 729), (625, 2511), (961, 1440), (961, 5600),
   (2401, 22599)]

set_option maxRecDepth 4096 in
theorem seven31 (full : Complete tseven31 rseven31) : HasValue primesSeven 31 4000 := by
  have p31 : Smooth tseven31 31 := smooth_prime (by decide) (by decide)
  apply rough_gap_value (T := tseven31) (by decide) (p31) (by decide) full (by decide)
  have p2 : Smooth primesSeven 2 := smooth_prime (by decide) (by decide)
  have p3 : Smooth primesSeven 3 := smooth_prime (by decide) (by decide)
  have p5 : Smooth primesSeven 5 := smooth_prime (by decide) (by decide)
  have p7 : Smooth primesSeven 7 := smooth_prime (by decide) (by decide)
  exact Or.inr ⟨(p2.pow 5).mul (p5.pow 3), 3969, (p3.pow 4).mul (p7.pow 2), Or.inl rfl⟩

#print axioms seven31

def tfive281 : Finset ℕ := {2, 3, 5, 281}
def rfive281 : List (ℕ × ℕ) :=
  [(1, 1), (1, 2), (1, 3), (1, 8), (1, 4), (1, 5),
   (1, 9), (1, 15), (1, 24), (1, 80), (2, 3), (2, 25),
   (3, 5), (3, 125), (4, 5), (5, 27), (9, 16), (25, 256),
   (1, 1124), (81, 200)]

set_option maxRecDepth 4096 in
theorem five281 (full : Complete tfive281 rfive281) : HasValue primesFive 281 256 := by
  have p281 : Smooth tfive281 281 := smooth_prime (by decide) (by decide)
  apply rough_gap_value (T := tfive281) (by decide) (p281) (by decide) full (by decide)
  have p2 : Smooth primesFive 2 := smooth_prime (by decide) (by decide)
  have p5 : Smooth primesFive 5 := smooth_prime (by decide) (by decide)
  exact Or.inr ⟨p2.pow 8, 25, p5.pow 2, Or.inr rfl⟩

#print axioms five281

def tseven1849 : Finset ℕ := {2, 3, 5, 7, 43}
def rseven1849 : List (ℕ × ℕ) :=
  [(1, 1), (1, 2), (1, 3), (1, 8), (1, 4), (1, 7),
   (1, 5), (1, 9), (1, 15), (1, 24), (1, 80), (2, 3),
   (2, 25), (3, 5), (3, 125), (4, 5), (5, 27), (9, 16),
   (1, 6), (1, 27), (1, 48), (1, 63), (2, 7), (3, 4),
   (7, 9), (32, 49), (1, 49), (2, 5), (7, 25), (1, 14),
   (1, 20), (1, 35), (1, 125), (1, 224), (1, 2400), (1, 4374),
   (2, 243), (3, 7), (3, 25), (3, 32), (4, 21), (4, 45),
   (5, 7), (5, 9), (5, 16), (5, 49), (5, 1024), (7, 8),
   (7, 18), (7, 20), (7, 128), (7, 243), (8, 27), (9, 40),
   (15, 49), (24, 25), (25, 56), (27, 98), (32, 343), (49, 576),
   (64, 125), (81, 175), (100, 243), (1, 128), (16, 27), (1, 343),
   (1, 215), (2, 43), (3, 40), (4, 125), (5, 43), (5, 81),
   (18, 25), (32, 43), (43, 200), (125, 387), (1, 42), (6, 43),
   (7, 36), (21, 43), (43, 686), (7, 43), (8, 35), (128, 215),
   (1, 300), (1, 5375), (1, 512000), (3, 172), (5, 387), (9, 215),
   (15, 28), (16, 9245), (20, 43), (25, 147), (27, 43), (28, 215),
   (43, 125), (43, 245), (43, 300), (43, 405), (43, 1280), (45, 256),
   (49, 80), (49, 86), (49, 1800), (63, 625), (64, 1161), (80, 2107),
   (81, 134375), (301, 324), (729, 1120), (1075, 15309), (2401, 5375)]

set_option maxRecDepth 4096 in
theorem seven1849 (full : Complete tseven1849 rseven1849) : HasValue primesSeven 1849 1800 := by
  have p43 : Smooth tseven1849 43 := smooth_prime (by decide) (by decide)
  apply rough_gap_value (T := tseven1849) (by decide) (p43.pow 2) (by decide) full (by decide)
  have p2 : Smooth primesSeven 2 := smooth_prime (by decide) (by decide)
  have p3 : Smooth primesSeven 3 := smooth_prime (by decide) (by decide)
  have p5 : Smooth primesSeven 5 := smooth_prime (by decide) (by decide)
  have p7 : Smooth primesSeven 7 := smooth_prime (by decide) (by decide)
  exact Or.inr ⟨((p2.pow 3).mul (p3.pow 2)).mul (p5.pow 2), 49, p7.pow 2, Or.inr rfl⟩

#print axioms seven1849

def tfive583 : Finset ℕ := {2, 3, 5, 11, 53}
def rfive583 : List (ℕ × ℕ) :=
  [(1, 1), (1, 2), (1, 3), (1, 8), (1, 4), (1, 5),
   (1, 9), (1, 15), (1, 24), (1, 80), (2, 3), (2, 25),
   (3, 5), (3, 125), (4, 5), (5, 27), (9, 16), (1, 11),
   (1, 32), (1, 242), (2, 9), (3, 8), (11, 16), (1, 10),
   (4, 121), (5, 11), (1, 53), (1, 44), (1, 54), (1, 99),
   (1, 120), (3, 22), (4, 11), (5, 6), (5, 22), (8, 25),
   (9, 11), (9, 55), (11, 25), (11, 64), (25, 96), (25, 704),
   (32, 243), (40, 81), (44, 81), (81, 1250), (121, 135), (625, 2048),
   (11, 53), (1, 159), (3, 50), (5, 48), (8, 45), (9, 256),
   (25, 81), (27, 53), (53, 72), (53, 75), (53, 3072), (64, 6561),
   (9, 44), (2, 53), (1, 264), (1, 2915), (6, 1325), (11, 625),
   (15, 106), (20, 33), (22, 53), (22, 243), (32, 265), (53, 55),
   (53, 352), (100, 1331), (121, 144), (121, 3975), (125, 352), (125, 3267),
   (128, 477), (216, 2809), (243, 605), (2809, 2816)]

set_option maxRecDepth 4096 in
theorem five583 (full : Complete tfive583 rfive583) : HasValue primesFive 583 0 := by
  have p11 : Smooth tfive583 11 := smooth_prime (by decide) (by decide)
  have p53 : Smooth tfive583 53 := smooth_prime (by decide) (by decide)
  apply rough_gap_value (T := tfive583) (by decide) (p11.mul p53) (by decide) full (by decide)
  exact Or.inl rfl

#print axioms five583

def tseven3737 : Finset ℕ := {2, 3, 5, 7, 37, 101}
def rseven3737 : List (ℕ × ℕ) :=
  [(1, 1), (1, 2), (1, 3), (1, 8), (1, 4), (1, 7),
   (1, 5), (1, 9), (1, 15), (1, 24), (1, 80), (2, 3),
   (2, 25), (3, 5), (3, 125), (4, 5), (5, 27), (9, 16),
   (1, 6), (1, 27), (1, 48), (1, 63), (2, 7), (3, 4),
   (7, 9), (32, 49), (1, 49), (2, 5), (7, 25), (1, 14),
   (1, 20), (1, 35), (1, 125), (1, 224), (1, 2400), (1, 4374),
   (2, 243), (3, 7), (3, 25), (3, 32), (4, 21), (4, 45),
   (5, 7), (5, 9), (5, 16), (5, 49), (5, 1024), (7, 8),
   (7, 18), (7, 20), (7, 128), (7, 243), (8, 27), (9, 40),
   (15, 49), (24, 25), (25, 56), (27, 98), (32, 343), (49, 576),
   (64, 125), (81, 175), (100, 243), (1, 36), (27, 37), (5, 32),
   (27, 101), (1, 100), (1, 74), (1, 999), (3, 37), (8, 37),
   (10, 27), (12, 25), (25, 999), (37, 125), (37, 32768), (128, 2997),
   (640, 729), (1, 111), (1, 147), (3, 256), (3, 1369), (7, 74),
   (9, 28), (12, 37), (16, 21), (16, 243), (2, 35), (25, 49),
   (1, 404), (5, 96), (20, 81), (24, 101), (101, 1024), (3, 98),
   (7, 101), (7, 505), (37, 64), (1, 1295), (4, 185), (5, 37),
   (7, 30), (7, 185), (9, 250), (10, 333), (14, 111), (25, 567),
   (25, 1344), (27, 148), (27, 343), (28, 50625), (35, 37), (37, 63),
   (37, 75), (37, 98), (37, 243), (37, 588), (49, 111), (64, 111),
   (125, 259), (144, 1225), (185, 256), (196, 729), (333, 1715), (343, 2025),
   (625, 1776), (1813, 2187), (1, 504), (4, 101), (5, 10201), (21, 80),
   (25, 101), (27, 175), (32, 675), (40, 303), (45, 56), (49, 101),
   (64, 441), (81, 12544), (101, 144), (101, 1600), (101, 3024), (125, 784),
   (128, 175), (162, 343), (224, 505), (404, 625), (1875, 32768), (16807, 81608),
   (27, 74), (729, 9472), (1369, 2727), (10, 101), (16, 909), (505, 864),
   (7, 296), (37, 404), (101, 343), (256, 242501), (2738, 823543), (74, 101),
   (5, 1813), (37, 6363), (45, 1369), (49, 1616), (84, 101), (101, 259),
   (101, 1369), (259, 1616), (324, 4625), (625, 707), (707, 1480), (729, 29896),
   (875, 3232), (999, 10201), (3125, 11211), (4725, 5476), (9583, 10100)]

set_option maxRecDepth 4096 in
theorem seven3737 (full : Complete tseven3737 rseven3737) : HasValue primesSeven 3737 0 := by
  have p37 : Smooth tseven3737 37 := smooth_prime (by decide) (by decide)
  have p101 : Smooth tseven3737 101 := smooth_prime (by decide) (by decide)
  apply rough_gap_value (T := tseven3737) (by decide) (p37.mul p101) (by decide) full (by decide)
  exact Or.inl rfl

#print axioms seven3737

end SmoothGaps
