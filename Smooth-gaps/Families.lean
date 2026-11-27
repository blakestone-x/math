import Gap

namespace SmoothGaps

/- Numerical rows are the unordered summands from von Känel and Matschke, Table 1.
   Their completeness appears explicitly as a theorem hypothesis. -/

def primesFive : Finset ℕ := {2, 3, 5}
def rowsFive : List (ℕ × ℕ) :=
  [(1, 1), (1, 2), (1, 3), (1, 8), (1, 4), (1, 5),
   (1, 9), (1, 15), (1, 24), (1, 80), (2, 3), (2, 25),
   (3, 5), (3, 125), (4, 5), (5, 27), (9, 16)]

theorem maximalFive (complete : Complete primesFive rowsFive)
    {h : ℕ} (hh : Smooth primesFive h) : HasValue primesFive h (h*81) := by
  apply smooth_gap_maximum (rows := rowsFive) complete _ (by decide) _ hh
  · decide
  · have p2 : Smooth primesFive 2 := smooth_prime (by decide) (by decide)
    have p3 : Smooth primesFive 3 := smooth_prime (by decide) (by decide)
    have p5 : Smooth primesFive 5 := smooth_prime (by decide) (by decide)
    exact ⟨p3.pow 4, 80, (p2.pow 4).mul p5, Or.inl rfl⟩

def primesSeven : Finset ℕ := {2, 3, 5, 7}
def rowsSeven : List (ℕ × ℕ) :=
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
   (64, 125), (81, 175), (100, 243)]

theorem maximalSeven (complete : Complete primesSeven rowsSeven)
    {h : ℕ} (hh : Smooth primesSeven h) : HasValue primesSeven h (h*4375) := by
  apply smooth_gap_maximum (rows := rowsSeven) complete _ (by decide) _ hh
  · decide
  · have p2 : Smooth primesSeven 2 := smooth_prime (by decide) (by decide)
    have p3 : Smooth primesSeven 3 := smooth_prime (by decide) (by decide)
    have p5 : Smooth primesSeven 5 := smooth_prime (by decide) (by decide)
    have p7 : Smooth primesSeven 7 := smooth_prime (by decide) (by decide)
    exact ⟨(p5.pow 4).mul p7, 4374, p2.mul (p3.pow 7), Or.inl rfl⟩

def rowsFiveWithEleven : List (ℕ × ℕ) :=
  [(1, 1), (1, 2), (1, 3), (1, 8), (1, 4), (1, 5),
   (1, 9), (1, 15), (1, 24), (1, 80), (2, 3), (2, 25),
   (3, 5), (3, 125), (4, 5), (5, 27), (9, 16), (1, 11),
   (1, 32), (1, 242), (2, 9), (3, 8), (11, 16), (1, 10),
   (4, 121), (5, 11), (1, 44), (1, 54), (1, 99), (1, 120),
   (3, 22), (4, 11), (5, 6), (5, 22), (8, 25), (9, 11),
   (9, 55), (11, 25), (11, 64), (25, 96), (25, 704), (32, 243),
   (40, 81), (44, 81), (81, 1250), (121, 135), (625, 2048)]

set_option maxRecDepth 4096 in
theorem absentFive (complete : Complete (insert 11 primesFive) rowsFiveWithEleven)
    (k : ℕ) {h : ℕ} (hh : Smooth primesFive h) :
    HasValue primesFive (11^(4+k)*h) 0 := by
  apply missing_prime_power (by decide) (by decide) complete _ k hh
  decide

#print axioms absentFive

def rowsSevenWithEleven : List (ℕ × ℕ) :=
  [(1, 1), (1, 2), (1, 3), (1, 8), (1, 4), (1, 7),
   (1, 5), (1, 9), (1, 15), (1, 24), (1, 80), (2, 3),
   (2, 25), (3, 5), (3, 125), (4, 5), (5, 27), (9, 16),
   (1, 6), (1, 27), (1, 48), (1, 63), (2, 7), (3, 4),
   (7, 9), (32, 49), (1, 11), (1, 32), (1, 242), (2, 9),
   (3, 8), (11, 16), (1, 49), (2, 5), (7, 25), (1, 10),
   (4, 121), (5, 11), (4, 7), (7, 121), (1, 14), (1, 20),
   (1, 35), (1, 125), (1, 224), (1, 2400), (1, 4374), (2, 243),
   (3, 7), (3, 25), (3, 32), (4, 21), (4, 45), (5, 7),
   (5, 9), (5, 16), (5, 49), (5, 1024), (7, 8), (7, 18),
   (7, 20), (7, 128), (7, 243), (8, 27), (9, 40), (15, 49),
   (24, 25), (25, 56), (27, 98), (32, 343), (49, 576), (64, 125),
   (81, 175), (100, 243), (1, 44), (1, 54), (1, 99), (1, 120),
   (3, 22), (4, 11), (5, 6), (5, 22), (8, 25), (9, 11),
   (9, 55), (11, 25), (11, 64), (25, 96), (25, 704), (32, 243),
   (40, 81), (44, 81), (81, 1250), (121, 135), (625, 2048), (1, 21),
   (1, 98), (3, 11), (4, 77), (7, 11), (7, 81), (8, 1323),
   (9, 112), (9, 343), (11, 21), (16, 33), (22, 27), (27, 512),
   (49, 72), (1, 55), (1, 175), (5, 44), (11, 14), (11, 245),
   (11, 3125), (343, 625), (1, 384), (1, 440), (1, 539), (1, 3024),
   (1, 9800), (2, 33), (2, 75), (3, 77), (3, 242), (3, 1372),
   (5, 28), (5, 72), (5, 121), (5, 891), (6, 49), (7, 15),
   (7, 33), (7, 48), (7, 125), (7, 3993), (7, 5625), (8, 55),
   (9, 35), (9, 616), (10, 11), (11, 24), (11, 45), (11, 49),
   (11, 70), (11, 189), (11, 675), (11, 864), (14, 121), (16, 105),
   (16, 875), (20, 343), (21, 100), (22, 125), (25, 63), (25, 231),
   (25, 2376), (27, 28), (27, 50), (32, 45), (35, 64), (35, 1296),
   (48, 77), (49, 50), (49, 176), (49, 275), (49, 16335), (54, 121),
   (55, 288), (55, 512), (55, 729), (75, 121), (77, 243), (81, 605),
   (99, 125), (99, 2401), (121, 320), (121, 504), (125, 847), (128, 147),
   (128, 3645), (245, 484), (297, 343), (363, 512), (384, 1331), (648, 3125),
   (1125, 8192), (1331, 9604), (2048, 2187), (3584, 14641)]

set_option maxRecDepth 4096 in
theorem absentSeven (complete : Complete (insert 11 primesSeven) rowsSevenWithEleven)
    (k : ℕ) {h : ℕ} (hh : Smooth primesSeven h) :
    HasValue primesSeven (11^(5+k)*h) 0 := by
  apply missing_prime_power (by decide) (by decide) complete _ k hh
  decide

#print axioms absentSeven

#print axioms attain_iff_scaled_primitive
#print axioms smooth_gap_maximum
#print axioms maximalFive
#print axioms maximalSeven

end SmoothGaps
