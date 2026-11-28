import Counts

namespace Kimberling288511
open Letter

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option trace.profiler false

def RecurrenceAt (f : ℕ → ℤ) (n : ℕ) : Prop :=
  f (n+13) = 2*f (n+12) - f (n+11) + 2*f (n+10) - 4*f (n+9) +
    4*f (n+8) - 4*f (n+7) + 4*f (n+6) - 4*f (n+5) + 4*f (n+4) -
    3*f (n+3) + 2*f (n+2) - 3*f (n+1) + 2*f n

private theorem phase_certificate0 (a b c t : ℤ) :
    RecurrenceAt (fun k => observe (future k ⟨0,a,b,c,t⟩)) 0 := by
  have h1 : future 1 ⟨0,a,b,c,t⟩ = ⟨1,2*c,a + c,b,t + 1⟩ := by
    rw [future]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h2 : future 2 ⟨0,a,b,c,t⟩ = ⟨2,2*b + 2,b + 2*c,a + c + 1,t + 1⟩ := by
    rw [future, h1]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h3 : future 3 ⟨0,a,b,c,t⟩ = ⟨3,2*a + 2*c + 2,a + 2*b + c + 3,b + 2*c,t + 2⟩ := by
    rw [future, h2]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h4 : future 4 ⟨0,a,b,c,t⟩ = ⟨4,2*b + 4*c + 1,2*a + b + 4*c + 2,a + 2*b + c + 4,t + 3⟩ := by
    rw [future, h3]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h5 : future 5 ⟨0,a,b,c,t⟩ = ⟨5,2*a + 4*b + 2*c + 9,a + 4*b + 5*c + 5,2*a + b + 4*c + 2,t + 4⟩ := by
    rw [future, h4]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h6 : future 6 ⟨0,a,b,c,t⟩ = ⟨6,4*a + 2*b + 8*c + 5,4*a + 5*b + 6*c + 11,a + 4*b + 5*c + 6,t + 4⟩ := by
    rw [future, h5]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h7 : future 7 ⟨0,a,b,c,t⟩ = ⟨7,2*a + 8*b + 10*c + 12,5*a + 6*b + 13*c + 11,4*a + 5*b + 6*c + 12,t + 5⟩ := by
    rw [future, h6]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h8 : future 8 ⟨0,a,b,c,t⟩ = ⟨8,8*a + 10*b + 12*c + 25,6*a + 13*b + 16*c + 24,5*a + 6*b + 13*c + 12,t + 5⟩ := by
    rw [future, h7]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h9 : future 9 ⟨0,a,b,c,t⟩ = ⟨9,10*a + 12*b + 26*c + 24,13*a + 16*b + 25*c + 37,6*a + 13*b + 16*c + 24,t + 6⟩ := by
    rw [future, h8]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h10 : future 10 ⟨0,a,b,c,t⟩ = ⟨0,12*a + 26*b + 32*c + 51,16*a + 25*b + 42*c + 48,13*a + 16*b + 25*c + 38,t + 7⟩ := by
    rw [future, h9]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h11 : future 11 ⟨0,a,b,c,t⟩ = ⟨1,26*a + 32*b + 50*c + 76,25*a + 42*b + 57*c + 89,16*a + 25*b + 42*c + 48,t + 8⟩ := by
    rw [future, h10]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h12 : future 12 ⟨0,a,b,c,t⟩ = ⟨2,32*a + 50*b + 84*c + 98,42*a + 57*b + 92*c + 124,25*a + 42*b + 57*c + 90,t + 8⟩ := by
    rw [future, h11]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h13 : future 13 ⟨0,a,b,c,t⟩ = ⟨3,50*a + 84*b + 114*c + 180,57*a + 92*b + 141*c + 188,42*a + 57*b + 92*c + 124,t + 9⟩ := by
    rw [future, h12]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  simp only [RecurrenceAt, zero_add, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  norm_num [observe, front, tail, encode, block, future] <;> ring

#print axioms phase_certificate0

private theorem phase_certificate1 (a b c t : ℤ) :
    RecurrenceAt (fun k => observe (future k ⟨1,a,b,c,t⟩)) 0 := by
  have h1 : future 1 ⟨1,a,b,c,t⟩ = ⟨2,2*c + 2,a + c,b + 1,t⟩ := by
    rw [future]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h2 : future 2 ⟨1,a,b,c,t⟩ = ⟨3,2*b + 2,b + 2*c + 3,a + c,t + 1⟩ := by
    rw [future, h1]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h3 : future 3 ⟨1,a,b,c,t⟩ = ⟨4,2*a + 2*c + 1,a + 2*b + c + 2,b + 2*c + 4,t + 2⟩ := by
    rw [future, h2]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h4 : future 4 ⟨1,a,b,c,t⟩ = ⟨5,2*b + 4*c + 9,2*a + b + 4*c + 5,a + 2*b + c + 2,t + 3⟩ := by
    rw [future, h3]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h5 : future 5 ⟨1,a,b,c,t⟩ = ⟨6,2*a + 4*b + 2*c + 5,a + 4*b + 5*c + 11,2*a + b + 4*c + 6,t + 3⟩ := by
    rw [future, h4]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h6 : future 6 ⟨1,a,b,c,t⟩ = ⟨7,4*a + 2*b + 8*c + 12,4*a + 5*b + 6*c + 11,a + 4*b + 5*c + 12,t + 4⟩ := by
    rw [future, h5]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h7 : future 7 ⟨1,a,b,c,t⟩ = ⟨8,2*a + 8*b + 10*c + 25,5*a + 6*b + 13*c + 24,4*a + 5*b + 6*c + 12,t + 4⟩ := by
    rw [future, h6]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h8 : future 8 ⟨1,a,b,c,t⟩ = ⟨9,8*a + 10*b + 12*c + 24,6*a + 13*b + 16*c + 37,5*a + 6*b + 13*c + 24,t + 5⟩ := by
    rw [future, h7]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h9 : future 9 ⟨1,a,b,c,t⟩ = ⟨0,10*a + 12*b + 26*c + 51,13*a + 16*b + 25*c + 48,6*a + 13*b + 16*c + 38,t + 6⟩ := by
    rw [future, h8]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h10 : future 10 ⟨1,a,b,c,t⟩ = ⟨1,12*a + 26*b + 32*c + 76,16*a + 25*b + 42*c + 89,13*a + 16*b + 25*c + 48,t + 7⟩ := by
    rw [future, h9]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h11 : future 11 ⟨1,a,b,c,t⟩ = ⟨2,26*a + 32*b + 50*c + 98,25*a + 42*b + 57*c + 124,16*a + 25*b + 42*c + 90,t + 7⟩ := by
    rw [future, h10]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h12 : future 12 ⟨1,a,b,c,t⟩ = ⟨3,32*a + 50*b + 84*c + 180,42*a + 57*b + 92*c + 188,25*a + 42*b + 57*c + 124,t + 8⟩ := by
    rw [future, h11]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h13 : future 13 ⟨1,a,b,c,t⟩ = ⟨4,50*a + 84*b + 114*c + 249,57*a + 92*b + 141*c + 304,42*a + 57*b + 92*c + 189,t + 9⟩ := by
    rw [future, h12]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  simp only [RecurrenceAt, zero_add, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  norm_num [observe, front, tail, encode, block, future] <;> ring

#print axioms phase_certificate1

private theorem phase_certificate2 (a b c t : ℤ) :
    RecurrenceAt (fun k => observe (future k ⟨2,a,b,c,t⟩)) 0 := by
  have h1 : future 1 ⟨2,a,b,c,t⟩ = ⟨3,2*c,a + c,b,t + 1⟩ := by
    rw [future]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h2 : future 2 ⟨2,a,b,c,t⟩ = ⟨4,2*b + 1,b + 2*c,a + c + 1,t + 2⟩ := by
    rw [future, h1]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h3 : future 3 ⟨2,a,b,c,t⟩ = ⟨5,2*a + 2*c + 3,a + 2*b + c + 2,b + 2*c,t + 3⟩ := by
    rw [future, h2]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h4 : future 4 ⟨2,a,b,c,t⟩ = ⟨6,2*b + 4*c + 1,2*a + b + 4*c + 3,a + 2*b + c + 3,t + 3⟩ := by
    rw [future, h3]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h5 : future 5 ⟨2,a,b,c,t⟩ = ⟨7,2*a + 4*b + 2*c + 6,a + 4*b + 5*c + 4,2*a + b + 4*c + 4,t + 4⟩ := by
    rw [future, h4]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h6 : future 6 ⟨2,a,b,c,t⟩ = ⟨8,4*a + 2*b + 8*c + 9,4*a + 5*b + 6*c + 10,a + 4*b + 5*c + 5,t + 4⟩ := by
    rw [future, h5]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h7 : future 7 ⟨2,a,b,c,t⟩ = ⟨9,2*a + 8*b + 10*c + 10,5*a + 6*b + 13*c + 14,4*a + 5*b + 6*c + 10,t + 5⟩ := by
    rw [future, h6]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h8 : future 8 ⟨2,a,b,c,t⟩ = ⟨0,8*a + 10*b + 12*c + 23,6*a + 13*b + 16*c + 20,5*a + 6*b + 13*c + 15,t + 6⟩ := by
    rw [future, h7]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h9 : future 9 ⟨2,a,b,c,t⟩ = ⟨1,10*a + 12*b + 26*c + 30,13*a + 16*b + 25*c + 38,6*a + 13*b + 16*c + 20,t + 7⟩ := by
    rw [future, h8]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h10 : future 10 ⟨2,a,b,c,t⟩ = ⟨2,12*a + 26*b + 32*c + 42,16*a + 25*b + 42*c + 50,13*a + 16*b + 25*c + 39,t + 7⟩ := by
    rw [future, h9]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h11 : future 11 ⟨2,a,b,c,t⟩ = ⟨3,26*a + 32*b + 50*c + 78,25*a + 42*b + 57*c + 81,16*a + 25*b + 42*c + 50,t + 8⟩ := by
    rw [future, h10]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h12 : future 12 ⟨2,a,b,c,t⟩ = ⟨4,32*a + 50*b + 84*c + 101,42*a + 57*b + 92*c + 128,25*a + 42*b + 57*c + 82,t + 9⟩ := by
    rw [future, h11]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h13 : future 13 ⟨2,a,b,c,t⟩ = ⟨5,50*a + 84*b + 114*c + 165,57*a + 92*b + 141*c + 183,42*a + 57*b + 92*c + 128,t + 10⟩ := by
    rw [future, h12]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  simp only [RecurrenceAt, zero_add, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  norm_num [observe, front, tail, encode, block, future] <;> ring

#print axioms phase_certificate2

private theorem phase_certificate3 (a b c t : ℤ) :
    RecurrenceAt (fun k => observe (future k ⟨3,a,b,c,t⟩)) 0 := by
  have h1 : future 1 ⟨3,a,b,c,t⟩ = ⟨4,2*c + 1,a + c,b + 1,t + 1⟩ := by
    rw [future]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h2 : future 2 ⟨3,a,b,c,t⟩ = ⟨5,2*b + 3,b + 2*c + 2,a + c,t + 2⟩ := by
    rw [future, h1]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h3 : future 3 ⟨3,a,b,c,t⟩ = ⟨6,2*a + 2*c + 1,a + 2*b + c + 3,b + 2*c + 3,t + 2⟩ := by
    rw [future, h2]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h4 : future 4 ⟨3,a,b,c,t⟩ = ⟨7,2*b + 4*c + 6,2*a + b + 4*c + 4,a + 2*b + c + 4,t + 3⟩ := by
    rw [future, h3]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h5 : future 5 ⟨3,a,b,c,t⟩ = ⟨8,2*a + 4*b + 2*c + 9,a + 4*b + 5*c + 10,2*a + b + 4*c + 5,t + 3⟩ := by
    rw [future, h4]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h6 : future 6 ⟨3,a,b,c,t⟩ = ⟨9,4*a + 2*b + 8*c + 10,4*a + 5*b + 6*c + 14,a + 4*b + 5*c + 10,t + 4⟩ := by
    rw [future, h5]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h7 : future 7 ⟨3,a,b,c,t⟩ = ⟨0,2*a + 8*b + 10*c + 23,5*a + 6*b + 13*c + 20,4*a + 5*b + 6*c + 15,t + 5⟩ := by
    rw [future, h6]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h8 : future 8 ⟨3,a,b,c,t⟩ = ⟨1,8*a + 10*b + 12*c + 30,6*a + 13*b + 16*c + 38,5*a + 6*b + 13*c + 20,t + 6⟩ := by
    rw [future, h7]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h9 : future 9 ⟨3,a,b,c,t⟩ = ⟨2,10*a + 12*b + 26*c + 42,13*a + 16*b + 25*c + 50,6*a + 13*b + 16*c + 39,t + 6⟩ := by
    rw [future, h8]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h10 : future 10 ⟨3,a,b,c,t⟩ = ⟨3,12*a + 26*b + 32*c + 78,16*a + 25*b + 42*c + 81,13*a + 16*b + 25*c + 50,t + 7⟩ := by
    rw [future, h9]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h11 : future 11 ⟨3,a,b,c,t⟩ = ⟨4,26*a + 32*b + 50*c + 101,25*a + 42*b + 57*c + 128,16*a + 25*b + 42*c + 82,t + 8⟩ := by
    rw [future, h10]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h12 : future 12 ⟨3,a,b,c,t⟩ = ⟨5,32*a + 50*b + 84*c + 165,42*a + 57*b + 92*c + 183,25*a + 42*b + 57*c + 128,t + 9⟩ := by
    rw [future, h11]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h13 : future 13 ⟨3,a,b,c,t⟩ = ⟨6,50*a + 84*b + 114*c + 257,57*a + 92*b + 141*c + 293,42*a + 57*b + 92*c + 184,t + 9⟩ := by
    rw [future, h12]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  simp only [RecurrenceAt, zero_add, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  norm_num [observe, front, tail, encode, block, future] <;> ring

#print axioms phase_certificate3

private theorem phase_certificate4 (a b c t : ℤ) :
    RecurrenceAt (fun k => observe (future k ⟨4,a,b,c,t⟩)) 0 := by
  have h1 : future 1 ⟨4,a,b,c,t⟩ = ⟨5,2*c + 1,a + c,b,t + 1⟩ := by
    rw [future]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h2 : future 2 ⟨4,a,b,c,t⟩ = ⟨6,2*b + 1,b + 2*c + 1,a + c + 1,t + 1⟩ := by
    rw [future, h1]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h3 : future 3 ⟨4,a,b,c,t⟩ = ⟨7,2*a + 2*c + 2,a + 2*b + c + 2,b + 2*c + 2,t + 2⟩ := by
    rw [future, h2]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h4 : future 4 ⟨4,a,b,c,t⟩ = ⟨8,2*b + 4*c + 5,2*a + b + 4*c + 4,a + 2*b + c + 3,t + 2⟩ := by
    rw [future, h3]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h5 : future 5 ⟨4,a,b,c,t⟩ = ⟨9,2*a + 4*b + 2*c + 6,a + 4*b + 5*c + 8,2*a + b + 4*c + 4,t + 3⟩ := by
    rw [future, h4]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h6 : future 6 ⟨4,a,b,c,t⟩ = ⟨0,4*a + 2*b + 8*c + 11,4*a + 5*b + 6*c + 10,a + 4*b + 5*c + 9,t + 4⟩ := by
    rw [future, h5]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h7 : future 7 ⟨4,a,b,c,t⟩ = ⟨1,2*a + 8*b + 10*c + 18,5*a + 6*b + 13*c + 20,4*a + 5*b + 6*c + 10,t + 5⟩ := by
    rw [future, h6]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h8 : future 8 ⟨4,a,b,c,t⟩ = ⟨2,8*a + 10*b + 12*c + 22,6*a + 13*b + 16*c + 28,5*a + 6*b + 13*c + 21,t + 5⟩ := by
    rw [future, h7]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h9 : future 9 ⟨4,a,b,c,t⟩ = ⟨3,10*a + 12*b + 26*c + 42,13*a + 16*b + 25*c + 43,6*a + 13*b + 16*c + 28,t + 6⟩ := by
    rw [future, h8]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h10 : future 10 ⟨4,a,b,c,t⟩ = ⟨4,12*a + 26*b + 32*c + 57,16*a + 25*b + 42*c + 70,13*a + 16*b + 25*c + 44,t + 7⟩ := by
    rw [future, h9]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h11 : future 11 ⟨4,a,b,c,t⟩ = ⟨5,26*a + 32*b + 50*c + 89,25*a + 42*b + 57*c + 101,16*a + 25*b + 42*c + 70,t + 8⟩ := by
    rw [future, h10]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h12 : future 12 ⟨4,a,b,c,t⟩ = ⟨6,32*a + 50*b + 84*c + 141,42*a + 57*b + 92*c + 159,25*a + 42*b + 57*c + 102,t + 8⟩ := by
    rw [future, h11]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h13 : future 13 ⟨4,a,b,c,t⟩ = ⟨7,50*a + 84*b + 114*c + 204,57*a + 92*b + 141*c + 243,42*a + 57*b + 92*c + 160,t + 9⟩ := by
    rw [future, h12]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  simp only [RecurrenceAt, zero_add, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  norm_num [observe, front, tail, encode, block, future] <;> ring

#print axioms phase_certificate4

private theorem phase_certificate5 (a b c t : ℤ) :
    RecurrenceAt (fun k => observe (future k ⟨5,a,b,c,t⟩)) 0 := by
  have h1 : future 1 ⟨5,a,b,c,t⟩ = ⟨6,2*c + 1,a + c,b + 1,t⟩ := by
    rw [future]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h2 : future 2 ⟨5,a,b,c,t⟩ = ⟨7,2*b + 2,b + 2*c + 2,a + c + 1,t + 1⟩ := by
    rw [future, h1]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h3 : future 3 ⟨5,a,b,c,t⟩ = ⟨8,2*a + 2*c + 3,a + 2*b + c + 3,b + 2*c + 3,t + 1⟩ := by
    rw [future, h2]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h4 : future 4 ⟨5,a,b,c,t⟩ = ⟨9,2*b + 4*c + 6,2*a + b + 4*c + 6,a + 2*b + c + 3,t + 2⟩ := by
    rw [future, h3]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h5 : future 5 ⟨5,a,b,c,t⟩ = ⟨0,2*a + 4*b + 2*c + 9,a + 4*b + 5*c + 9,2*a + b + 4*c + 7,t + 3⟩ := by
    rw [future, h4]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h6 : future 6 ⟨5,a,b,c,t⟩ = ⟨1,4*a + 2*b + 8*c + 14,4*a + 5*b + 6*c + 16,a + 4*b + 5*c + 9,t + 4⟩ := by
    rw [future, h5]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h7 : future 7 ⟨5,a,b,c,t⟩ = ⟨2,2*a + 8*b + 10*c + 20,5*a + 6*b + 13*c + 23,4*a + 5*b + 6*c + 17,t + 4⟩ := by
    rw [future, h6]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h8 : future 8 ⟨5,a,b,c,t⟩ = ⟨3,8*a + 10*b + 12*c + 34,6*a + 13*b + 16*c + 37,5*a + 6*b + 13*c + 23,t + 5⟩ := by
    rw [future, h7]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h9 : future 9 ⟨5,a,b,c,t⟩ = ⟨4,10*a + 12*b + 26*c + 47,13*a + 16*b + 25*c + 57,6*a + 13*b + 16*c + 38,t + 6⟩ := by
    rw [future, h8]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h10 : future 10 ⟨5,a,b,c,t⟩ = ⟨5,12*a + 26*b + 32*c + 77,16*a + 25*b + 42*c + 85,13*a + 16*b + 25*c + 57,t + 7⟩ := by
    rw [future, h9]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h11 : future 11 ⟨5,a,b,c,t⟩ = ⟨6,26*a + 32*b + 50*c + 115,25*a + 42*b + 57*c + 134,16*a + 25*b + 42*c + 86,t + 7⟩ := by
    rw [future, h10]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h12 : future 12 ⟨5,a,b,c,t⟩ = ⟨7,32*a + 50*b + 84*c + 172,42*a + 57*b + 92*c + 201,25*a + 42*b + 57*c + 135,t + 8⟩ := by
    rw [future, h11]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h13 : future 13 ⟨5,a,b,c,t⟩ = ⟨8,50*a + 84*b + 114*c + 271,57*a + 92*b + 141*c + 307,42*a + 57*b + 92*c + 202,t + 8⟩ := by
    rw [future, h12]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  simp only [RecurrenceAt, zero_add, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  norm_num [observe, front, tail, encode, block, future] <;> ring

#print axioms phase_certificate5

private theorem phase_certificate6 (a b c t : ℤ) :
    RecurrenceAt (fun k => observe (future k ⟨6,a,b,c,t⟩)) 0 := by
  have h1 : future 1 ⟨6,a,b,c,t⟩ = ⟨7,2*c,a + c,b + 1,t + 1⟩ := by
    rw [future]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h2 : future 2 ⟨6,a,b,c,t⟩ = ⟨8,2*b + 3,b + 2*c + 1,a + c + 1,t + 1⟩ := by
    rw [future, h1]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h3 : future 3 ⟨6,a,b,c,t⟩ = ⟨9,2*a + 2*c + 2,a + 2*b + c + 4,b + 2*c + 1,t + 2⟩ := by
    rw [future, h2]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h4 : future 4 ⟨6,a,b,c,t⟩ = ⟨0,2*b + 4*c + 5,2*a + b + 4*c + 3,a + 2*b + c + 5,t + 3⟩ := by
    rw [future, h3]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h5 : future 5 ⟨6,a,b,c,t⟩ = ⟨1,2*a + 4*b + 2*c + 10,a + 4*b + 5*c + 10,2*a + b + 4*c + 3,t + 4⟩ := by
    rw [future, h4]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h6 : future 6 ⟨6,a,b,c,t⟩ = ⟨2,4*a + 2*b + 8*c + 8,4*a + 5*b + 6*c + 13,a + 4*b + 5*c + 11,t + 4⟩ := by
    rw [future, h5]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h7 : future 7 ⟨6,a,b,c,t⟩ = ⟨3,2*a + 8*b + 10*c + 22,5*a + 6*b + 13*c + 19,4*a + 5*b + 6*c + 13,t + 5⟩ := by
    rw [future, h6]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h8 : future 8 ⟨6,a,b,c,t⟩ = ⟨4,8*a + 10*b + 12*c + 27,6*a + 13*b + 16*c + 35,5*a + 6*b + 13*c + 20,t + 6⟩ := by
    rw [future, h7]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h9 : future 9 ⟨6,a,b,c,t⟩ = ⟨5,10*a + 12*b + 26*c + 41,13*a + 16*b + 25*c + 47,6*a + 13*b + 16*c + 35,t + 7⟩ := by
    rw [future, h8]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h10 : future 10 ⟨6,a,b,c,t⟩ = ⟨6,12*a + 26*b + 32*c + 71,16*a + 25*b + 42*c + 76,13*a + 16*b + 25*c + 48,t + 7⟩ := by
    rw [future, h9]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h11 : future 11 ⟨6,a,b,c,t⟩ = ⟨7,26*a + 32*b + 50*c + 96,25*a + 42*b + 57*c + 119,16*a + 25*b + 42*c + 77,t + 8⟩ := by
    rw [future, h10]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h12 : future 12 ⟨6,a,b,c,t⟩ = ⟨8,32*a + 50*b + 84*c + 155,42*a + 57*b + 92*c + 173,25*a + 42*b + 57*c + 120,t + 8⟩ := by
    rw [future, h11]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h13 : future 13 ⟨6,a,b,c,t⟩ = ⟨9,50*a + 84*b + 114*c + 240,57*a + 92*b + 141*c + 275,42*a + 57*b + 92*c + 173,t + 9⟩ := by
    rw [future, h12]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  simp only [RecurrenceAt, zero_add, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  norm_num [observe, front, tail, encode, block, future] <;> ring

#print axioms phase_certificate6

private theorem phase_certificate7 (a b c t : ℤ) :
    RecurrenceAt (fun k => observe (future k ⟨7,a,b,c,t⟩)) 0 := by
  have h1 : future 1 ⟨7,a,b,c,t⟩ = ⟨8,2*c + 1,a + c,b + 1,t⟩ := by
    rw [future]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h2 : future 2 ⟨7,a,b,c,t⟩ = ⟨9,2*b + 2,b + 2*c + 2,a + c,t + 1⟩ := by
    rw [future, h1]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h3 : future 3 ⟨7,a,b,c,t⟩ = ⟨0,2*a + 2*c + 3,a + 2*b + c + 2,b + 2*c + 3,t + 2⟩ := by
    rw [future, h2]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h4 : future 4 ⟨7,a,b,c,t⟩ = ⟨1,2*b + 4*c + 6,2*a + b + 4*c + 6,a + 2*b + c + 2,t + 3⟩ := by
    rw [future, h3]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h5 : future 5 ⟨7,a,b,c,t⟩ = ⟨2,2*a + 4*b + 2*c + 6,a + 4*b + 5*c + 8,2*a + b + 4*c + 7,t + 3⟩ := by
    rw [future, h4]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h6 : future 6 ⟨7,a,b,c,t⟩ = ⟨3,4*a + 2*b + 8*c + 14,4*a + 5*b + 6*c + 13,a + 4*b + 5*c + 8,t + 4⟩ := by
    rw [future, h5]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h7 : future 7 ⟨7,a,b,c,t⟩ = ⟨4,2*a + 8*b + 10*c + 17,5*a + 6*b + 13*c + 22,4*a + 5*b + 6*c + 14,t + 5⟩ := by
    rw [future, h6]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h8 : future 8 ⟨7,a,b,c,t⟩ = ⟨5,8*a + 10*b + 12*c + 29,6*a + 13*b + 16*c + 31,5*a + 6*b + 13*c + 22,t + 6⟩ := by
    rw [future, h7]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h9 : future 9 ⟨7,a,b,c,t⟩ = ⟨6,10*a + 12*b + 26*c + 45,13*a + 16*b + 25*c + 51,6*a + 13*b + 16*c + 32,t + 6⟩ := by
    rw [future, h8]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h10 : future 10 ⟨7,a,b,c,t⟩ = ⟨7,12*a + 26*b + 32*c + 64,16*a + 25*b + 42*c + 77,13*a + 16*b + 25*c + 52,t + 7⟩ := by
    rw [future, h9]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h11 : future 11 ⟨7,a,b,c,t⟩ = ⟨8,26*a + 32*b + 50*c + 105,25*a + 42*b + 57*c + 116,16*a + 25*b + 42*c + 78,t + 7⟩ := by
    rw [future, h10]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h12 : future 12 ⟨7,a,b,c,t⟩ = ⟨9,32*a + 50*b + 84*c + 156,42*a + 57*b + 92*c + 183,25*a + 42*b + 57*c + 116,t + 8⟩ := by
    rw [future, h11]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h13 : future 13 ⟨7,a,b,c,t⟩ = ⟨0,50*a + 84*b + 114*c + 235,57*a + 92*b + 141*c + 272,42*a + 57*b + 92*c + 184,t + 9⟩ := by
    rw [future, h12]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  simp only [RecurrenceAt, zero_add, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  norm_num [observe, front, tail, encode, block, future] <;> ring

#print axioms phase_certificate7

private theorem phase_certificate8 (a b c t : ℤ) :
    RecurrenceAt (fun k => observe (future k ⟨8,a,b,c,t⟩)) 0 := by
  have h1 : future 1 ⟨8,a,b,c,t⟩ = ⟨9,2*c,a + c,b,t + 1⟩ := by
    rw [future]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h2 : future 2 ⟨8,a,b,c,t⟩ = ⟨0,2*b + 3,b + 2*c,a + c + 1,t + 2⟩ := by
    rw [future, h1]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h3 : future 3 ⟨8,a,b,c,t⟩ = ⟨1,2*a + 2*c + 2,a + 2*b + c + 4,b + 2*c,t + 3⟩ := by
    rw [future, h2]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h4 : future 4 ⟨8,a,b,c,t⟩ = ⟨2,2*b + 4*c + 2,2*a + b + 4*c + 2,a + 2*b + c + 5,t + 3⟩ := by
    rw [future, h3]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h5 : future 5 ⟨8,a,b,c,t⟩ = ⟨3,2*a + 4*b + 2*c + 10,a + 4*b + 5*c + 7,2*a + b + 4*c + 2,t + 4⟩ := by
    rw [future, h4]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h6 : future 6 ⟨8,a,b,c,t⟩ = ⟨4,4*a + 2*b + 8*c + 5,4*a + 5*b + 6*c + 12,a + 4*b + 5*c + 8,t + 5⟩ := by
    rw [future, h5]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h7 : future 7 ⟨8,a,b,c,t⟩ = ⟨5,2*a + 8*b + 10*c + 17,5*a + 6*b + 13*c + 13,4*a + 5*b + 6*c + 12,t + 6⟩ := by
    rw [future, h6]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h8 : future 8 ⟨8,a,b,c,t⟩ = ⟨6,8*a + 10*b + 12*c + 25,6*a + 13*b + 16*c + 29,5*a + 6*b + 13*c + 14,t + 6⟩ := by
    rw [future, h7]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h9 : future 9 ⟨8,a,b,c,t⟩ = ⟨7,10*a + 12*b + 26*c + 28,13*a + 16*b + 25*c + 39,6*a + 13*b + 16*c + 30,t + 7⟩ := by
    rw [future, h8]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h10 : future 10 ⟨8,a,b,c,t⟩ = ⟨8,12*a + 26*b + 32*c + 61,16*a + 25*b + 42*c + 58,13*a + 16*b + 25*c + 40,t + 7⟩ := by
    rw [future, h9]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h11 : future 11 ⟨8,a,b,c,t⟩ = ⟨9,26*a + 32*b + 50*c + 80,25*a + 42*b + 57*c + 101,16*a + 25*b + 42*c + 58,t + 8⟩ := by
    rw [future, h10]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h12 : future 12 ⟨8,a,b,c,t⟩ = ⟨0,32*a + 50*b + 84*c + 119,42*a + 57*b + 92*c + 138,25*a + 42*b + 57*c + 102,t + 9⟩ := by
    rw [future, h11]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h13 : future 13 ⟨8,a,b,c,t⟩ = ⟨1,50*a + 84*b + 114*c + 204,57*a + 92*b + 141*c + 221,42*a + 57*b + 92*c + 138,t + 10⟩ := by
    rw [future, h12]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  simp only [RecurrenceAt, zero_add, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  norm_num [observe, front, tail, encode, block, future] <;> ring

#print axioms phase_certificate8

private theorem phase_certificate9 (a b c t : ℤ) :
    RecurrenceAt (fun k => observe (future k ⟨9,a,b,c,t⟩)) 0 := by
  have h1 : future 1 ⟨9,a,b,c,t⟩ = ⟨0,2*c + 3,a + c,b + 1,t + 1⟩ := by
    rw [future]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h2 : future 2 ⟨9,a,b,c,t⟩ = ⟨1,2*b + 2,b + 2*c + 4,a + c,t + 2⟩ := by
    rw [future, h1]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h3 : future 3 ⟨9,a,b,c,t⟩ = ⟨2,2*a + 2*c + 2,a + 2*b + c + 2,b + 2*c + 5,t + 2⟩ := by
    rw [future, h2]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h4 : future 4 ⟨9,a,b,c,t⟩ = ⟨3,2*b + 4*c + 10,2*a + b + 4*c + 7,a + 2*b + c + 2,t + 3⟩ := by
    rw [future, h3]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h5 : future 5 ⟨9,a,b,c,t⟩ = ⟨4,2*a + 4*b + 2*c + 5,a + 4*b + 5*c + 12,2*a + b + 4*c + 8,t + 4⟩ := by
    rw [future, h4]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h6 : future 6 ⟨9,a,b,c,t⟩ = ⟨5,4*a + 2*b + 8*c + 17,4*a + 5*b + 6*c + 13,a + 4*b + 5*c + 12,t + 5⟩ := by
    rw [future, h5]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h7 : future 7 ⟨9,a,b,c,t⟩ = ⟨6,2*a + 8*b + 10*c + 25,5*a + 6*b + 13*c + 29,4*a + 5*b + 6*c + 14,t + 5⟩ := by
    rw [future, h6]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h8 : future 8 ⟨9,a,b,c,t⟩ = ⟨7,8*a + 10*b + 12*c + 28,6*a + 13*b + 16*c + 39,5*a + 6*b + 13*c + 30,t + 6⟩ := by
    rw [future, h7]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h9 : future 9 ⟨9,a,b,c,t⟩ = ⟨8,10*a + 12*b + 26*c + 61,13*a + 16*b + 25*c + 58,6*a + 13*b + 16*c + 40,t + 6⟩ := by
    rw [future, h8]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h10 : future 10 ⟨9,a,b,c,t⟩ = ⟨9,12*a + 26*b + 32*c + 80,16*a + 25*b + 42*c + 101,13*a + 16*b + 25*c + 58,t + 7⟩ := by
    rw [future, h9]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h11 : future 11 ⟨9,a,b,c,t⟩ = ⟨0,26*a + 32*b + 50*c + 119,25*a + 42*b + 57*c + 138,16*a + 25*b + 42*c + 102,t + 8⟩ := by
    rw [future, h10]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h12 : future 12 ⟨9,a,b,c,t⟩ = ⟨1,32*a + 50*b + 84*c + 204,42*a + 57*b + 92*c + 221,25*a + 42*b + 57*c + 138,t + 9⟩ := by
    rw [future, h11]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  have h13 : future 13 ⟨9,a,b,c,t⟩ = ⟨2,50*a + 84*b + 114*c + 278,57*a + 92*b + 141*c + 342,42*a + 57*b + 92*c + 222,t + 9⟩ := by
    rw [future, h12]
    norm_num [future, advance, next, count, left, extra, gain, Fin.ext_iff] <;> ring_nf <;> (try simp) <;> decide
  simp only [RecurrenceAt, zero_add, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  norm_num [observe, front, tail, encode, block, future] <;> ring

#print axioms phase_certificate9

/-- A universal identity in the four integer coordinates, for every phase. -/
theorem recurrence_certificate (s : State) :
    RecurrenceAt (fun k => observe (future k s)) 0 := by
  rcases s with ⟨p,a,b,c,t⟩
  fin_cases p
  · simpa using phase_certificate0 a b c t
  · simpa using phase_certificate1 a b c t
  · simpa using phase_certificate2 a b c t
  · simpa using phase_certificate3 a b c t
  · simpa using phase_certificate4 a b c t
  · simpa using phase_certificate5 a b c t
  · simpa using phase_certificate6 a b c t
  · simpa using phase_certificate7 a b c t
  · simpa using phase_certificate8 a b c t
  · simpa using phase_certificate9 a b c t

theorem tail_recurrence (n : ℕ) : RecurrenceAt lengthValue (n+9) := by
  have h (k : ℕ) : lengthValue (n+9+k) = observe (future k (future n seed)) := by
    rw [show n+9+k = (n+k)+9 by omega, literal_numeric_bridge, future_add]
  have h0 : lengthValue (n+9) = observe (future n seed) := literal_numeric_bridge n
  have hz (s : State) : future 0 s = s := rfl
  simpa only [RecurrenceAt, zero_add, h, h0, hz] using recurrence_certificate (future n seed)

def fastLength (n : ℕ) : ℤ :=
  if 9 ≤ n then observe (future (n-9) seed) else ((word n).length : ℤ)

lemma length_fast (n : ℕ) : lengthValue n = fastLength n := by
  unfold fastLength
  split_ifs with h
  · simpa [show n-9+9=n by omega] using literal_numeric_bridge (n-9)
  · rfl

lemma value_0 : lengthValue 0 = 2 := by
  norm_num [lengthValue, word, rewrite]
lemma value_1 : lengthValue 1 = 4 := by
  norm_num [lengthValue, word, rewrite]
lemma value_2 : lengthValue 2 = 5 := by
  norm_num [lengthValue, word, rewrite]
lemma value_3 : lengthValue 3 = 7 := by
  norm_num [lengthValue, word, rewrite]
lemma value_4 : lengthValue 4 = 9 := by
  norm_num [lengthValue, word, rewrite]
lemma value_5 : lengthValue 5 = 12 := by
  norm_num [lengthValue, word, rewrite]
lemma value_6 : lengthValue 6 = 17 := by
  norm_num [lengthValue, word, rewrite]
lemma value_7 : lengthValue 7 = 23 := by
  norm_num [lengthValue, word, rewrite]
lemma value_8 : lengthValue 8 = 33 := by
  norm_num [lengthValue, word, rewrite]
lemma value_9 : lengthValue 9 = 48 := by
  rw [length_fast]
  decide
lemma value_10 : lengthValue 10 = 70 := by
  rw [length_fast]
  decide
lemma value_11 : lengthValue 11 = 103 := by
  rw [length_fast]
  decide
lemma value_12 : lengthValue 12 = 152 := by
  rw [length_fast]
  decide
lemma value_13 : lengthValue 13 = 228 := by
  rw [length_fast]
  decide
lemma value_14 : lengthValue 14 = 343 := by
  rw [length_fast]
  decide
lemma value_15 : lengthValue 15 = 515 := by
  rw [length_fast]
  decide
lemma value_16 : lengthValue 16 = 779 := by
  rw [length_fast]
  decide
lemma value_17 : lengthValue 17 = 1180 := by
  rw [length_fast]
  decide
lemma value_18 : lengthValue 18 = 1787 := by
  rw [length_fast]
  decide
lemma value_19 : lengthValue 19 = 2715 := by
  rw [length_fast]
  decide
lemma value_20 : lengthValue 20 = 4124 := by
  rw [length_fast]
  decide
lemma value_21 : lengthValue 21 = 6264 := by
  rw [length_fast]
  decide

/-- The recurrence begins exactly at the source's specified cutoff n=16. -/
theorem literal_recurrence (n : ℕ) : RecurrenceAt lengthValue (n+3) := by
  by_cases h : 6 ≤ n
  · simpa [show n-6+9=n+3 by omega] using tail_recurrence (n-6)
  · interval_cases n <;> norm_num [RecurrenceAt, value_0, value_1, value_2, value_3, value_4, value_5, value_6, value_7, value_8, value_9, value_10, value_11, value_12, value_13, value_14, value_15, value_16, value_17, value_18, value_19, value_20, value_21]

/-- The recurrence sequence, independently defined by the OEIS initial values. -/
def source : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | 3 => 7
  | 4 => 9
  | 5 => 12
  | 6 => 17
  | 7 => 23
  | 8 => 33
  | 9 => 48
  | 10 => 70
  | 11 => 103
  | 12 => 152
  | 13 => 228
  | 14 => 343
  | 15 => 515
  | n+16 => 2*source (n+15) - source (n+14) + 2*source (n+13) -
      4*source (n+12) + 4*source (n+11) - 4*source (n+10) +
      4*source (n+9) - 4*source (n+8) + 4*source (n+7) -
      3*source (n+6) + 2*source (n+5) - 3*source (n+4) + 2*source (n+3)

theorem source_recurrence (n : ℕ) : RecurrenceAt source (n+3) := by
  unfold RecurrenceAt
  rw [show n+3+13 = n+16 by omega, source]

theorem initial_agreement (n : ℕ) (h : n < 16) : lengthValue n = source n := by
  interval_cases n <;> norm_num [source, value_0, value_1, value_2, value_3, value_4, value_5, value_6, value_7, value_8, value_9, value_10, value_11, value_12, value_13, value_14, value_15]

/-- Kimberling's complete A288511 length conjecture, including n=0. -/
theorem all_lengths (n : ℕ) : ((word n).length : ℤ) = source n := by
  change lengthValue n = source n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 16
    · exact initial_agreement n hn
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 16 ≤ n by omega)
      have hl := literal_recurrence k
      have hs := source_recurrence k
      simp only [RecurrenceAt] at hl hs
      have h (j : ℕ) (hj : j < 16) : lengthValue (k+j) = source (k+j) :=
        ih (k+j) (by omega)
      simp only [show k+3+13=k+16 by omega, show k+3+12=k+15 by omega,
        show k+3+11=k+14 by omega, show k+3+10=k+13 by omega,
        show k+3+9=k+12 by omega, show k+3+8=k+11 by omega,
        show k+3+7=k+10 by omega, show k+3+6=k+9 by omega,
        show k+3+5=k+8 by omega, show k+3+4=k+7 by omega,
        show k+3+3=k+6 by omega, show k+3+2=k+5 by omega,
        show k+3+1=k+4 by omega] at hl hs
      rw [h 15 (by decide), h 14 (by decide), h 13 (by decide), h 12 (by decide),
        h 11 (by decide), h 10 (by decide), h 9 (by decide), h 8 (by decide),
        h 7 (by decide), h 6 (by decide), h 5 (by decide), h 4 (by decide),
        h 3 (by decide)] at hl
      simpa [Nat.add_comm] using hl.trans hs.symm

end Kimberling288511
