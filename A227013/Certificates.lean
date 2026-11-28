import Bounds

namespace QuarticHarmonic

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def dVal (n : ℚ) : ℚ := n^4-(n-1)^4
def cVal (n : ℚ) : ℚ := (n^2-n+1)^2
def rVal (n : ℚ) : ℚ := (dVal n-1)/2
def qVal (n : ℚ) : ℚ := n*(n-1)*(3*n^2-3*n+2)/3

def lowerVal (n : ℚ) : ℚ :=
  1/cVal n + ((dVal n)^2-1)/(12*(cVal n)^3) +
  (((dVal n)^2-1)*(3*(dVal n)^2-7))/(240*(cVal n)^5) +
  (((dVal n)^2-1)*(3*(dVal n)^4-18*(dVal n)^2+31))/(1344*(cVal n)^7)

def upperVal (n : ℚ) : ℚ :=
  1/cVal n + ((dVal n)^2-1)/(12*(cVal n)^3) +
  (((dVal n)^2-1)*(3*(dVal n)^2-7))/(240*(cVal n)^3*((cVal n)^2-(rVal n)^2))

def lowerNumerator (t : ℚ) : ℚ :=
  28*t^24 + 3024*t^23 + 156572*t^22 + 5172156*t^21 + 122369371*t^20 + 2206424754*t^19 + 31496055869*t^18 + 364973853078*t^17 + 3492525189361*t^16 + 27925808790492*t^15 + 188059104987530*t^14 + 1071825627742992*t^13 + 5182093657336537*t^12 + 21253816999367298*t^11 + 73776484843852949*t^10 + 215711119121472558*t^9 + 527200074613081231*t^8 + 1064965904311292064*t^7 + 1749657582705865988*t^6 + 2284392530671416108*t^5 + 2290486550158893280*t^4 + 1671930872839271052*t^3 + 810572143783759280*t^2 + 216472755572592948*t + 18186223121964135

theorem lower_identity (t : ℚ) (ht : 0 ≤ t) :
    (qVal (t+5)+2/3)*lowerVal (t+5)-1 = lowerNumerator t / (315*(t^2+9*t+21)^14) := by
  have hs : 0 < t^2+9*t+21 := by positivity
  have hsp : (t+5)^2-(t+5)+1 = t^2+9*t+21 := by ring
  have hct : (cVal (t+5))^2-(rVal (t+5))^2 = (t+5)^4*((t+4)^4+1) := by
    unfold cVal rVal dVal; ring
  have hct0 : (cVal (t+5))^2-(rVal (t+5))^2 ≠ 0 := by rw [hct]; positivity
  unfold lowerVal qVal
  skip
  unfold cVal dVal lowerNumerator
  rw [hsp]
  field_simp
  <;> ring

theorem lower_strict (t : ℚ) (ht : 0 ≤ t) :
    0 < (qVal (t+5)+2/3)*lowerVal (t+5)-1 := by
  rw [lower_identity t ht]
  unfold lowerNumerator
  positivity

def upperNumerator (t : ℚ) : ℚ :=
  26*t^14 + 1612*t^13 + 46362*t^12 + 819836*t^11 + 9958385*t^10 + 87898188*t^9 + 581403224*t^8 + 2927810658*t^7 + 11280438711*t^6 + 33094892742*t^5 + 72791311130*t^4 + 116416933660*t^3 + 128020606587*t^2 + 86680806370*t + 27278343429

theorem upper_identity (t : ℚ) (ht : 0 ≤ t) :
    1-qVal (t+5)*upperVal (t+5) = upperNumerator t / (45*(t+5)^2*(t^2+9*t+21)^6*((t+4)^4+1)) := by
  have hs : 0 < t^2+9*t+21 := by positivity
  have hsp : (t+5)^2-(t+5)+1 = t^2+9*t+21 := by ring
  have hct : (cVal (t+5))^2-(rVal (t+5))^2 = (t+5)^4*((t+4)^4+1) := by
    unfold cVal rVal dVal; ring
  have hct0 : (cVal (t+5))^2-(rVal (t+5))^2 ≠ 0 := by rw [hct]; positivity
  unfold upperVal qVal
  rw [hct]
  unfold cVal dVal upperNumerator
  rw [hsp]
  field_simp
  <;> ring

theorem upper_strict (t : ℚ) (ht : 0 ≤ t) :
    0 < 1-qVal (t+5)*upperVal (t+5) := by
  rw [upper_identity t ht]
  unfold upperNumerator
  positivity

end QuarticHarmonic
