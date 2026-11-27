import Std

/- Finite part of the ring-period proof, using the local Wolfram rule at
   each site. The five closed equalities below reduce in the Lean kernel. -/
namespace SmallRings

def step (rule width word : Nat) : Nat :=
  (List.range width).foldl (fun output i =>
    let left := (word.testBit ((i + width - 1) % width)).toNat
    let center := (word.testBit i).toNat
    let right := (word.testBit ((i + 1) % width)).toNat
    let code := 4 * left + 2 * center + right
    if rule.testBit code then output + 2 ^ i else output) 0

/-- True iff the first visit to base from next occurs on the last
    of the allowed steps. The caller sets next to the first successor. -/
def firstReturn (advance : Nat → Nat) (base next : Nat) : Nat → Bool
  | 0 => false
  | remaining + 1 =>
    if next == base then remaining == 0
    else firstReturn advance base (advance next) remaining

def hasPeriod (rule width period : Nat) : Bool :=
  let advance := step rule width
  let base := (List.range 16).foldl (fun word _ => advance word) 1
  firstReturn advance base (advance base) period

def checkWidths (rule : Nat) (periods : List Nat) : Bool :=
  periods.zipIdx.all (fun (period, i) => hasPeriod rule (i + 1) period)

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

theorem rule9 : checkWidths 9
    [2,2,2,2,2,9,5,12,18,5,22,12,26,14,30,16] = true := by decide +kernel

theorem rule25 : checkWidths 25
    [2,2,3,2,15,15,21,16,9,20,22,24,26,28,30,32] = true := by decide +kernel

theorem rule41 : checkWidths 41
    [2,2,2,2,15,2,28,8,36,20,44,12,52,28,60,16] = true := by decide +kernel

theorem rule107 : checkWidths 107
    [2,2,3,2,15,2,28,2,36,20,11,12,117,28,60,8] = true := by decide +kernel

theorem rule190 : checkWidths 190
    [1,1,1,4,5,6,7,4,9,10,11,4,13,14,15,4] = true := by decide +kernel

end SmallRings
