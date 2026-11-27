import Std

/- A word is a polynomial modulo x^37-1, packed into a 37-bit mask.
   At set bit j of the exponent, multiplication by (1+x)^(2^j)
   means XOR with the rotation by 2^j. Starting at 3 represents 1+x.
   All certificate exponents fit in 17 bits. The residue equalities
   below are definitional equalities, checked by the Lean kernel. -/
namespace A355255

def rotateWord (word : BitVec 37) (shift : Nat) : BitVec 37 :=
  let s := shift % 37
  (word <<< s) ||| (word >>> (37 - s))

def afterSteps (steps : Nat) (_ : steps < 2 ^ 17 := by decide) : BitVec 37 :=
  (List.range 17).foldl
    (fun word j =>
      if steps.testBit j then word ^^^ rotateWord word (2 ^ j) else word)
    (3 : BitVec 37)

theorem fullPeriod : afterSteps 87381 = rotateWord 3 12 := rfl
theorem fullMask : afterSteps 87381 = 0x3000 := rfl
theorem withoutThree : afterSteps (87381 / 3) = 0xe26323afd := rfl
theorem withoutSeven : afterSteps (87381 / 7) = 0x1b4a5b07e0 := rfl
theorem withoutNineteen : afterSteps (87381 / 19) = 0x1434b0a0a0 := rfl
theorem withoutSeventyThree : afterSteps (87381 / 73) = 0x1a50a5f80f := rfl

def isReturn (word : BitVec 37) : Bool :=
  (List.range 37).any (fun shift => word == rotateWord 3 shift)

theorem excludedReturns :
    isReturn (afterSteps (87381 / 3)) = false ∧
    isReturn (afterSteps (87381 / 7)) = false ∧
    isReturn (afterSteps (87381 / 19)) = false ∧
    isReturn (afterSteps (87381 / 73)) = false := by decide +kernel

end A355255
