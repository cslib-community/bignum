import Bignum.ArmRev

open Bignum.ArmRev

example : Condition.EQ.value = 0b0000 := by rfl
example : Condition.NE.value = 0b0001 := by rfl
example : Condition.CS.value = 0b0010 := by rfl
example : Condition.HS.value = 0b0010 := by rfl
example : Condition.CC.value = 0b0011 := by rfl
example : Condition.LO.value = 0b0011 := by rfl
example : Condition.MI.value = 0b0100 := by rfl
example : Condition.PL.value = 0b0101 := by rfl
example : Condition.VS.value = 0b0110 := by rfl
example : Condition.VC.value = 0b0111 := by rfl
example : Condition.HI.value = 0b1000 := by rfl
example : Condition.LS.value = 0b1001 := by rfl
example : Condition.GE.value = 0b1010 := by rfl
example : Condition.LT.value = 0b1011 := by rfl
example : Condition.GT.value = 0b1100 := by rfl
example : Condition.LE.value = 0b1101 := by rfl
example : Condition.AL.value = 0b1110 := by rfl
example : Condition.NV.value = 0b1111 := by rfl
