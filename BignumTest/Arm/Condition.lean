/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/

import Bignum.Arm

open Bignum.Arm

-- example : Condition.EQ.toBitVec = 0b0000 := by rfl
-- example : Condition.NE.toBitVec = 0b0001 := by rfl
-- example : Condition.CS.toBitVec = 0b0010 := by rfl
-- example : Condition.HS.toBitVec = 0b0010 := by rfl
-- example : Condition.CC.toBitVec = 0b0011 := by rfl
-- example : Condition.LO.toBitVec = 0b0011 := by rfl
-- example : Condition.MI.toBitVec = 0b0100 := by rfl
-- example : Condition.PL.toBitVec = 0b0101 := by rfl
-- example : Condition.VS.toBitVec = 0b0110 := by rfl
-- example : Condition.VC.toBitVec = 0b0111 := by rfl
-- example : Condition.HI.toBitVec = 0b1000 := by rfl
-- example : Condition.LS.toBitVec = 0b1001 := by rfl
-- example : Condition.GE.toBitVec = 0b1010 := by rfl
-- example : Condition.LT.toBitVec = 0b1011 := by rfl
-- example : Condition.GT.toBitVec = 0b1100 := by rfl
-- example : Condition.LE.toBitVec = 0b1101 := by rfl
-- example : Condition.AL.toBitVec = 0b1110 := by rfl
-- example : Condition.NV.toBitVec = 0b1111 := by rfl
