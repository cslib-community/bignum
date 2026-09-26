/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/

import Bignum.Arm
open Bignum.Arm.State

example : Condition.HS = .CS := by rfl
example : Condition.LO = .CC := by rfl

example : Condition.EQ.toBitVec = 0b0000 := by rfl
example : Condition.NE.toBitVec = 0b0001 := by rfl
example : Condition.CS.toBitVec = 0b0010 := by rfl
example : Condition.HS.toBitVec = 0b0010 := by rfl
example : Condition.CC.toBitVec = 0b0011 := by rfl
example : Condition.LO.toBitVec = 0b0011 := by rfl
example : Condition.MI.toBitVec = 0b0100 := by rfl
example : Condition.PL.toBitVec = 0b0101 := by rfl
example : Condition.VS.toBitVec = 0b0110 := by rfl
example : Condition.VC.toBitVec = 0b0111 := by rfl
example : Condition.HI.toBitVec = 0b1000 := by rfl
example : Condition.LS.toBitVec = 0b1001 := by rfl
example : Condition.GE.toBitVec = 0b1010 := by rfl
example : Condition.LT.toBitVec = 0b1011 := by rfl
example : Condition.GT.toBitVec = 0b1100 := by rfl
example : Condition.LE.toBitVec = 0b1101 := by rfl
example : Condition.AL.toBitVec = 0b1110 := by rfl
example : Condition.NV.toBitVec = 0b1111 := by rfl

example : Condition.EQ = .ofBitVec 0b0000 := by rfl
example : Condition.NE = .ofBitVec 0b0001 := by rfl
example : Condition.CS = .ofBitVec 0b0010 := by rfl
example : Condition.HS = .ofBitVec 0b0010 := by rfl
example : Condition.CC = .ofBitVec 0b0011 := by rfl
example : Condition.LO = .ofBitVec 0b0011 := by rfl
example : Condition.MI = .ofBitVec 0b0100 := by rfl
example : Condition.PL = .ofBitVec 0b0101 := by rfl
example : Condition.VS = .ofBitVec 0b0110 := by rfl
example : Condition.VC = .ofBitVec 0b0111 := by rfl
example : Condition.HI = .ofBitVec 0b1000 := by rfl
example : Condition.LS = .ofBitVec 0b1001 := by rfl
example : Condition.GE = .ofBitVec 0b1010 := by rfl
example : Condition.LT = .ofBitVec 0b1011 := by rfl
example : Condition.GT = .ofBitVec 0b1100 := by rfl
example : Condition.LE = .ofBitVec 0b1101 := by rfl
example : Condition.AL = .ofBitVec 0b1110 := by rfl
example : Condition.NV = .ofBitVec 0b1111 := by rfl

example : Condition.EQ.invert = .NE := by rfl
example : Condition.NE.invert = .EQ := by rfl
example : Condition.CS.invert = .CC := by rfl
example : Condition.CC.invert = .CS := by rfl
example : Condition.MI.invert = .PL := by rfl
example : Condition.PL.invert = .MI := by rfl
example : Condition.VS.invert = .VC := by rfl
example : Condition.VC.invert = .VS := by rfl
example : Condition.HI.invert = .LS := by rfl
example : Condition.LS.invert = .HI := by rfl
example : Condition.GE.invert = .LT := by rfl
example : Condition.LT.invert = .GE := by rfl
example : Condition.GT.invert = .LE := by rfl
example : Condition.LE.invert = .GT := by rfl
example : Condition.AL.invert = .NV := by rfl
example : Condition.NV.invert = .AL := by rfl
