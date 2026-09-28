/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/
module

import Bignum.Arm

open Bignum.Arm

example : ShiftType.LSL.shift 1 4#32 = 8#32 := by rfl
example : ShiftType.LSL.shift 1 0x80000000#32 = 0#32 := by rfl

example : ShiftType.LSR.shift 1 4#32 = 2#32 := by rfl
example : ShiftType.LSR.shift 1 1#32 = 0#32 := by rfl

example : ShiftType.ASR.shift 1 0#32 = 0#32 := by rfl
example : ShiftType.ASR.shift 1 1#32 = 0#32 := by rfl
example : ShiftType.ASR.shift 1 5#4 = 2#4 := by rfl

example : ShiftType.ROR.shift 1 1#8 = 0x80#8 := by rfl
example : ShiftType.ROR.shift 1 2#4 = 1#4 := by rfl

open State

example : (shifted .LSL 1 X0).read (X0.write 4 .allZeros) = 8 := by rfl
example : (shifted .LSL 1 X0).read
    (X0.write 0x8000000000000000 .allZeros) = 0 := by rfl

example : (shifted .LSR 1 X0).read (X0.write 4 .allZeros) = 2 := by rfl
example : (shifted .LSR 1 X0).read (X0.write 1 .allZeros) = 0 := by rfl

example : (shifted .ASR 1 X0).read (X0.write 0 .allZeros) = 0 := by rfl
example : (shifted .ASR 1 X0).read (X0.write 1 .allZeros) = 0 := by rfl
example : (shifted .ASR 1 X0).read (X0.write 5 .allZeros) = 2 := by rfl

example : (shifted .ROR 1 X0).read
    (X0.write 1 .allZeros) = 0x8000000000000000 := by rfl
example : (shifted .ROR 1 X0).read (X0.write 2 .allZeros) = 1 := by rfl
