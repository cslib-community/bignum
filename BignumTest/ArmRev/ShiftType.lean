/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/

import Bignum.ArmRev

open Bignum.ArmRev

-- -- LSL

-- example : ShiftType.LSL.shift 1 4#32 = 8#32 := by rfl
-- example : ShiftType.LSL.shift 1 0x80000000#32 = 0#32 := by rfl

-- -- LSR

-- example : ShiftType.LSR.shift 1 4#32 = 2#32 := by rfl
-- example : ShiftType.LSR.shift 1 1#32 = 0#32 := by rfl

-- -- ASR

-- example : ShiftType.ASR.shift 1 0#32 = 0#32 := by rfl
-- example : ShiftType.ASR.shift 1 1#32 = 0#32 := by rfl
-- example : ShiftType.ASR.shift 1 5#4 = 2#4 := by rfl

-- -- ROR

-- example : ShiftType.ROR.shift 1 1#8 = 0x80#8 := by rfl
-- example : ShiftType.ROR.shift 1 2#4 = 1#4 := by rfl
