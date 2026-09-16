/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/

import Bignum.ArmRev

open Bignum.ArmRev

open State

-- allZeros

example : NF.read allZeros = false := by rfl
example : ZF.read allZeros = false := by rfl
example : CF.read allZeros = false := by rfl
example : VF.read allZeros = false := by rfl

example : XZR.read allZeros = 0#64 := by rfl
-- example : State.allZeros.X0 = 0#64 := by rfl
-- example : State.allZeros.X1 = 0#64 := by rfl
-- example : State.allZeros.X2 = 0#64 := by rfl
-- example : State.allZeros.X3 = 0#64 := by rfl
-- example : State.allZeros.X4 = 0#64 := by rfl
-- example : State.allZeros.X5 = 0#64 := by rfl
-- example : State.allZeros.X6 = 0#64 := by rfl
-- example : State.allZeros.X7 = 0#64 := by rfl
-- example : State.allZeros.X8 = 0#64 := by rfl
-- example : State.allZeros.X9 = 0#64 := by rfl
-- example : State.allZeros.X10 = 0#64 := by rfl
-- example : State.allZeros.X11 = 0#64 := by rfl
-- example : State.allZeros.X12 = 0#64 := by rfl
-- example : State.allZeros.X13 = 0#64 := by rfl
-- example : State.allZeros.X14 = 0#64 := by rfl
-- example : State.allZeros.X15 = 0#64 := by rfl
-- example : State.allZeros.X16 = 0#64 := by rfl
-- example : State.allZeros.X17 = 0#64 := by rfl
-- example : State.allZeros.X18 = 0#64 := by rfl
-- example : State.allZeros.X19 = 0#64 := by rfl
-- example : State.allZeros.X20 = 0#64 := by rfl
-- example : State.allZeros.X21 = 0#64 := by rfl
-- example : State.allZeros.X22 = 0#64 := by rfl
-- example : State.allZeros.X23 = 0#64 := by rfl
-- example : State.allZeros.X24 = 0#64 := by rfl
-- example : State.allZeros.X25 = 0#64 := by rfl
-- example : State.allZeros.X26 = 0#64 := by rfl
-- example : State.allZeros.X27 = 0#64 := by rfl
-- example : State.allZeros.X28 = 0#64 := by rfl
-- example : State.allZeros.X29 = 0#64 := by rfl
-- example : State.allZeros.X30 = 0#64 := by rfl
-- example : State.allZeros.SP = 0#64 := by rfl

-- example : State.allZeros.W0 = 0#32 := by rfl
-- example : State.allZeros.W1 = 0#32 := by rfl
-- example : State.allZeros.W2 = 0#32 := by rfl
-- example : State.allZeros.W3 = 0#32 := by rfl
-- example : State.allZeros.W4 = 0#32 := by rfl
-- example : State.allZeros.W5 = 0#32 := by rfl
-- example : State.allZeros.W6 = 0#32 := by rfl
-- example : State.allZeros.W7 = 0#32 := by rfl
-- example : State.allZeros.W8 = 0#32 := by rfl
-- example : State.allZeros.W9 = 0#32 := by rfl
-- example : State.allZeros.W10 = 0#32 := by rfl
-- example : State.allZeros.W11 = 0#32 := by rfl
-- example : State.allZeros.W12 = 0#32 := by rfl
-- example : State.allZeros.W13 = 0#32 := by rfl
-- example : State.allZeros.W14 = 0#32 := by rfl
-- example : State.allZeros.W15 = 0#32 := by rfl
-- example : State.allZeros.W16 = 0#32 := by rfl
-- example : State.allZeros.W17 = 0#32 := by rfl
-- example : State.allZeros.W18 = 0#32 := by rfl
-- example : State.allZeros.W19 = 0#32 := by rfl
-- example : State.allZeros.W20 = 0#32 := by rfl
-- example : State.allZeros.W21 = 0#32 := by rfl
-- example : State.allZeros.W22 = 0#32 := by rfl
-- example : State.allZeros.W23 = 0#32 := by rfl
-- example : State.allZeros.W24 = 0#32 := by rfl
-- example : State.allZeros.W25 = 0#32 := by rfl
-- example : State.allZeros.W26 = 0#32 := by rfl
-- example : State.allZeros.W27 = 0#32 := by rfl
-- example : State.allZeros.W28 = 0#32 := by rfl
-- example : State.allZeros.W29 = 0#32 := by rfl
-- example : State.allZeros.W30 = 0#32 := by rfl
-- example : State.allZeros.WSP = 0#32 := by rfl

-- -- allOnes

example : NF.read allOnes = true := by rfl
example : ZF.read allOnes = true := by rfl
example : CF.read allOnes = true := by rfl
example : VF.read allOnes = true := by rfl

example : XZR.read allOnes = 0#64 := by rfl
-- example : State.allOnes.X0 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X1 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X2 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X3 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X4 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X5 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X6 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X7 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X8 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X9 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X10 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X11 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X12 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X13 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X14 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X15 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X16 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X17 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X18 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X19 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X20 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X21 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X22 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X23 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X24 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X25 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X26 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X27 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X28 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X29 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.X30 = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.SP = 0xffffffffffffffff#64 := by rfl
-- example : State.allOnes.W0 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W1 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W2 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W3 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W4 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W5 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W6 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W7 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W8 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W9 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W10 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W11 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W12 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W13 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W14 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W15 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W16 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W17 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W18 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W19 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W20 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W21 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W22 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W23 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W24 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W25 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W26 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W27 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W28 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W29 = 0xffffffff#32 := by rfl
-- example : State.allOnes.W30 = 0xffffffff#32 := by rfl
-- example : State.allOnes.WSP = 0xffffffff#32 := by rfl
