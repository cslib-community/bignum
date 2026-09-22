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

example : NF.read (NF.write true allZeros) = true := by rfl
example : NF.read (ZF.write true allZeros) = false := by rfl

example : (NF.write true allZeros)._flags = 0b1000 := by rfl
example : (ZF.write true allZeros)._flags = 0b0100 := by rfl
example : (CF.write true allZeros)._flags = 0b0010 := by rfl
example : (VF.write true allZeros)._flags = 0b0001 := by rfl

example : XZR.read allZeros = 0#64 := by rfl
example : XZR.read (XZR.write 1 allZeros) = 0#64 := by rfl
example : WZR.read allZeros = 0#32 := by rfl
example : WZR.read (WZR.write 1 allZeros) = 0#32 := by rfl

example : X0.read allZeros = 0#64 := by rfl
example : X1.read allZeros = 0#64 := by rfl
example : X2.read allZeros = 0#64 := by rfl
example : X3.read allZeros = 0#64 := by rfl
example : X4.read allZeros = 0#64 := by rfl
example : X5.read allZeros = 0#64 := by rfl
example : X6.read allZeros = 0#64 := by rfl
example : X7.read allZeros = 0#64 := by rfl
example : X8.read allZeros = 0#64 := by rfl
example : X9.read allZeros = 0#64 := by rfl
example : X10.read allZeros = 0#64 := by rfl
example : X11.read allZeros = 0#64 := by rfl
example : X12.read allZeros = 0#64 := by rfl
example : X13.read allZeros = 0#64 := by rfl
example : X14.read allZeros = 0#64 := by rfl
example : X15.read allZeros = 0#64 := by rfl
example : X16.read allZeros = 0#64 := by rfl
example : X17.read allZeros = 0#64 := by rfl
example : X18.read allZeros = 0#64 := by rfl
example : X19.read allZeros = 0#64 := by rfl
example : X20.read allZeros = 0#64 := by rfl
example : X21.read allZeros = 0#64 := by rfl
example : X22.read allZeros = 0#64 := by rfl
example : X23.read allZeros = 0#64 := by rfl
example : X24.read allZeros = 0#64 := by rfl
example : X25.read allZeros = 0#64 := by rfl
example : X26.read allZeros = 0#64 := by rfl
example : X27.read allZeros = 0#64 := by rfl
example : X28.read allZeros = 0#64 := by rfl
example : X29.read allZeros = 0#64 := by rfl
example : X30.read allZeros = 0#64 := by rfl
example : SP.read allZeros = 0#64 := by rfl

example : (X0.write 0xff allZeros)._registers 0 = 0xff := by rfl
example : (X1.write 0xff allZeros)._registers 1 = 0xff := by rfl
example : (X2.write 0xff allZeros)._registers 2 = 0xff := by rfl
example : (X3.write 0xff allZeros)._registers 3 = 0xff := by rfl
example : (X4.write 0xff allZeros)._registers 4 = 0xff := by rfl
example : (X5.write 0xff allZeros)._registers 5 = 0xff := by rfl
example : (X6.write 0xff allZeros)._registers 6 = 0xff := by rfl
example : (X7.write 0xff allZeros)._registers 7 = 0xff := by rfl
example : (X8.write 0xff allZeros)._registers 8 = 0xff := by rfl
example : (X9.write 0xff allZeros)._registers 9 = 0xff := by rfl
example : (X10.write 0xff allZeros)._registers 10 = 0xff := by rfl
example : (X11.write 0xff allZeros)._registers 11 = 0xff := by rfl
example : (X12.write 0xff allZeros)._registers 12 = 0xff := by rfl
example : (X13.write 0xff allZeros)._registers 13 = 0xff := by rfl
example : (X14.write 0xff allZeros)._registers 14 = 0xff := by rfl
example : (X15.write 0xff allZeros)._registers 15 = 0xff := by rfl
example : (X16.write 0xff allZeros)._registers 16 = 0xff := by rfl
example : (X17.write 0xff allZeros)._registers 17 = 0xff := by rfl
example : (X18.write 0xff allZeros)._registers 18 = 0xff := by rfl
example : (X19.write 0xff allZeros)._registers 19 = 0xff := by rfl
example : (X20.write 0xff allZeros)._registers 20 = 0xff := by rfl
example : (X21.write 0xff allZeros)._registers 21 = 0xff := by rfl
example : (X22.write 0xff allZeros)._registers 22 = 0xff := by rfl
example : (X23.write 0xff allZeros)._registers 23 = 0xff := by rfl
example : (X24.write 0xff allZeros)._registers 24 = 0xff := by rfl
example : (X25.write 0xff allZeros)._registers 25 = 0xff := by rfl
example : (X26.write 0xff allZeros)._registers 26 = 0xff := by rfl
example : (X27.write 0xff allZeros)._registers 27 = 0xff := by rfl
example : (X28.write 0xff allZeros)._registers 28 = 0xff := by rfl
example : (X29.write 0xff allZeros)._registers 29 = 0xff := by rfl
example : (X30.write 0xff allZeros)._registers 30 = 0xff := by rfl
example : (SP.write 0xff allZeros)._registers 31 = 0xff := by rfl
example : ((XREG 31).write 0xff allZeros)._registers 31 = 0x0 := by rfl

example : W0.read allZeros = 0#32 := by rfl
example : W1.read allZeros = 0#32 := by rfl
example : W2.read allZeros = 0#32 := by rfl
example : W3.read allZeros = 0#32 := by rfl
example : W4.read allZeros = 0#32 := by rfl
example : W5.read allZeros = 0#32 := by rfl
example : W6.read allZeros = 0#32 := by rfl
example : W7.read allZeros = 0#32 := by rfl
example : W8.read allZeros = 0#32 := by rfl
example : W9.read allZeros = 0#32 := by rfl
example : W10.read allZeros = 0#32 := by rfl
example : W11.read allZeros = 0#32 := by rfl
example : W12.read allZeros = 0#32 := by rfl
example : W13.read allZeros = 0#32 := by rfl
example : W14.read allZeros = 0#32 := by rfl
example : W15.read allZeros = 0#32 := by rfl
example : W16.read allZeros = 0#32 := by rfl
example : W17.read allZeros = 0#32 := by rfl
example : W18.read allZeros = 0#32 := by rfl
example : W19.read allZeros = 0#32 := by rfl
example : W20.read allZeros = 0#32 := by rfl
example : W21.read allZeros = 0#32 := by rfl
example : W22.read allZeros = 0#32 := by rfl
example : W23.read allZeros = 0#32 := by rfl
example : W24.read allZeros = 0#32 := by rfl
example : W25.read allZeros = 0#32 := by rfl
example : W26.read allZeros = 0#32 := by rfl
example : W27.read allZeros = 0#32 := by rfl
example : W28.read allZeros = 0#32 := by rfl
example : W29.read allZeros = 0#32 := by rfl
example : W30.read allZeros = 0#32 := by rfl
example : WSP.read allZeros = 0#32 := by rfl

example : (W0.write 0xff allZeros)._registers 0 = 0xff := by rfl
example : (W1.write 0xff allZeros)._registers 1 = 0xff := by rfl
example : (W2.write 0xff allZeros)._registers 2 = 0xff := by rfl
example : (W3.write 0xff allZeros)._registers 3 = 0xff := by rfl
example : (W4.write 0xff allZeros)._registers 4 = 0xff := by rfl
example : (W5.write 0xff allZeros)._registers 5 = 0xff := by rfl
example : (W6.write 0xff allZeros)._registers 6 = 0xff := by rfl
example : (W7.write 0xff allZeros)._registers 7 = 0xff := by rfl
example : (W8.write 0xff allZeros)._registers 8 = 0xff := by rfl
example : (W9.write 0xff allZeros)._registers 9 = 0xff := by rfl
example : (W10.write 0xff allZeros)._registers 10 = 0xff := by rfl
example : (W11.write 0xff allZeros)._registers 11 = 0xff := by rfl
example : (W12.write 0xff allZeros)._registers 12 = 0xff := by rfl
example : (W13.write 0xff allZeros)._registers 13 = 0xff := by rfl
example : (W14.write 0xff allZeros)._registers 14 = 0xff := by rfl
example : (W15.write 0xff allZeros)._registers 15 = 0xff := by rfl
example : (W16.write 0xff allZeros)._registers 16 = 0xff := by rfl
example : (W17.write 0xff allZeros)._registers 17 = 0xff := by rfl
example : (W18.write 0xff allZeros)._registers 18 = 0xff := by rfl
example : (W19.write 0xff allZeros)._registers 19 = 0xff := by rfl
example : (W20.write 0xff allZeros)._registers 20 = 0xff := by rfl
example : (W21.write 0xff allZeros)._registers 21 = 0xff := by rfl
example : (W22.write 0xff allZeros)._registers 22 = 0xff := by rfl
example : (W23.write 0xff allZeros)._registers 23 = 0xff := by rfl
example : (W24.write 0xff allZeros)._registers 24 = 0xff := by rfl
example : (W25.write 0xff allZeros)._registers 25 = 0xff := by rfl
example : (W26.write 0xff allZeros)._registers 26 = 0xff := by rfl
example : (W27.write 0xff allZeros)._registers 27 = 0xff := by rfl
example : (W28.write 0xff allZeros)._registers 28 = 0xff := by rfl
example : (W29.write 0xff allZeros)._registers 29 = 0xff := by rfl
example : (W30.write 0xff allZeros)._registers 30 = 0xff := by rfl
example : (WSP.write 0xff allZeros)._registers 31 = 0xff := by rfl
example : ((WREG 31).write 0xff allZeros)._registers 31 = 0x0 := by rfl

-- allOnes

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
