/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/

import Bignum.Arm
open Bignum.Arm.State

/-! # Unit tests for ARM state -/

def S₀ := allZeros
def S₁ := allOnes

/-! ## allZeros -/

example : allZeros._PC               = 0  := by rfl
example : allZeros._registers 42     = 0  := by rfl
example : allZeros._simdregisters 42 = 0  := by rfl
example : allZeros._flags            = 0  := by rfl
example : allZeros._memory 42        = 0  := by rfl
example : allZeros._events           = [] := by rfl

/-! ## allOnes -/

example : allOnes._PC               = .allOnes 64  := by rfl
example : allOnes._registers 42     = .allOnes 64  := by rfl
example : allOnes._simdregisters 42 = .allOnes 128 := by rfl
example : allOnes._flags            = .allOnes 4   := by rfl
example : allOnes._memory 42        = .allOnes 8   := by rfl
example : allOnes._events           = []           := by rfl

/-! ## State components -/

example : PC.read S₀            = S₀._PC            := by rfl
example : PC.read S₁            = S₁._PC            := by rfl
example : registers.read S₀     = S₀._registers     := by rfl
example : registers.read S₁     = S₁._registers     := by rfl
example : simdregisters.read S₀ = S₀._simdregisters := by rfl
example : simdregisters.read S₁ = S₁._simdregisters := by rfl
example : flags.read S₀         = S₀._flags         := by rfl
example : flags.read S₁         = S₁._flags         := by rfl
example : memory.read S₀        = S₀._memory        := by rfl
example : memory.read S₁        = S₁._memory        := by rfl
example : events.read S₀        = S₀._events        := by rfl
example : events.read S₁        = S₁._events        := by rfl

example : PC.read (PC.write 1 S₀) = 1 := by rfl
example : flags.read (PC.write 1 S₀) = 0 := by rfl
example : PC.read (PC.write 1 S₁) = 1 := by rfl
example : flags.read (PC.write 1 S₁) = .allOnes 4 := by rfl

/-! ## Condition flags -/

example : NF.read S₀ = false := by rfl
example : ZF.read S₀ = false := by rfl
example : CF.read S₀ = false := by rfl
example : VF.read S₀ = false := by rfl

example : NF.read S₁ = true := by rfl
example : ZF.read S₁ = true := by rfl
example : CF.read S₁ = true := by rfl
example : VF.read S₁ = true := by rfl

example : NF.read (NF.write true S₀) = true := by rfl
example : NF.read (ZF.write true S₀) = false := by rfl
example : NF.read (NF.write false S₁) = false := by rfl
example : NF.read (ZF.write false S₁) = true := by rfl

example : (NF.write true S₀)._flags = 0b1000 := by rfl
example : (ZF.write true S₀)._flags = 0b0100 := by rfl
example : (CF.write true S₀)._flags = 0b0010 := by rfl
example : (VF.write true S₀)._flags = 0b0001 := by rfl

example : (NF.write false S₁)._flags = 0b0111 := by rfl
example : (ZF.write false S₁)._flags = 0b1011 := by rfl
example : (CF.write false S₁)._flags = 0b1101 := by rfl
example : (VF.write false S₁)._flags = 0b1110 := by rfl

/-! ## Zero registers -/

example : XZR.read S₀ = 0#64 := by rfl
example : XZR.read S₁ = 0#64 := by rfl
example : XZR.read (XZR.write 1 S₀) = 0#64 := by rfl
example : XZR.read (XZR.write 1 S₁) = 0#64 := by rfl

example : WZR.read S₀ = 0#32 := by rfl
example : WZR.read S₁ = 0#32 := by rfl
example : WZR.read (WZR.write 1 S₀) = 0#32 := by rfl
example : WZR.read (WZR.write 1 S₁) = 0#32 := by rfl

/-! ## Main registers -/

example : X0.read S₀  = 0#64 := by rfl
example : X1.read S₀  = 0#64 := by rfl
example : X2.read S₀  = 0#64 := by rfl
example : X3.read S₀  = 0#64 := by rfl
example : X4.read S₀  = 0#64 := by rfl
example : X5.read S₀  = 0#64 := by rfl
example : X6.read S₀  = 0#64 := by rfl
example : X7.read S₀  = 0#64 := by rfl
example : X8.read S₀  = 0#64 := by rfl
example : X9.read S₀  = 0#64 := by rfl
example : X10.read S₀ = 0#64 := by rfl
example : X11.read S₀ = 0#64 := by rfl
example : X12.read S₀ = 0#64 := by rfl
example : X13.read S₀ = 0#64 := by rfl
example : X14.read S₀ = 0#64 := by rfl
example : X15.read S₀ = 0#64 := by rfl
example : X16.read S₀ = 0#64 := by rfl
example : X17.read S₀ = 0#64 := by rfl
example : X18.read S₀ = 0#64 := by rfl
example : X19.read S₀ = 0#64 := by rfl
example : X20.read S₀ = 0#64 := by rfl
example : X21.read S₀ = 0#64 := by rfl
example : X22.read S₀ = 0#64 := by rfl
example : X23.read S₀ = 0#64 := by rfl
example : X24.read S₀ = 0#64 := by rfl
example : X25.read S₀ = 0#64 := by rfl
example : X26.read S₀ = 0#64 := by rfl
example : X27.read S₀ = 0#64 := by rfl
example : X28.read S₀ = 0#64 := by rfl
example : X29.read S₀ = 0#64 := by rfl
example : X30.read S₀ = 0#64 := by rfl
example : SP.read S₀  = 0#64 := by rfl

example : X0.read S₁  = .allOnes 64 := by rfl
example : X1.read S₁  = .allOnes 64 := by rfl
example : X2.read S₁  = .allOnes 64 := by rfl
example : X3.read S₁  = .allOnes 64 := by rfl
example : X4.read S₁  = .allOnes 64 := by rfl
example : X5.read S₁  = .allOnes 64 := by rfl
example : X6.read S₁  = .allOnes 64 := by rfl
example : X7.read S₁  = .allOnes 64 := by rfl
example : X8.read S₁  = .allOnes 64 := by rfl
example : X9.read S₁  = .allOnes 64 := by rfl
example : X10.read S₁ = .allOnes 64 := by rfl
example : X11.read S₁ = .allOnes 64 := by rfl
example : X12.read S₁ = .allOnes 64 := by rfl
example : X13.read S₁ = .allOnes 64 := by rfl
example : X14.read S₁ = .allOnes 64 := by rfl
example : X15.read S₁ = .allOnes 64 := by rfl
example : X16.read S₁ = .allOnes 64 := by rfl
example : X17.read S₁ = .allOnes 64 := by rfl
example : X18.read S₁ = .allOnes 64 := by rfl
example : X19.read S₁ = .allOnes 64 := by rfl
example : X20.read S₁ = .allOnes 64 := by rfl
example : X21.read S₁ = .allOnes 64 := by rfl
example : X22.read S₁ = .allOnes 64 := by rfl
example : X23.read S₁ = .allOnes 64 := by rfl
example : X24.read S₁ = .allOnes 64 := by rfl
example : X25.read S₁ = .allOnes 64 := by rfl
example : X26.read S₁ = .allOnes 64 := by rfl
example : X27.read S₁ = .allOnes 64 := by rfl
example : X28.read S₁ = .allOnes 64 := by rfl
example : X29.read S₁ = .allOnes 64 := by rfl
example : X30.read S₁ = .allOnes 64 := by rfl
example : SP.read S₁  = .allOnes 64 := by rfl

example : (X0.write 1 S₀)._registers 0 = 1 := by rfl
example : (X1.write 1 S₀)._registers 1 = 1 := by rfl
example : (X2.write 1 S₀)._registers 2 = 1 := by rfl
example : (X3.write 1 S₀)._registers 3 = 1 := by rfl
example : (X4.write 1 S₀)._registers 4 = 1 := by rfl
example : (X5.write 1 S₀)._registers 5 = 1 := by rfl
example : (X6.write 1 S₀)._registers 6 = 1 := by rfl
example : (X7.write 1 S₀)._registers 7 = 1 := by rfl
example : (X8.write 1 S₀)._registers 8 = 1 := by rfl
example : (X9.write 1 S₀)._registers 9 = 1 := by rfl
example : (X10.write 1 S₀)._registers 10 = 1 := by rfl
example : (X11.write 1 S₀)._registers 11 = 1 := by rfl
example : (X12.write 1 S₀)._registers 12 = 1 := by rfl
example : (X13.write 1 S₀)._registers 13 = 1 := by rfl
example : (X14.write 1 S₀)._registers 14 = 1 := by rfl
example : (X15.write 1 S₀)._registers 15 = 1 := by rfl
example : (X16.write 1 S₀)._registers 16 = 1 := by rfl
example : (X17.write 1 S₀)._registers 17 = 1 := by rfl
example : (X18.write 1 S₀)._registers 18 = 1 := by rfl
example : (X19.write 1 S₀)._registers 19 = 1 := by rfl
example : (X20.write 1 S₀)._registers 20 = 1 := by rfl
example : (X21.write 1 S₀)._registers 21 = 1 := by rfl
example : (X22.write 1 S₀)._registers 22 = 1 := by rfl
example : (X23.write 1 S₀)._registers 23 = 1 := by rfl
example : (X24.write 1 S₀)._registers 24 = 1 := by rfl
example : (X25.write 1 S₀)._registers 25 = 1 := by rfl
example : (X26.write 1 S₀)._registers 26 = 1 := by rfl
example : (X27.write 1 S₀)._registers 27 = 1 := by rfl
example : (X28.write 1 S₀)._registers 28 = 1 := by rfl
example : (X29.write 1 S₀)._registers 29 = 1 := by rfl
example : (X30.write 1 S₀)._registers 30 = 1 := by rfl
example : (SP.write 1 S₀)._registers 31 = 1 := by rfl

example : (X0.write 0 S₁)._registers 0 = 0 := by rfl
example : (X1.write 0 S₁)._registers 1 = 0 := by rfl
example : (X2.write 0 S₁)._registers 2 = 0 := by rfl
example : (X3.write 0 S₁)._registers 3 = 0 := by rfl
example : (X4.write 0 S₁)._registers 4 = 0 := by rfl
example : (X5.write 0 S₁)._registers 5 = 0 := by rfl
example : (X6.write 0 S₁)._registers 6 = 0 := by rfl
example : (X7.write 0 S₁)._registers 7 = 0 := by rfl
example : (X8.write 0 S₁)._registers 8 = 0 := by rfl
example : (X9.write 0 S₁)._registers 9 = 0 := by rfl
example : (X10.write 0 S₁)._registers 10 = 0 := by rfl
example : (X11.write 0 S₁)._registers 11 = 0 := by rfl
example : (X12.write 0 S₁)._registers 12 = 0 := by rfl
example : (X13.write 0 S₁)._registers 13 = 0 := by rfl
example : (X14.write 0 S₁)._registers 14 = 0 := by rfl
example : (X15.write 0 S₁)._registers 15 = 0 := by rfl
example : (X16.write 0 S₁)._registers 16 = 0 := by rfl
example : (X17.write 0 S₁)._registers 17 = 0 := by rfl
example : (X18.write 0 S₁)._registers 18 = 0 := by rfl
example : (X19.write 0 S₁)._registers 19 = 0 := by rfl
example : (X20.write 0 S₁)._registers 20 = 0 := by rfl
example : (X21.write 0 S₁)._registers 21 = 0 := by rfl
example : (X22.write 0 S₁)._registers 22 = 0 := by rfl
example : (X23.write 0 S₁)._registers 23 = 0 := by rfl
example : (X24.write 0 S₁)._registers 24 = 0 := by rfl
example : (X25.write 0 S₁)._registers 25 = 0 := by rfl
example : (X26.write 0 S₁)._registers 26 = 0 := by rfl
example : (X27.write 0 S₁)._registers 27 = 0 := by rfl
example : (X28.write 0 S₁)._registers 28 = 0 := by rfl
example : (X29.write 0 S₁)._registers 29 = 0 := by rfl
example : (X30.write 0 S₁)._registers 30 = 0 := by rfl
example : (SP.write 0 S₁)._registers 31 = 0 := by rfl

example : (XREG 31).read ((XREG 31).write 1 S₀) = 0 := by rfl
example : (XREG 31).read ((XREG 31).write 8 S₁) = 0 := by rfl

/-! ## 32-bit versions of the main registers -/

example : W0.read S₀  = 0#32 := by rfl
example : W1.read S₀  = 0#32 := by rfl
example : W2.read S₀  = 0#32 := by rfl
example : W3.read S₀  = 0#32 := by rfl
example : W4.read S₀  = 0#32 := by rfl
example : W5.read S₀  = 0#32 := by rfl
example : W6.read S₀  = 0#32 := by rfl
example : W7.read S₀  = 0#32 := by rfl
example : W8.read S₀  = 0#32 := by rfl
example : W9.read S₀  = 0#32 := by rfl
example : W10.read S₀ = 0#32 := by rfl
example : W11.read S₀ = 0#32 := by rfl
example : W12.read S₀ = 0#32 := by rfl
example : W13.read S₀ = 0#32 := by rfl
example : W14.read S₀ = 0#32 := by rfl
example : W15.read S₀ = 0#32 := by rfl
example : W16.read S₀ = 0#32 := by rfl
example : W17.read S₀ = 0#32 := by rfl
example : W18.read S₀ = 0#32 := by rfl
example : W19.read S₀ = 0#32 := by rfl
example : W20.read S₀ = 0#32 := by rfl
example : W21.read S₀ = 0#32 := by rfl
example : W22.read S₀ = 0#32 := by rfl
example : W23.read S₀ = 0#32 := by rfl
example : W24.read S₀ = 0#32 := by rfl
example : W25.read S₀ = 0#32 := by rfl
example : W26.read S₀ = 0#32 := by rfl
example : W27.read S₀ = 0#32 := by rfl
example : W28.read S₀ = 0#32 := by rfl
example : W29.read S₀ = 0#32 := by rfl
example : W30.read S₀ = 0#32 := by rfl
example : WSP.read S₀ = 0#32 := by rfl

example : W0.read S₁  = .allOnes 32 := by rfl
example : W1.read S₁  = .allOnes 32 := by rfl
example : W2.read S₁  = .allOnes 32 := by rfl
example : W3.read S₁  = .allOnes 32 := by rfl
example : W4.read S₁  = .allOnes 32 := by rfl
example : W5.read S₁  = .allOnes 32 := by rfl
example : W6.read S₁  = .allOnes 32 := by rfl
example : W7.read S₁  = .allOnes 32 := by rfl
example : W8.read S₁  = .allOnes 32 := by rfl
example : W9.read S₁  = .allOnes 32 := by rfl
example : W10.read S₁ = .allOnes 32 := by rfl
example : W11.read S₁ = .allOnes 32 := by rfl
example : W12.read S₁ = .allOnes 32 := by rfl
example : W13.read S₁ = .allOnes 32 := by rfl
example : W14.read S₁ = .allOnes 32 := by rfl
example : W15.read S₁ = .allOnes 32 := by rfl
example : W16.read S₁ = .allOnes 32 := by rfl
example : W17.read S₁ = .allOnes 32 := by rfl
example : W18.read S₁ = .allOnes 32 := by rfl
example : W19.read S₁ = .allOnes 32 := by rfl
example : W20.read S₁ = .allOnes 32 := by rfl
example : W21.read S₁ = .allOnes 32 := by rfl
example : W22.read S₁ = .allOnes 32 := by rfl
example : W23.read S₁ = .allOnes 32 := by rfl
example : W24.read S₁ = .allOnes 32 := by rfl
example : W25.read S₁ = .allOnes 32 := by rfl
example : W26.read S₁ = .allOnes 32 := by rfl
example : W27.read S₁ = .allOnes 32 := by rfl
example : W28.read S₁ = .allOnes 32 := by rfl
example : W29.read S₁ = .allOnes 32 := by rfl
example : W30.read S₁ = .allOnes 32 := by rfl
example : WSP.read S₁ = .allOnes 32 := by rfl

example : (W0.write 1 S₀)._registers 0 = 1 := by rfl
example : (W1.write 1 S₀)._registers 1 = 1 := by rfl
example : (W2.write 1 S₀)._registers 2 = 1 := by rfl
example : (W3.write 1 S₀)._registers 3 = 1 := by rfl
example : (W4.write 1 S₀)._registers 4 = 1 := by rfl
example : (W5.write 1 S₀)._registers 5 = 1 := by rfl
example : (W6.write 1 S₀)._registers 6 = 1 := by rfl
example : (W7.write 1 S₀)._registers 7 = 1 := by rfl
example : (W8.write 1 S₀)._registers 8 = 1 := by rfl
example : (W9.write 1 S₀)._registers 9 = 1 := by rfl
example : (W10.write 1 S₀)._registers 10 = 1 := by rfl
example : (W11.write 1 S₀)._registers 11 = 1 := by rfl
example : (W12.write 1 S₀)._registers 12 = 1 := by rfl
example : (W13.write 1 S₀)._registers 13 = 1 := by rfl
example : (W14.write 1 S₀)._registers 14 = 1 := by rfl
example : (W15.write 1 S₀)._registers 15 = 1 := by rfl
example : (W16.write 1 S₀)._registers 16 = 1 := by rfl
example : (W17.write 1 S₀)._registers 17 = 1 := by rfl
example : (W18.write 1 S₀)._registers 18 = 1 := by rfl
example : (W19.write 1 S₀)._registers 19 = 1 := by rfl
example : (W20.write 1 S₀)._registers 20 = 1 := by rfl
example : (W21.write 1 S₀)._registers 21 = 1 := by rfl
example : (W22.write 1 S₀)._registers 22 = 1 := by rfl
example : (W23.write 1 S₀)._registers 23 = 1 := by rfl
example : (W24.write 1 S₀)._registers 24 = 1 := by rfl
example : (W25.write 1 S₀)._registers 25 = 1 := by rfl
example : (W26.write 1 S₀)._registers 26 = 1 := by rfl
example : (W27.write 1 S₀)._registers 27 = 1 := by rfl
example : (W28.write 1 S₀)._registers 28 = 1 := by rfl
example : (W29.write 1 S₀)._registers 29 = 1 := by rfl
example : (W30.write 1 S₀)._registers 30 = 1 := by rfl
example : (WSP.write 1 S₀)._registers 31 = 1 := by rfl

example : (W0.write 0 S₁)._registers 0 = 0 := by rfl
example : (W1.write 0 S₁)._registers 1 = 0 := by rfl
example : (W2.write 0 S₁)._registers 2 = 0 := by rfl
example : (W3.write 0 S₁)._registers 3 = 0 := by rfl
example : (W4.write 0 S₁)._registers 4 = 0 := by rfl
example : (W5.write 0 S₁)._registers 5 = 0 := by rfl
example : (W6.write 0 S₁)._registers 6 = 0 := by rfl
example : (W7.write 0 S₁)._registers 7 = 0 := by rfl
example : (W8.write 0 S₁)._registers 8 = 0 := by rfl
example : (W9.write 0 S₁)._registers 9 = 0 := by rfl
example : (W10.write 0 S₁)._registers 10 = 0 := by rfl
example : (W11.write 0 S₁)._registers 11 = 0 := by rfl
example : (W12.write 0 S₁)._registers 12 = 0 := by rfl
example : (W13.write 0 S₁)._registers 13 = 0 := by rfl
example : (W14.write 0 S₁)._registers 14 = 0 := by rfl
example : (W15.write 0 S₁)._registers 15 = 0 := by rfl
example : (W16.write 0 S₁)._registers 16 = 0 := by rfl
example : (W17.write 0 S₁)._registers 17 = 0 := by rfl
example : (W18.write 0 S₁)._registers 18 = 0 := by rfl
example : (W19.write 0 S₁)._registers 19 = 0 := by rfl
example : (W20.write 0 S₁)._registers 20 = 0 := by rfl
example : (W21.write 0 S₁)._registers 21 = 0 := by rfl
example : (W22.write 0 S₁)._registers 22 = 0 := by rfl
example : (W23.write 0 S₁)._registers 23 = 0 := by rfl
example : (W24.write 0 S₁)._registers 24 = 0 := by rfl
example : (W25.write 0 S₁)._registers 25 = 0 := by rfl
example : (W26.write 0 S₁)._registers 26 = 0 := by rfl
example : (W27.write 0 S₁)._registers 27 = 0 := by rfl
example : (W28.write 0 S₁)._registers 28 = 0 := by rfl
example : (W29.write 0 S₁)._registers 29 = 0 := by rfl
example : (W30.write 0 S₁)._registers 30 = 0 := by rfl
example : (WSP.write 0 S₁)._registers 31 = 0 := by rfl

example : (WREG 31).read ((WREG 31).write 1 S₀) = 0 := by rfl
example : (WREG 31).read ((WREG 31).write 8 S₁) = 0 := by rfl

-- Writing to W* should overwrite the top 32-bit of X* with 0.
example : X0.read (W0.write (1 <<< 33) allOnes) = 0 := by rfl
example : SP.read (WSP.write 0 allOnes) = 0 := by rfl

/-! ## Shifted operands -/

example : (shifted .LSL 1 X1).read (X1.write 1 S₀) = 1 <<< 1 := by rfl
example : X1.read ((shifted .LSL 1 X1).write 1 S₀) = 1#64 := by rfl

example : (shifted .LSR 63 X1).read (X1.write (1 <<< 63) S₀) = 1 := by rfl
example : X1.read ((shifted .LSL 1 X1).write 1 S₀) = 1#64 := by rfl

example : (shifted .ASR 63 X1).read (X1.write (1 <<< 63) S₀)
          = .allOnes 64 := by rfl
example : X1.read ((shifted .ASR 1 X1).write 2 S₀) = 2#64 := by rfl

example : (shifted .ROR 1 X1).read (X1.write 1 S₀) = (1 <<< 63) := by rfl
example : X1.read ((shifted .ROR 1 X1).write 2 S₀) = 2#64 := by rfl

/-! ## Extended operands -/

example : (extended .UXTB X1).read S₁ = 255#32 := by rfl
example : (extended .UXTH X1).read S₁ = .allOnes 16 := by rfl
example : (extended .UXTW X1).read S₁
          = (BitVec.allOnes 32).zeroExtend 64 := by rfl
example : (extended .UXTX X1).read S₁
          = (BitVec.allOnes 64).zeroExtend 128 := by rfl
example : ((extended .SXTB X1).read (X1.write (-127) S₁) : BitVec 32)
          = BitVec.ofInt 32 (-127) := by rfl

example : ((extended .SXTB X1).read
            (X1.write (1 <<< 7) S₀) : BitVec 64).toInt
          = (1 <<< 7 : BitVec 8).toInt := by rfl
example : ((extended .SXTH X1).read
            (X1.write (1 <<< 15) S₀) : BitVec 64).toInt
          = (1 <<< 15 : BitVec 16).toInt := by rfl
example : ((extended .SXTW X1).read
            (X1.write (1 <<< 31) S₀) : BitVec 64).toInt
          = (1 <<< 31 : BitVec 32).toInt := by rfl
example : ((extended .SXTX X1).read
            (X1.write (1 <<< 63) S₀) : BitVec 128).toInt
          = (1 <<< 63 : BitVec 64).toInt := by rfl

/-! ## Main SIMD registers -/

example : ((QREG 0).read $ (DREG 0).write (.allOnes 64) S₀)
          = (BitVec.allOnes 64).zeroExtend 128 := by rfl

example : ((QREG 0).read $ (SREG 0).write (.allOnes 32) S₀)
          = (BitVec.allOnes 32).zeroExtend 128 := by rfl

example : ((QREG 0).read $ (HREG 0).write (.allOnes 16) S₀)
          = (BitVec.allOnes 16).zeroExtend 128 := by rfl

example : ((QREG 0).read $ (BREG 0).write (.allOnes 8) S₀)
          = (BitVec.allOnes 8).zeroExtend 128 := by rfl

example : Q0.read S₀  = 0#128 := by rfl
example : Q1.read S₀  = 0#128 := by rfl
example : Q2.read S₀  = 0#128 := by rfl
example : Q3.read S₀  = 0#128 := by rfl
example : Q4.read S₀  = 0#128 := by rfl
example : Q5.read S₀  = 0#128 := by rfl
example : Q6.read S₀  = 0#128 := by rfl
example : Q7.read S₀  = 0#128 := by rfl
example : Q8.read S₀  = 0#128 := by rfl
example : Q9.read S₀  = 0#128 := by rfl
example : Q10.read S₀ = 0#128 := by rfl
example : Q11.read S₀ = 0#128 := by rfl
example : Q12.read S₀ = 0#128 := by rfl
example : Q13.read S₀ = 0#128 := by rfl
example : Q14.read S₀ = 0#128 := by rfl
example : Q15.read S₀ = 0#128 := by rfl
example : Q16.read S₀ = 0#128 := by rfl
example : Q17.read S₀ = 0#128 := by rfl
example : Q18.read S₀ = 0#128 := by rfl
example : Q19.read S₀ = 0#128 := by rfl
example : Q20.read S₀ = 0#128 := by rfl
example : Q21.read S₀ = 0#128 := by rfl
example : Q22.read S₀ = 0#128 := by rfl
example : Q23.read S₀ = 0#128 := by rfl
example : Q24.read S₀ = 0#128 := by rfl
example : Q25.read S₀ = 0#128 := by rfl
example : Q26.read S₀ = 0#128 := by rfl
example : Q27.read S₀ = 0#128 := by rfl
example : Q28.read S₀ = 0#128 := by rfl
example : Q29.read S₀ = 0#128 := by rfl
example : Q30.read S₀ = 0#128 := by rfl
example : Q31.read S₀ = 0#128 := by rfl

example : Q0.read S₁  = .allOnes 128 := by rfl
example : Q1.read S₁  = .allOnes 128 := by rfl
example : Q2.read S₁  = .allOnes 128 := by rfl
example : Q3.read S₁  = .allOnes 128 := by rfl
example : Q4.read S₁  = .allOnes 128 := by rfl
example : Q5.read S₁  = .allOnes 128 := by rfl
example : Q6.read S₁  = .allOnes 128 := by rfl
example : Q7.read S₁  = .allOnes 128 := by rfl
example : Q8.read S₁  = .allOnes 128 := by rfl
example : Q9.read S₁  = .allOnes 128 := by rfl
example : Q10.read S₁ = .allOnes 128 := by rfl
example : Q11.read S₁ = .allOnes 128 := by rfl
example : Q12.read S₁ = .allOnes 128 := by rfl
example : Q13.read S₁ = .allOnes 128 := by rfl
example : Q14.read S₁ = .allOnes 128 := by rfl
example : Q15.read S₁ = .allOnes 128 := by rfl
example : Q16.read S₁ = .allOnes 128 := by rfl
example : Q17.read S₁ = .allOnes 128 := by rfl
example : Q18.read S₁ = .allOnes 128 := by rfl
example : Q19.read S₁ = .allOnes 128 := by rfl
example : Q20.read S₁ = .allOnes 128 := by rfl
example : Q21.read S₁ = .allOnes 128 := by rfl
example : Q22.read S₁ = .allOnes 128 := by rfl
example : Q23.read S₁ = .allOnes 128 := by rfl
example : Q24.read S₁ = .allOnes 128 := by rfl
example : Q25.read S₁ = .allOnes 128 := by rfl
example : Q26.read S₁ = .allOnes 128 := by rfl
example : Q27.read S₁ = .allOnes 128 := by rfl
example : Q28.read S₁ = .allOnes 128 := by rfl
example : Q29.read S₁ = .allOnes 128 := by rfl
example : Q30.read S₁ = .allOnes 128 := by rfl
example : Q31.read S₁ = .allOnes 128 := by rfl

example : (Q0.write 1 S₀)._simdregisters 0 = 1 := by rfl
example : (Q1.write 1 S₀)._simdregisters 1 = 1 := by rfl
example : (Q2.write 1 S₀)._simdregisters 2 = 1 := by rfl
example : (Q3.write 1 S₀)._simdregisters 3 = 1 := by rfl
example : (Q4.write 1 S₀)._simdregisters 4 = 1 := by rfl
example : (Q5.write 1 S₀)._simdregisters 5 = 1 := by rfl
example : (Q6.write 1 S₀)._simdregisters 6 = 1 := by rfl
example : (Q7.write 1 S₀)._simdregisters 7 = 1 := by rfl
example : (Q8.write 1 S₀)._simdregisters 8 = 1 := by rfl
example : (Q9.write 1 S₀)._simdregisters 9 = 1 := by rfl
example : (Q10.write 1 S₀)._simdregisters 10 = 1 := by rfl
example : (Q11.write 1 S₀)._simdregisters 11 = 1 := by rfl
example : (Q12.write 1 S₀)._simdregisters 12 = 1 := by rfl
example : (Q13.write 1 S₀)._simdregisters 13 = 1 := by rfl
example : (Q14.write 1 S₀)._simdregisters 14 = 1 := by rfl
example : (Q15.write 1 S₀)._simdregisters 15 = 1 := by rfl
example : (Q16.write 1 S₀)._simdregisters 16 = 1 := by rfl
example : (Q17.write 1 S₀)._simdregisters 17 = 1 := by rfl
example : (Q18.write 1 S₀)._simdregisters 18 = 1 := by rfl
example : (Q19.write 1 S₀)._simdregisters 19 = 1 := by rfl
example : (Q20.write 1 S₀)._simdregisters 20 = 1 := by rfl
example : (Q21.write 1 S₀)._simdregisters 21 = 1 := by rfl
example : (Q22.write 1 S₀)._simdregisters 22 = 1 := by rfl
example : (Q23.write 1 S₀)._simdregisters 23 = 1 := by rfl
example : (Q24.write 1 S₀)._simdregisters 24 = 1 := by rfl
example : (Q25.write 1 S₀)._simdregisters 25 = 1 := by rfl
example : (Q26.write 1 S₀)._simdregisters 26 = 1 := by rfl
example : (Q27.write 1 S₀)._simdregisters 27 = 1 := by rfl
example : (Q28.write 1 S₀)._simdregisters 28 = 1 := by rfl
example : (Q29.write 1 S₀)._simdregisters 29 = 1 := by rfl
example : (Q30.write 1 S₀)._simdregisters 30 = 1 := by rfl
example : (Q31.write 1 S₀)._simdregisters 31 = 1 := by rfl

example : (Q0.write 0 S₁)._simdregisters 0 = 0 := by rfl
example : (Q1.write 0 S₁)._simdregisters 1 = 0 := by rfl
example : (Q2.write 0 S₁)._simdregisters 2 = 0 := by rfl
example : (Q3.write 0 S₁)._simdregisters 3 = 0 := by rfl
example : (Q4.write 0 S₁)._simdregisters 4 = 0 := by rfl
example : (Q5.write 0 S₁)._simdregisters 5 = 0 := by rfl
example : (Q6.write 0 S₁)._simdregisters 6 = 0 := by rfl
example : (Q7.write 0 S₁)._simdregisters 7 = 0 := by rfl
example : (Q8.write 0 S₁)._simdregisters 8 = 0 := by rfl
example : (Q9.write 0 S₁)._simdregisters 9 = 0 := by rfl
example : (Q10.write 0 S₁)._simdregisters 10 = 0 := by rfl
example : (Q11.write 0 S₁)._simdregisters 11 = 0 := by rfl
example : (Q12.write 0 S₁)._simdregisters 12 = 0 := by rfl
example : (Q13.write 0 S₁)._simdregisters 13 = 0 := by rfl
example : (Q14.write 0 S₁)._simdregisters 14 = 0 := by rfl
example : (Q15.write 0 S₁)._simdregisters 15 = 0 := by rfl
example : (Q16.write 0 S₁)._simdregisters 16 = 0 := by rfl
example : (Q17.write 0 S₁)._simdregisters 17 = 0 := by rfl
example : (Q18.write 0 S₁)._simdregisters 18 = 0 := by rfl
example : (Q19.write 0 S₁)._simdregisters 19 = 0 := by rfl
example : (Q20.write 0 S₁)._simdregisters 20 = 0 := by rfl
example : (Q21.write 0 S₁)._simdregisters 21 = 0 := by rfl
example : (Q22.write 0 S₁)._simdregisters 22 = 0 := by rfl
example : (Q23.write 0 S₁)._simdregisters 23 = 0 := by rfl
example : (Q24.write 0 S₁)._simdregisters 24 = 0 := by rfl
example : (Q25.write 0 S₁)._simdregisters 25 = 0 := by rfl
example : (Q26.write 0 S₁)._simdregisters 26 = 0 := by rfl
example : (Q27.write 0 S₁)._simdregisters 27 = 0 := by rfl
example : (Q28.write 0 S₁)._simdregisters 28 = 0 := by rfl
example : (Q29.write 0 S₁)._simdregisters 29 = 0 := by rfl
example : (Q30.write 0 S₁)._simdregisters 30 = 0 := by rfl
example : (Q31.write 0 S₁)._simdregisters 31 = 0 := by rfl

example : (QREG 31).read ((QREG 31).write 1 S₀) = 1 := by rfl
example : (QREG 31).read ((QREG 31).write 8 S₁) = 8 := by rfl

/-! ## 32-bit versions of the main SIMD registers -/

example : D0.read S₀  = 0#64 := by rfl
example : D1.read S₀  = 0#64 := by rfl
example : D2.read S₀  = 0#64 := by rfl
example : D3.read S₀  = 0#64 := by rfl
example : D4.read S₀  = 0#64 := by rfl
example : D5.read S₀  = 0#64 := by rfl
example : D6.read S₀  = 0#64 := by rfl
example : D7.read S₀  = 0#64 := by rfl
example : D8.read S₀  = 0#64 := by rfl
example : D9.read S₀  = 0#64 := by rfl
example : D10.read S₀ = 0#64 := by rfl
example : D11.read S₀ = 0#64 := by rfl
example : D12.read S₀ = 0#64 := by rfl
example : D13.read S₀ = 0#64 := by rfl
example : D14.read S₀ = 0#64 := by rfl
example : D15.read S₀ = 0#64 := by rfl
example : D16.read S₀ = 0#64 := by rfl
example : D17.read S₀ = 0#64 := by rfl
example : D18.read S₀ = 0#64 := by rfl
example : D19.read S₀ = 0#64 := by rfl
example : D20.read S₀ = 0#64 := by rfl
example : D21.read S₀ = 0#64 := by rfl
example : D22.read S₀ = 0#64 := by rfl
example : D23.read S₀ = 0#64 := by rfl
example : D24.read S₀ = 0#64 := by rfl
example : D25.read S₀ = 0#64 := by rfl
example : D26.read S₀ = 0#64 := by rfl
example : D27.read S₀ = 0#64 := by rfl
example : D28.read S₀ = 0#64 := by rfl
example : D29.read S₀ = 0#64 := by rfl
example : D30.read S₀ = 0#64 := by rfl
example : D31.read S₀ = 0#64 := by rfl

example : D0.read S₁  = .allOnes 64 := by rfl
example : D1.read S₁  = .allOnes 64 := by rfl
example : D2.read S₁  = .allOnes 64 := by rfl
example : D3.read S₁  = .allOnes 64 := by rfl
example : D4.read S₁  = .allOnes 64 := by rfl
example : D5.read S₁  = .allOnes 64 := by rfl
example : D6.read S₁  = .allOnes 64 := by rfl
example : D7.read S₁  = .allOnes 64 := by rfl
example : D8.read S₁  = .allOnes 64 := by rfl
example : D9.read S₁  = .allOnes 64 := by rfl
example : D10.read S₁ = .allOnes 64 := by rfl
example : D11.read S₁ = .allOnes 64 := by rfl
example : D12.read S₁ = .allOnes 64 := by rfl
example : D13.read S₁ = .allOnes 64 := by rfl
example : D14.read S₁ = .allOnes 64 := by rfl
example : D15.read S₁ = .allOnes 64 := by rfl
example : D16.read S₁ = .allOnes 64 := by rfl
example : D17.read S₁ = .allOnes 64 := by rfl
example : D18.read S₁ = .allOnes 64 := by rfl
example : D19.read S₁ = .allOnes 64 := by rfl
example : D20.read S₁ = .allOnes 64 := by rfl
example : D21.read S₁ = .allOnes 64 := by rfl
example : D22.read S₁ = .allOnes 64 := by rfl
example : D23.read S₁ = .allOnes 64 := by rfl
example : D24.read S₁ = .allOnes 64 := by rfl
example : D25.read S₁ = .allOnes 64 := by rfl
example : D26.read S₁ = .allOnes 64 := by rfl
example : D27.read S₁ = .allOnes 64 := by rfl
example : D28.read S₁ = .allOnes 64 := by rfl
example : D29.read S₁ = .allOnes 64 := by rfl
example : D30.read S₁ = .allOnes 64 := by rfl
example : D31.read S₁ = .allOnes 64 := by rfl

example : (D0.write 1 S₀)._simdregisters 0 = 1 := by rfl
example : (D1.write 1 S₀)._simdregisters 1 = 1 := by rfl
example : (D2.write 1 S₀)._simdregisters 2 = 1 := by rfl
example : (D3.write 1 S₀)._simdregisters 3 = 1 := by rfl
example : (D4.write 1 S₀)._simdregisters 4 = 1 := by rfl
example : (D5.write 1 S₀)._simdregisters 5 = 1 := by rfl
example : (D6.write 1 S₀)._simdregisters 6 = 1 := by rfl
example : (D7.write 1 S₀)._simdregisters 7 = 1 := by rfl
example : (D8.write 1 S₀)._simdregisters 8 = 1 := by rfl
example : (D9.write 1 S₀)._simdregisters 9 = 1 := by rfl
example : (D10.write 1 S₀)._simdregisters 10 = 1 := by rfl
example : (D11.write 1 S₀)._simdregisters 11 = 1 := by rfl
example : (D12.write 1 S₀)._simdregisters 12 = 1 := by rfl
example : (D13.write 1 S₀)._simdregisters 13 = 1 := by rfl
example : (D14.write 1 S₀)._simdregisters 14 = 1 := by rfl
example : (D15.write 1 S₀)._simdregisters 15 = 1 := by rfl
example : (D16.write 1 S₀)._simdregisters 16 = 1 := by rfl
example : (D17.write 1 S₀)._simdregisters 17 = 1 := by rfl
example : (D18.write 1 S₀)._simdregisters 18 = 1 := by rfl
example : (D19.write 1 S₀)._simdregisters 19 = 1 := by rfl
example : (D20.write 1 S₀)._simdregisters 20 = 1 := by rfl
example : (D21.write 1 S₀)._simdregisters 21 = 1 := by rfl
example : (D22.write 1 S₀)._simdregisters 22 = 1 := by rfl
example : (D23.write 1 S₀)._simdregisters 23 = 1 := by rfl
example : (D24.write 1 S₀)._simdregisters 24 = 1 := by rfl
example : (D25.write 1 S₀)._simdregisters 25 = 1 := by rfl
example : (D26.write 1 S₀)._simdregisters 26 = 1 := by rfl
example : (D27.write 1 S₀)._simdregisters 27 = 1 := by rfl
example : (D28.write 1 S₀)._simdregisters 28 = 1 := by rfl
example : (D29.write 1 S₀)._simdregisters 29 = 1 := by rfl
example : (D30.write 1 S₀)._simdregisters 30 = 1 := by rfl
example : (D31.write 1 S₀)._simdregisters 31 = 1 := by rfl

example : (D0.write 0 S₁)._simdregisters 0 = 0 := by rfl
example : (D1.write 0 S₁)._simdregisters 1 = 0 := by rfl
example : (D2.write 0 S₁)._simdregisters 2 = 0 := by rfl
example : (D3.write 0 S₁)._simdregisters 3 = 0 := by rfl
example : (D4.write 0 S₁)._simdregisters 4 = 0 := by rfl
example : (D5.write 0 S₁)._simdregisters 5 = 0 := by rfl
example : (D6.write 0 S₁)._simdregisters 6 = 0 := by rfl
example : (D7.write 0 S₁)._simdregisters 7 = 0 := by rfl
example : (D8.write 0 S₁)._simdregisters 8 = 0 := by rfl
example : (D9.write 0 S₁)._simdregisters 9 = 0 := by rfl
example : (D10.write 0 S₁)._simdregisters 10 = 0 := by rfl
example : (D11.write 0 S₁)._simdregisters 11 = 0 := by rfl
example : (D12.write 0 S₁)._simdregisters 12 = 0 := by rfl
example : (D13.write 0 S₁)._simdregisters 13 = 0 := by rfl
example : (D14.write 0 S₁)._simdregisters 14 = 0 := by rfl
example : (D15.write 0 S₁)._simdregisters 15 = 0 := by rfl
example : (D16.write 0 S₁)._simdregisters 16 = 0 := by rfl
example : (D17.write 0 S₁)._simdregisters 17 = 0 := by rfl
example : (D18.write 0 S₁)._simdregisters 18 = 0 := by rfl
example : (D19.write 0 S₁)._simdregisters 19 = 0 := by rfl
example : (D20.write 0 S₁)._simdregisters 20 = 0 := by rfl
example : (D21.write 0 S₁)._simdregisters 21 = 0 := by rfl
example : (D22.write 0 S₁)._simdregisters 22 = 0 := by rfl
example : (D23.write 0 S₁)._simdregisters 23 = 0 := by rfl
example : (D24.write 0 S₁)._simdregisters 24 = 0 := by rfl
example : (D25.write 0 S₁)._simdregisters 25 = 0 := by rfl
example : (D26.write 0 S₁)._simdregisters 26 = 0 := by rfl
example : (D27.write 0 S₁)._simdregisters 27 = 0 := by rfl
example : (D28.write 0 S₁)._simdregisters 28 = 0 := by rfl
example : (D29.write 0 S₁)._simdregisters 29 = 0 := by rfl
example : (D30.write 0 S₁)._simdregisters 30 = 0 := by rfl
example : (D31.write 0 S₁)._simdregisters 31 = 0 := by rfl

example : (DREG 31).read ((DREG 31).write 1 S₀) = 1 := by rfl
example : (DREG 31).read ((DREG 31).write 8 S₁) = 8 := by rfl

/-! ## SIMD register lanes -/

example : ((Q0 :> LANE_B 0).read (Q0.write 0x0a01 S₀))
          = 0x01010101010101010101010101010101 := by rfl
example : ((Q0 :> LANE_B 1).read (Q0.write 0xa001 S₀))
          = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := by rfl

example : ((Q0 :> LANE_H 0).read (Q0.write 0xffff0a01 S₀))
          = 0x0a010a010a010a010a010a010a010a01 := by rfl
example : ((Q0 :> LANE_H 1).read (Q0.write 0xffff0a01 S₀))
          = 0xffffffffffffffffffffffffffffffff := by rfl

example : ((Q0 :> LANE_S 0).read (Q0.write 0xbb01ffff0a01 S₀))
          = 0xffff0a01ffff0a01ffff0a01ffff0a01 := by rfl
example : ((Q0 :> LANE_S 1).read (Q0.write 0xbb01ffff0a01 S₀))
          = 0x0000bb010000bb010000bb010000bb01 := by rfl

example : ((Q0 :> LANE_D 0).read (Q0.write 0xff00bb01ffff0a01 S₀))
          = 0xff00bb01ffff0a01ff00bb01ffff0a01 := by rfl
example : ((Q0 :> LANE_D 1).read (Q0.write (0xff00bb01ffff0a01 <<< 64) S₀))
          = 0xff00bb01ffff0a01ff00bb01ffff0a01 := by rfl
