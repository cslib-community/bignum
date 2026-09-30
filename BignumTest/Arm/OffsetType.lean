/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

import Bignum.Arm

open Bignum.Arm

example : (OffsetType.register X0).writesback = false := by rfl
example : (OffsetType.shiftreg X0 0).writesback = false := by rfl
example : (OffsetType.postreg X0).writesback = true := by rfl
example : (OffsetType.immediate 0).writesback = false := by rfl
example : (OffsetType.preimmediate 0).writesback = true := by rfl
example : (OffsetType.postimmediate 0).writesback = true := by rfl

example : OffsetType.no_offset = .immediate 0 := by rfl

def S₁ := State.allOnes

example : S₁.offset_address (.register X0) = .allOnes 64 := by rfl
example : S₁.offset_address (.shiftreg X0 5)
    = (BitVec.allOnes 64 <<< 5) := by rfl
example : S₁.offset_address (.postreg X0) = 0 := by rfl
example : S₁.offset_address (.immediate 8) = 8 := by rfl
example : S₁.offset_address (.preimmediate 8) = 8 := by rfl
example : S₁.offset_address (.postimmediate 8) = 0 := by rfl

example : S₁.offset_writeback (.register X0) = 0 := by rfl
example : S₁.offset_writeback (.shiftreg X0 5) = 0 := by rfl
example : S₁.offset_writeback (.postreg X0) = .allOnes 64 := by rfl
example : S₁.offset_writeback (.immediate 8) = 0 := by rfl
example : S₁.offset_writeback (.preimmediate 8) = 8 := by rfl
example : S₁.offset_writeback (.postimmediate 8) = 8 := by rfl
