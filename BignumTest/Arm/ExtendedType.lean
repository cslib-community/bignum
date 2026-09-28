/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/
module

import Bignum.Arm

open Bignum.Arm

example : ExtendedType.extend .UXTB 0x101#16 = 1#16 := by rfl
example : ExtendedType.extend .UXTH 0x10001#32 = 1#32 := by rfl
example : ExtendedType.extend .UXTW 0x100000001#64 = 1#64 := by rfl
example : ExtendedType.extend .UXTX 0x10000000000000001#128 = 1#128 := by rfl

example : ((ExtendedType.extend .SXTB
      ((1 <<< 7) : BitVec 64)) : BitVec 64).toInt
    = ((1 <<< 7) : BitVec 8).toInt := by rfl

example : ((ExtendedType.extend .SXTH
      ((1 <<< 15) : BitVec 64)) : BitVec 64).toInt
    = ((1 <<< 15) : BitVec 16).toInt := by rfl

example : ((ExtendedType.extend .SXTW
      ((1 <<< 31) : BitVec 64)) : BitVec 64).toInt
    = ((1 <<< 31) : BitVec 32).toInt := by rfl

example : ((ExtendedType.extend .SXTX
      ((1 <<< 63) : BitVec 128)) : BitVec 128).toInt
    = ((1 <<< 63) : BitVec 64).toInt := by rfl
