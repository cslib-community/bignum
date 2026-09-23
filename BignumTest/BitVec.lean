/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/

import Bignum.BitVec
open BitVec

/-! # Unit test for bitvector operations -/

/-! ## toBitString -/

example : (0#0).toBitString = "" := by rfl
example : (1101#4).toBitString = "1101" := by rfl

/-! ## setLsb -/

example : setLsb (0b0000#8) 3 true == 8#8 := by rfl
example : setLsb (0b1010#8) 1 false == 8#8 := by rfl

/-! ## extractLsb' -/

namespace extractLsb'_NS
def bv := 0b10010110#8
example : bv.extractLsb' 3 2 = 2#2 := by rfl
example : bv.extractLsb' 3 2 = bv.extractLsb'Alt 3 2 := by rfl
end extractLsb'_NS

/-! ## overwriteLsb' -/

namespace overwriteLsb'_NS
def bv := 0b10010110#8
example : bv.overwriteLsb' 3 2 0b01#2 = 0b10001110#8 := by rfl
example : bv.overwriteLsb' 3 2 0b01#2 = bv.overwriteLsb'Alt 3 2 0b01#2 := by rfl
example : bv.overwriteLsb' 0 16 0xffff = 0xffff#8 := by rfl
example : bv.overwriteLsb' 0 16 0xffff = bv.overwriteLsb'Alt 0 16 0xffff := by rfl
example : bv.overwriteLsb' 7 16 0x0#16 = 0b00010110#8 := by rfl
end overwriteLsb'_NS
