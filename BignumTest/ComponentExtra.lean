/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/

import Bignum.Component.Extra

open Bignum

-- bitelement

namespace bitelementNS
def bv : BitVec 8 := 0b01001011#8
example : (Component.bitelement 0).read bv = true := by rfl
example : (Component.bitelement 1).read bv = true := by rfl
example : (Component.bitelement 2).read bv = false := by rfl
example : (Component.bitelement 3).read bv = true := by rfl
example : (Component.bitelement 3).write false bv = 0b01000011#8 := by rfl
namespace bitelementNS

-- subword

namespace subwordNS
def bv : BitVec 8 := 0b01001011#8
example : (Component.subword 0 3).read bv == 0b11#3 := by rfl
example : (Component.subword 4 1).read bv == 0#1 := by rfl
example : (Component.subword 0 0).read bv == 0#0 := by rfl
example : (Component.subword 6 3).read bv == 1#3 := by rfl
example : (Component.subword 7 3).read bv == 0#3 := by rfl
example : (Component.subword 100 2).read bv == 0#2 := by rfl
example : (Component.subword 0 3).write 0 bv == 0b01001000#8 := by rfl
example : (Component.subword 1 3).write 0b101 bv == 0b01001011#8 := by rfl
example : (Component.subword 6 4).write 0xf bv == 0b11001011#8 := by rfl
end subwordNS
