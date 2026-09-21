/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/

import Bignum.ComponentExtra

open Bignum

section bitelement
def bv : BitVec 8 := 0b01001011#8
example : (Component.bitelement 0).read bv = true := by rfl
example : (Component.bitelement 1).read bv = true := by rfl
example : (Component.bitelement 2).read bv = false := by rfl
example : (Component.bitelement 3).read bv = true := by rfl
def bv' := (Component.bitelement 3).write false bv
example : bv' = 0b01000011#8 := by rfl
end bitelement
