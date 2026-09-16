/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/

import Bignum.BitVec

open BitVec

example : setLsb (0b0000#8) 3 true == 8#8 := by rfl
example : setLsb (0b1010#8) 1 false == 8#8 := by rfl
