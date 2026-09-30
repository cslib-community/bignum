/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

import Bignum.Memory
open Bignum

/-! # Unit test for memory operations -/

/-! ## Byte list -/

def bs : ByteList := [0xef, 0xcd, 0xab, 0x00]
example : ByteList.ofNatLE 4 bs.toNatLE = bs := by rfl
example : ByteList.ofNatLE 6 bs.toNatLE = bs ++ [0, 0] := by rfl
example : ByteList.ofIntLE 2 (-129) = [0x7f, 0xff] := by rfl
example : ByteList.ofIntLE 1 (-129) = [0x7f] := by rfl
