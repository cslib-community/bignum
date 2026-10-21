/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

import Bignum
open Bignum

/-! # Proving a simple property about `simple.S` -/

def simple : ByteList :=
  [0x22, 0x00, 0x00, 0x8b,      -- add x2, x1, x0
   0x42, 0x00, 0x01, 0xcb]      -- sub x2, x2, x1
