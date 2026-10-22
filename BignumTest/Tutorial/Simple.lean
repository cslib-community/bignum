/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

import Bignum
open Bignum Bignum.Arm

/-! # Proving a simple property about `simple.S` -/

def simple : ByteList :=
  [0x22, 0x00, 0x00, 0x8b,      -- add x2, x1, x0
   0x42, 0x00, 0x01, 0xcb]      -- sub x2, x2, x1

theorem simple_spec : forall pc a b,
    arm.Ensures
    (fun s ↦                    -- precondition
      s.AlignedBytesLoaded pc simple ∧
      s.read PC = pc ∧
      s.read X0 = a ∧
      s.read X1 = b)
    (fun s ↦                    -- postcondition
      s.read PC = pc + 8 ∧
      s.read X2 = a)
    (MayChange [PC, X2]) := by  -- frame
  sorry
