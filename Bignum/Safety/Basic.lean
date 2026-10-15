/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

@[expose] public section

/-! # Constant-time and memory-safety properties -/

namespace Bignum

/--
Observable micro-architectural (uarch) event.
-/
inductive UArchEvent (w : Nat) where
  /-- `len` bytes were read from memory at offset `addr`. -/
  | EventLoad (addr : BitVec w) (len : Nat)
  /-- `len` bytes were written to memory at offset `addr`. -/
  | EventStore (addr : BitVec w) (len : Nat)
  /-- Execution jumped (PC-changed) from `src` to `dest`. -/
  | EventJump (src : BitVec w) (dest : BitVec w)

end Bignum
