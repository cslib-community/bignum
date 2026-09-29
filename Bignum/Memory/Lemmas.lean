/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/

module

public import Bignum.Memory.Basic

@[expose] public section

/-! # Lemmas about memory operations -/

set_option autoImplicit false

namespace Bignum

/-! ## Byte list -/

namespace ByteList

theorem length_ofNatLE (len n : Nat) :
    (ofNatLE len n).length = len := by
  induction len generalizing n with
  | zero => rfl
  | succ len' ih => rw [ofNatLE, List.length_cons, ih]

theorem length_ofIntLE (len : Nat) (n : Int) :
    (ofIntLE len n).length = len := by
  rw [ofIntLE, length_ofNatLE]

theorem toNatLE_bound (l : ByteList) : l.toNatLE < (256 ^ (l.length)) := by
  unfold toNatLE
  induction l with
  | nil => simp
  | cons b bs ih =>
    sorry

end ByteList
end Bignum
