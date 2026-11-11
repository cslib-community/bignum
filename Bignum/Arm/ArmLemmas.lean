/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Arm.Arm
public import Bignum.Arm.StateLemmas

@[expose] public section

/-! # Theorems about ARM semantics -/

namespace Bignum.Arm
namespace State

variable (s : State) (addr : BitVec 64) (instr : Rel State State)

/-! ## Instruction decoding -/

theorem decode_eq_none_iff : s.decode addr = none ↔ ¬ 4 ∣ addr.toNat ∨
    Decode.decode (s.fetch addr) = none := by
  grind [decode]

theorem decode_eq_some_iff (data : BitVec 32) (instr : Rel State State) :
    s.decode addr = some (data, instr) ↔
    s.AlignedBytesLoaded addr (.ofBitVecLE 4 data) ∧
    Decode.decode (s.fetch addr) = some instr := by
  constructor
  · simp [decode]; intro h4 h
    constructor <;> split at h <;> injections <;> try contradiction
    · refine ⟨h4, ?_⟩; subst data; unfold Memory.BytesLoadedLE
      rw [ByteList.length_ofBitVecLE, ← read_bytes, fetch]
      exact (ByteList.ofBitVecLE_toBitVecLE_of_length_eq _
        (length_read_bytes s addr 4) _).symm
    · subst instr; assumption
  · intro ⟨ha, hd⟩; simp [decode, ha.aligned, hd]
    have h : s.read (bytes addr 4) = ByteList.ofBitVecLE 4 data := by
      rw [read_bytes]
      exact (Memory.BytesLoadedLE_ofBitVecLE_iff _ _ _ _).mp ha.bytesLoadedLE
    exact ByteList.ofBitVecLE_inj _ _ rfl
      ((ByteList.ofBitVecLE_toBitVecLE_of_length_eq _
        (length_read_bytes s addr 4) (by rw [length_read_bytes])).trans h)

theorem decode_def : s.Decode addr instr ↔ ∃ data,
    s.AlignedBytesLoaded addr (.ofBitVecLE 4 data) ∧
    s.decode addr = some (data, instr) := by
  unfold Decode; constructor
  · simp [decode_eq_some_iff]
  · intro ⟨data, _, _⟩; exists data

theorem decode_cons (bs bs' : ByteList) (data : BitVec 32)
    (ha : s.AlignedBytesLoaded addr bs)
    (hpop : bs.popBitVecLE 4 = some (data, bs'))
    (hdec : s.decode addr = some (data, instr)) :
    s.Decode addr instr ∧ s.AlignedBytesLoaded (addr + 4#64) bs' := by
  constructor
  · apply (s.decode_def _ _).mpr; exists data; constructor
    · exact ((s.decode_eq_some_iff _ _ _).mp hdec).1
    · exact hdec
  · rcases (ByteList.popBitVecLE_eq_some_iff _ _ _ _).mp hpop with ⟨hn, -, rfl⟩
    have h4 : (bs.take 4).length = 4 := by
      rw [List.length_take, Nat.min_eq_left hn]
    have := (Memory.AlignedBytesLoadedLE_append' (s.read memory) addr
      (bs.take 4) (bs.drop 4) (by rw [h4]; exact Nat.dvd_refl 4)).mp
      (by rw [List.take_append_drop]; exact ha)
    rw [h4] at this
    exact this.2

end State
end Bignum.Arm
