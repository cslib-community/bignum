/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Relation
public import Bignum.Component.Basic

@[expose] public section

/-! # Relational model of programs and Hoare-type rules -/

namespace Bignum
namespace Component

universe u v

variable {α : Type u} {β : Type v}

/--
Assignment of component as a functional relation.
-/
def Assign (cp : Component α β) (b : β) : α → α → Prop :=
  fun a a' ↦ cp.write b a = a'

/--
Non-deterministic assignment of component.
-/
def Assigns (cp : Component α β) : α → α → Prop :=
  fun a a' ↦ ∃ b, (cp.Assign b) a a'

end Component

@[inherit_doc] scoped infixr:70 " ≔ " => Component.Assign

end Bignum
