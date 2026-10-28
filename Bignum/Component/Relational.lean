/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Relational
public import Bignum.Component.Basic

@[expose] public section

/-! # Relational model of programs and Hoare-type rules -/

namespace Bignum

universe u v

namespace Component

variable {α : Type u} {β : Type v}

/--
Assignment of component as a functional relation.
-/
def Assign (cp : Component α β) (b : β) : Relation α α :=
  fun a a' ↦ cp.write b a = a'

/--
Non-deterministic assignment of component.
-/
def Assigns (cp : Component α β) : Relation α α :=
  fun a a' ↦ ∃ b, (cp.Assign b) a a'

end Component

/--
Expresses "a step only (possibly) changes these components".
-/
def MayChange {α : Type u} {β : Type v} :
    List (Component α β) → Relation α α
  | [] => Eq
  | cp :: cps => cp.Assigns ,, MayChange cps

@[inherit_doc] scoped infixr:70 " ≔ " => Component.Assign

end Bignum
