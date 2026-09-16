/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/

import Bignum.Component

open Bignum.Component

structure A where
  x : Nat
  y : Bool

structure B where
  f : A
  z : Nat

def X := Component.mk (λ a : A ↦ a.x) (λ x a ↦ {a with x := x})
def Y := Component.mk (λ a : A ↦ a.y) (λ y a ↦ {a with y := y})
def F := Component.mk (λ b : B ↦ b.f) (λ f b ↦ {b with f := f})
def Z := Component.mk (λ b : B ↦ b.z) (λ z b ↦ {b with z := z})

#check (X : Component A Nat)
#check (Y : Component A Bool)
#check (F : Component B A)
#check (Z : Component B Nat)
#check (F :> X : Component B Nat)
#check (F :> Y : Component B Bool)

def aa : A := ⟨1, false⟩
def bb : B := ⟨aa, 2⟩

example : X.read aa = aa.x := by rfl
example : Y.read aa = aa.y := by rfl
example : X.write 44 aa = ⟨44, false⟩ := by rfl
example : (F :> X).read bb = 1 := by rfl
example : (F :> X).write 99 bb = {f := {x := 99, y := false}, z := 2} := by rfl
