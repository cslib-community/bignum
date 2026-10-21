/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

import Bignum.Component
open Bignum

/-! # Unit tests for components -/

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

/-- info: X : Component A Nat -/
#guard_msgs in
#check X

/-- info: Y : Component A Bool -/
#guard_msgs in
#check Y

/-- info: F : Component B A -/
#guard_msgs in
#check F

/-- info: Z : Component B Nat -/
#guard_msgs in
#check Z

def aa : A := ⟨1, false⟩
def bb : B := ⟨aa, 2⟩
example : X.read aa = aa.x := by rfl
example : Y.read aa = aa.y := by rfl
example : X.write 44 aa = ⟨44, false⟩ := by rfl

/-! ## compose -/

/-- info: F :> X : Component B Nat -/
#guard_msgs in
#check F :> X

/-- info: F :> Y : Component B Bool -/
#guard_msgs in
#check F :> Y

example : (F :> X).read bb = 1 := by rfl
example : (F :> X).write 99 bb = {f := {x := 99, y := false}, z := 2} := by
  rfl

/-! ## entirety -/

example : (X :> .entirety).read aa = aa.x := by rfl
example : (.entirety :> X).read aa = aa.x := by rfl
example : ((X :> .entirety).write 42) aa = {aa with x := 42} := by rfl
example : ((.entirety :> X).write 42) aa = {aa with x := 42} := by rfl

/-- info: Component.instReadOverWriteEntirety -/
#guard_msgs in
#synth Component.entirety.ReadOverWrite

/-- info: Component.instWeakReadOverWriteEntirety -/
#guard_msgs in
#synth Component.entirety.WeakReadOverWrite

/-- info: Component.instWriteOverReadEntirety -/
#guard_msgs in
#synth Component.entirety.WriteOverRead

/-- info: Component.instWriteOverWriteEntirety -/
#guard_msgs in
#synth Component.entirety.WriteOverWrite

/-- info: { toReadOverWrite := Component.instReadOverWriteEntirety,
toWriteOverWrite := Component.instWriteOverWriteEntirety } -/
#guard_msgs in
#synth Component.entirety.Valid

/-- info: Component.instWeaklyValidOfValid Component.entirety -/
#guard_msgs in
#synth Component.entirety.WeaklyValid

/-- info: { toReadOverWrite := Component.instReadOverWriteEntirety,
toWriteOverWrite := Component.instWriteOverWriteEntirety,
  toWriteOverRead := Component.instWriteOverReadEntirety } -/
#guard_msgs in
#synth Component.entirety.StronglyValid

/-- info: Component.instExtensionallyValidOfStronglyValid
Component.entirety -/
#guard_msgs in
#synth Component.entirety.ExtensionallyValid

/-- info: Component.instReadOverWriteCompose Component.entirety
Component.entirety -/
#guard_msgs in
#synth (.entirety :> .entirety).ReadOverWrite

/-- info: Component.instWeakReadOverWriteOfReadOverWrite
(Component.entirety :> Component.entirety) -/
#guard_msgs in
#synth (.entirety :> .entirety).WeakReadOverWrite

/-- info: Component.instWriteOverReadCompose Component.entirety
Component.entirety -/
#guard_msgs in
#synth (.entirety :> .entirety).WriteOverRead

/-- info: Component.instWriteOverWriteComposeOfReadOverWrite
Component.entirety Component.entirety -/
#guard_msgs in
#synth (.entirety :> .entirety).WriteOverWrite

/-- info: Component.instValidCompose Component.entirety
Component.entirety -/
#guard_msgs in
#synth (.entirety :> .entirety).Valid

/-- info: Component.instWeaklyValidOfValid
(Component.entirety :> Component.entirety) -/
#guard_msgs in
#synth (.entirety :> .entirety).WeaklyValid

/-- info: Component.instStronglyValidCompose Component.entirety
Component.entirety -/
#guard_msgs in
#synth (.entirety :> .entirety).StronglyValid

/-- info: Component.instExtensionallyValidOfStronglyValid
(Component.entirety :> Component.entirety) -/
#guard_msgs in
#synth (.entirety :> .entirety).ExtensionallyValid

