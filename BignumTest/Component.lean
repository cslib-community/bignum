/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/

import Bignum.Component.Basic
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

/-- info: X : Component A Nat     -/  #guard_msgs in #check X
/-- info: Y : Component A Bool    -/  #guard_msgs in #check Y
/-- info: F : Component B A       -/  #guard_msgs in #check F
/-- info: Z : Component B Nat     -/  #guard_msgs in #check Z
/-- info: F:>X : Component B Nat  -/  #guard_msgs in #check F:>X
/-- info: F:>Y : Component B Bool -/  #guard_msgs in #check F:>Y

def aa : A := ⟨1, false⟩
def bb : B := ⟨aa, 2⟩
example : X.read aa = aa.x := by rfl
example : Y.read aa = aa.y := by rfl
example : X.write 44 aa = ⟨44, false⟩ := by rfl
example : (F :> X).read bb = 1 := by rfl
example : (F :> X).write 99 bb = {f := {x := 99, y := false}, z := 2} := by rfl

/-! ## entirety -/

example : (X :> .entirety).read aa = aa.x := by rfl
example : (.entirety :> X).read aa = aa.x := by rfl
example : ((X :> .entirety).write 42) aa = {aa with x := 42} := by rfl
example : ((.entirety :> X).write 42) aa = {aa with x := 42} := by rfl

/-! ## rvalue -/

example : (.rvalue 42 : Component Bool Nat).read true = 42 := by rfl
example : ((.rvalue 42 : Component Bool Nat).write 33 false) = false := by rfl

/-! ## element -/

structure C where
  g : Nat → Nat

def G := Component.mk (λ c : C ↦ c.g) (λ g c ↦ {c with g := g})
def G13 := (G :> .element 13)
def cc : C := ⟨λ _ ↦ 0⟩

example : G.read cc 42 = 0 := by rfl
example : G13.read cc = 0 := by rfl
example :  G13.read (G13.write 11 cc) = 11 := by rfl

/-! ## through -/

def Xr := X :> .through Nat.succ id
def Xw := X :> .through id Nat.pred

example : X.read aa = 1 := by rfl
example : Xr.read aa = 2 := by rfl
example : Xr.read (Xr.write 8 aa) = 9 := by rfl

example : X.write 2 aa = {aa with x := 2} := by rfl
example : (Xw.write 8 aa) = {aa with x := 7} := by rfl
example : X.read (Xw.write 8 aa) = 7 := by rfl
example : Xr.read (Xw.write 8 aa) = 8 := by rfl
