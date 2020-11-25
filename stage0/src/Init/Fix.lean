/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.UInt
universe u

def bfix1 {α β : Type u} (base : α → β) (rec : (α → β) → α → β) : Nat → α → β
  | 0,   a => base a
  | n+1, a => rec (bfix1 base rec n) a

@[extern c inline "lean_fixpoint(#4, #5)"]
def fixCore1 {α β : Type u} (base : @& (α → β)) (rec : (α → β) → α → β) : α → β :=
  bfix1 base rec USize.size

@[inline] def fixCore {α β : Type u} (base : @& (α → β)) (rec : (α → β) → α → β) : α → β :=
  fixCore1 base rec

@[inline] def fix1 {α β : Type u} [Inhabited β] (rec : (α → β) → α → β) : α → β :=
  fixCore1 (fun _ => arbitrary) rec

@[inline] def fix {α β : Type u} [Inhabited β] (rec : (α → β) → α → β) : α → β :=
  fixCore1 (fun _ => arbitrary) rec

def bfix2 {α₁ α₂ β : Type u} (base : α₁ → α₂ → β) (rec : (α₁ → α₂ → β) → α₁ → α₂ → β) : Nat → α₁ → α₂ → β
  | 0,   a₁, a₂ => base a₁ a₂
  | n+1, a₁, a₂ => rec (bfix2 base rec n) a₁ a₂

@[extern c inline "lean_fixpoint2(#5, #6, #7)"]
def fixCore2 {α₁ α₂ β : Type u} (base : α₁ → α₂ → β) (rec : (α₁ → α₂ → β) → α₁ → α₂ → β) : α₁ → α₂ → β :=
  bfix2 base rec USize.size

@[inline] def fix2 {α₁ α₂ β : Type u} [Inhabited β] (rec : (α₁ → α₂ → β) → α₁ → α₂ → β) : α₁ → α₂ → β :=
  fixCore2 (fun _ _ => arbitrary) rec

def bfix3 {α₁ α₂ α₃ β : Type u} (base : α₁ → α₂ → α₃ → β) (rec : (α₁ → α₂ → α₃ → β) → α₁ → α₂ → α₃ → β) : Nat → α₁ → α₂ → α₃ → β
  | 0,   a₁, a₂, a₃ => base a₁ a₂ a₃
  | n+1, a₁, a₂, a₃ => rec (bfix3 base rec n) a₁ a₂ a₃

@[extern c inline "lean_fixpoint3(#6, #7, #8, #9)"]
def fixCore3 {α₁ α₂ α₃ β : Type u} (base : α₁ → α₂ → α₃ → β) (rec : (α₁ → α₂ → α₃ → β) → α₁ → α₂ → α₃ → β) : α₁ → α₂ → α₃ → β :=
  bfix3 base rec USize.size

@[inline] def fix3 {α₁ α₂ α₃ β : Type u} [Inhabited β] (rec : (α₁ → α₂ → α₃ → β) → α₁ → α₂ → α₃ → β) : α₁ → α₂ → α₃ → β :=
  fixCore3 (fun _ _ _ => arbitrary) rec

def bfix4 {α₁ α₂ α₃ α₄ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → β) (rec : (α₁ → α₂ → α₃ → α₄ → β) → α₁ → α₂ → α₃ → α₄ → β) : Nat → α₁ → α₂ → α₃ → α₄ → β
  | 0,   a₁, a₂, a₃, a₄ => base a₁ a₂ a₃ a₄
  | n+1, a₁, a₂, a₃, a₄ => rec (bfix4 base rec n) a₁ a₂ a₃ a₄

@[extern c inline "lean_fixpoint4(#7, #8, #9, #10, #11)"]
def fixCore4 {α₁ α₂ α₃ α₄ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → β) (rec : (α₁ → α₂ → α₃ → α₄ → β) → α₁ → α₂ → α₃ → α₄ → β) : α₁ → α₂ → α₃ → α₄ → β :=
  bfix4 base rec USize.size

@[inline] def fix4 {α₁ α₂ α₃ α₄ β : Type u} [Inhabited β] (rec : (α₁ → α₂ → α₃ → α₄ → β) → α₁ → α₂ → α₃ → α₄ → β) : α₁ → α₂ → α₃ → α₄ → β :=
fixCore4 (fun _ _ _ _ => arbitrary) rec

def bfix5 {α₁ α₂ α₃ α₄ α₅ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → β) : Nat → α₁ → α₂ → α₃ → α₄ → α₅ → β
  | 0,   a₁, a₂, a₃, a₄, a₅ => base a₁ a₂ a₃ a₄ a₅
  | n+1, a₁, a₂, a₃, a₄, a₅ => rec (bfix5 base rec n) a₁ a₂ a₃ a₄ a₅

@[extern c inline "lean_fixpoint5(#8, #9, #10, #11, #12, #13)"]
def fixCore5 {α₁ α₂ α₃ α₄ α₅ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → β :=
  bfix5 base rec USize.size

@[inline] def fix5 {α₁ α₂ α₃ α₄ α₅ β : Type u} [Inhabited β] (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → β :=
  fixCore5 (fun _ _ _ _ _ => arbitrary) rec

def bfix6 {α₁ α₂ α₃ α₄ α₅ α₆ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) : Nat → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β
  | 0,   a₁, a₂, a₃, a₄, a₅, a₆ => base a₁ a₂ a₃ a₄ a₅ a₆
  | n+1, a₁, a₂, a₃, a₄, a₅, a₆ => rec (bfix6 base rec n) a₁ a₂ a₃ a₄ a₅ a₆

@[extern c inline "lean_fixpoint6(#9, #10, #11, #12, #13, #14, #15)"]
def fixCore6 {α₁ α₂ α₃ α₄ α₅ α₆ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β :=
  bfix6 base rec USize.size

@[inline] def fix6 {α₁ α₂ α₃ α₄ α₅ α₆ β : Type u} [Inhabited β] (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β :=
  fixCore6 (fun _ _ _ _ _ _ => arbitrary) rec
