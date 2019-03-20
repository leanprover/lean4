/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.uint
universe u

def bfix1 {α β : Type u} (base : α → β) (rec : (α → β) → α → β) : nat → α → β
| 0     a := base a
| (n+1) a := rec (bfix1 n) a

@[extern cpp inline "lean::fixpoint(#4, #5)"]
def fixCore1 {α β : Type u} (base : @& (α → β)) (rec : (α → β) → α → β) : α → β :=
bfix1 base rec usizeSz

@[inline] def fixCore {α β : Type u} (base : @& (α → β)) (rec : (α → β) → α → β) : α → β :=
fixCore1 base rec

@[inline] def fix1 {α β : Type u} [inhabited β] (rec : (α → β) → α → β) : α → β :=
fixCore1 (λ _, default β) rec

@[inline] def fix {α β : Type u} [inhabited β] (rec : (α → β) → α → β) : α → β :=
fixCore1 (λ _, default β) rec

def bfix2 {α₁ α₂ β : Type u} (base : α₁ → α₂ → β) (rec : (α₁ → α₂ → β) → α₁ → α₂ → β) : nat → α₁ → α₂ → β
| 0     a₁ a₂ := base a₁ a₂
| (n+1) a₁ a₂ := rec (bfix2 n) a₁ a₂

@[extern cpp inline "lean::fixpoint2(#5, #6, #7)"]
def fixCore2 {α₁ α₂ β : Type u} (base : α₁ → α₂ → β) (rec : (α₁ → α₂ → β) → α₁ → α₂ → β) : α₁ → α₂ → β :=
bfix2 base rec usizeSz

@[inline] def fix2 {α₁ α₂ β : Type u} [inhabited β] (rec : (α₁ → α₂ → β) → α₁ → α₂ → β) : α₁ → α₂ → β :=
fixCore2 (λ _ _, default β) rec

def bfix3 {α₁ α₂ α₃ β : Type u} (base : α₁ → α₂ → α₃ → β) (rec : (α₁ → α₂ → α₃ → β) → α₁ → α₂ → α₃ → β) : nat → α₁ → α₂ → α₃ → β
| 0     a₁ a₂ a₃ := base a₁ a₂ a₃
| (n+1) a₁ a₂ a₃ := rec (bfix3 n) a₁ a₂ a₃

@[extern cpp inline "lean::fixpoint3(#6, #7, #8, #9)"]
def fixCore3 {α₁ α₂ α₃ β : Type u} (base : α₁ → α₂ → α₃ → β) (rec : (α₁ → α₂ → α₃ → β) → α₁ → α₂ → α₃ → β) : α₁ → α₂ → α₃ → β :=
bfix3 base rec usizeSz

@[inline] def fix3 {α₁ α₂ α₃ β : Type u} [inhabited β] (rec : (α₁ → α₂ → α₃ → β) → α₁ → α₂ → α₃ → β) : α₁ → α₂ → α₃ → β :=
fixCore3 (λ _ _ _, default β) rec

def bfix4 {α₁ α₂ α₃ α₄ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → β) (rec : (α₁ → α₂ → α₃ → α₄ → β) → α₁ → α₂ → α₃ → α₄ → β) : nat → α₁ → α₂ → α₃ → α₄ → β
| 0     a₁ a₂ a₃ a₄ := base a₁ a₂ a₃ a₄
| (n+1) a₁ a₂ a₃ a₄ := rec (bfix4 n) a₁ a₂ a₃ a₄

@[extern cpp inline "lean::fixpoint4(#7, #8, #9, #10, #11)"]
def fixCore4 {α₁ α₂ α₃ α₄ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → β) (rec : (α₁ → α₂ → α₃ → α₄ → β) → α₁ → α₂ → α₃ → α₄ → β) : α₁ → α₂ → α₃ → α₄ → β :=
bfix4 base rec usizeSz

@[inline] def fix4 {α₁ α₂ α₃ α₄ β : Type u} [inhabited β] (rec : (α₁ → α₂ → α₃ → α₄ → β) → α₁ → α₂ → α₃ → α₄ → β) : α₁ → α₂ → α₃ → α₄ → β :=
fixCore4 (λ _ _ _ _, default β) rec

def bfix5 {α₁ α₂ α₃ α₄ α₅ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → β) : nat → α₁ → α₂ → α₃ → α₄ → α₅ → β
| 0     a₁ a₂ a₃ a₄ a₅ := base a₁ a₂ a₃ a₄ a₅
| (n+1) a₁ a₂ a₃ a₄ a₅ := rec (bfix5 n) a₁ a₂ a₃ a₄ a₅

@[extern cpp inline "lean::fixpoint5(#8, #9, #10, #11, #12, #13)"]
def fixCore5 {α₁ α₂ α₃ α₄ α₅ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → β :=
bfix5 base rec usizeSz

@[inline] def fix5 {α₁ α₂ α₃ α₄ α₅ β : Type u} [inhabited β] (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → β :=
fixCore5 (λ _ _ _ _ _, default β) rec

def bfix6 {α₁ α₂ α₃ α₄ α₅ α₆ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) : nat → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β
| 0     a₁ a₂ a₃ a₄ a₅ a₆ := base a₁ a₂ a₃ a₄ a₅ a₆
| (n+1) a₁ a₂ a₃ a₄ a₅ a₆ := rec (bfix6 n) a₁ a₂ a₃ a₄ a₅ a₆

@[extern cpp inline "lean::fixpoint6(#9, #10, #11, #12, #13, #14, #15)"]
def fixCore6 {α₁ α₂ α₃ α₄ α₅ α₆ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β :=
bfix6 base rec usizeSz

@[inline] def fix6 {α₁ α₂ α₃ α₄ α₅ α₆ β : Type u} [inhabited β] (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β :=
fixCore6 (λ _ _ _ _ _ _, default β) rec
