/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.uint
universe u

def bfix {α β : Type u} (base : α → β) (rec : (α → β) → α → β) : nat → α → β
| 0     a := base a
| (n+1) a := rec (bfix n) a

@[extern cpp inline "lean::fixpoint(#4, #5)"]
def fix_core {α β : Type u} (base : @& (α → β)) (rec : (α → β) → α → β) : α → β :=
bfix base rec usize_sz

@[inline] def fix {α β : Type u} [inhabited β] (rec : (α → β) → α → β) : α → β :=
fix_core (λ _, default β) rec

@[inline] def fix₁ {α β : Type u} [inhabited β] (rec : (α → β) → α → β) : α → β :=
fix_core (λ _, default β) rec

def bfix₂ {α₁ α₂ β : Type u} (base : α₁ → α₂ → β) (rec : (α₁ → α₂ → β) → α₁ → α₂ → β) : nat → α₁ → α₂ → β
| 0     a₁ a₂ := base a₁ a₂
| (n+1) a₁ a₂ := rec (bfix₂ n) a₁ a₂

@[extern cpp inline "lean::fixpoint2(#5, #6, #7)"]
def fix_core₂ {α₁ α₂ β : Type u} (base : α₁ → α₂ → β) (rec : (α₁ → α₂ → β) → α₁ → α₂ → β) : α₁ → α₂ → β :=
bfix₂ base rec usize_sz

@[inline] def fix₂ {α₁ α₂ β : Type u} [inhabited β] (rec : (α₁ → α₂ → β) → α₁ → α₂ → β) : α₁ → α₂ → β :=
fix_core₂ (λ _ _, default β) rec

def bfix₃ {α₁ α₂ α₃ β : Type u} (base : α₁ → α₂ → α₃ → β) (rec : (α₁ → α₂ → α₃ → β) → α₁ → α₂ → α₃ → β) : nat → α₁ → α₂ → α₃ → β
| 0     a₁ a₂ a₃ := base a₁ a₂ a₃
| (n+1) a₁ a₂ a₃ := rec (bfix₃ n) a₁ a₂ a₃

@[extern cpp inline "lean::fixpoint3(#6, #7, #8, #9)"]
def fix_core₃ {α₁ α₂ α₃ β : Type u} (base : α₁ → α₂ → α₃ → β) (rec : (α₁ → α₂ → α₃ → β) → α₁ → α₂ → α₃ → β) : α₁ → α₂ → α₃ → β :=
bfix₃ base rec usize_sz

@[inline] def fix₃ {α₁ α₂ α₃ β : Type u} [inhabited β] (rec : (α₁ → α₂ → α₃ → β) → α₁ → α₂ → α₃ → β) : α₁ → α₂ → α₃ → β :=
fix_core₃ (λ _ _ _, default β) rec

def bfix₄ {α₁ α₂ α₃ α₄ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → β) (rec : (α₁ → α₂ → α₃ → α₄ → β) → α₁ → α₂ → α₃ → α₄ → β) : nat → α₁ → α₂ → α₃ → α₄ → β
| 0     a₁ a₂ a₃ a₄ := base a₁ a₂ a₃ a₄
| (n+1) a₁ a₂ a₃ a₄ := rec (bfix₄ n) a₁ a₂ a₃ a₄

@[extern cpp inline "lean::fixpoint4(#7, #8, #9, #10, #11)"]
def fix_core₄ {α₁ α₂ α₃ α₄ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → β) (rec : (α₁ → α₂ → α₃ → α₄ → β) → α₁ → α₂ → α₃ → α₄ → β) : α₁ → α₂ → α₃ → α₄ → β :=
bfix₄ base rec usize_sz

@[inline] def fix₄ {α₁ α₂ α₃ α₄ β : Type u} [inhabited β] (rec : (α₁ → α₂ → α₃ → α₄ → β) → α₁ → α₂ → α₃ → α₄ → β) : α₁ → α₂ → α₃ → α₄ → β :=
fix_core₄ (λ _ _ _ _, default β) rec

def bfix₅ {α₁ α₂ α₃ α₄ α₅ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → β) : nat → α₁ → α₂ → α₃ → α₄ → α₅ → β
| 0     a₁ a₂ a₃ a₄ a₅ := base a₁ a₂ a₃ a₄ a₅
| (n+1) a₁ a₂ a₃ a₄ a₅ := rec (bfix₅ n) a₁ a₂ a₃ a₄ a₅

@[extern cpp inline "lean::fixpoint5(#8, #9, #10, #11, #12, #13)"]
def fix_core₅ {α₁ α₂ α₃ α₄ α₅ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → β :=
bfix₅ base rec usize_sz

@[inline] def fix₅ {α₁ α₂ α₃ α₄ α₅ β : Type u} [inhabited β] (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → β :=
fix_core₅ (λ _ _ _ _ _, default β) rec

def bfix₆ {α₁ α₂ α₃ α₄ α₅ α₆ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) : nat → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β
| 0     a₁ a₂ a₃ a₄ a₅ a₆ := base a₁ a₂ a₃ a₄ a₅ a₆
| (n+1) a₁ a₂ a₃ a₄ a₅ a₆ := rec (bfix₆ n) a₁ a₂ a₃ a₄ a₅ a₆

@[extern cpp inline "lean::fixpoint6(#9, #10, #11, #12, #13, #14, #15)"]
def fix_core₆ {α₁ α₂ α₃ α₄ α₅ α₆ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β :=
bfix₆ base rec usize_sz

@[inline] def fix₆ {α₁ α₂ α₃ α₄ α₅ α₆ β : Type u} [inhabited β] (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β :=
fix_core₆ (λ _ _ _ _ _ _, default β) rec
