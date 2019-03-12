/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.uint
universe u

def bfix_1 {α β : Type u} (base : α → β) (rec : (α → β) → α → β) : nat → α → β
| 0     a := base a
| (n+1) a := rec (bfix_1 n) a

@[extern cpp inline "lean::fixpoint(#4, #5)"]
def fix_core_1 {α β : Type u} (base : @& (α → β)) (rec : (α → β) → α → β) : α → β :=
bfix_1 base rec usize_sz

@[inline] def fix_core {α β : Type u} (base : @& (α → β)) (rec : (α → β) → α → β) : α → β :=
fix_core_1 base rec

@[inline] def fix_1 {α β : Type u} [inhabited β] (rec : (α → β) → α → β) : α → β :=
fix_core_1 (λ _, default β) rec

@[inline] def fix {α β : Type u} [inhabited β] (rec : (α → β) → α → β) : α → β :=
fix_core_1 (λ _, default β) rec

def bfix_2 {α₁ α₂ β : Type u} (base : α₁ → α₂ → β) (rec : (α₁ → α₂ → β) → α₁ → α₂ → β) : nat → α₁ → α₂ → β
| 0     a₁ a₂ := base a₁ a₂
| (n+1) a₁ a₂ := rec (bfix_2 n) a₁ a₂

@[extern cpp inline "lean::fixpoint2(#5, #6, #7)"]
def fix_core_2 {α₁ α₂ β : Type u} (base : α₁ → α₂ → β) (rec : (α₁ → α₂ → β) → α₁ → α₂ → β) : α₁ → α₂ → β :=
bfix_2 base rec usize_sz

@[inline] def fix_2 {α₁ α₂ β : Type u} [inhabited β] (rec : (α₁ → α₂ → β) → α₁ → α₂ → β) : α₁ → α₂ → β :=
fix_core_2 (λ _ _, default β) rec

def bfix_3 {α₁ α₂ α₃ β : Type u} (base : α₁ → α₂ → α₃ → β) (rec : (α₁ → α₂ → α₃ → β) → α₁ → α₂ → α₃ → β) : nat → α₁ → α₂ → α₃ → β
| 0     a₁ a₂ a₃ := base a₁ a₂ a₃
| (n+1) a₁ a₂ a₃ := rec (bfix_3 n) a₁ a₂ a₃

@[extern cpp inline "lean::fixpoint3(#6, #7, #8, #9)"]
def fix_core_3 {α₁ α₂ α₃ β : Type u} (base : α₁ → α₂ → α₃ → β) (rec : (α₁ → α₂ → α₃ → β) → α₁ → α₂ → α₃ → β) : α₁ → α₂ → α₃ → β :=
bfix_3 base rec usize_sz

@[inline] def fix_3 {α₁ α₂ α₃ β : Type u} [inhabited β] (rec : (α₁ → α₂ → α₃ → β) → α₁ → α₂ → α₃ → β) : α₁ → α₂ → α₃ → β :=
fix_core_3 (λ _ _ _, default β) rec

def bfix_4 {α₁ α₂ α₃ α₄ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → β) (rec : (α₁ → α₂ → α₃ → α₄ → β) → α₁ → α₂ → α₃ → α₄ → β) : nat → α₁ → α₂ → α₃ → α₄ → β
| 0     a₁ a₂ a₃ a₄ := base a₁ a₂ a₃ a₄
| (n+1) a₁ a₂ a₃ a₄ := rec (bfix_4 n) a₁ a₂ a₃ a₄

@[extern cpp inline "lean::fixpoint4(#7, #8, #9, #10, #11)"]
def fix_core_4 {α₁ α₂ α₃ α₄ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → β) (rec : (α₁ → α₂ → α₃ → α₄ → β) → α₁ → α₂ → α₃ → α₄ → β) : α₁ → α₂ → α₃ → α₄ → β :=
bfix_4 base rec usize_sz

@[inline] def fix_4 {α₁ α₂ α₃ α₄ β : Type u} [inhabited β] (rec : (α₁ → α₂ → α₃ → α₄ → β) → α₁ → α₂ → α₃ → α₄ → β) : α₁ → α₂ → α₃ → α₄ → β :=
fix_core_4 (λ _ _ _ _, default β) rec

def bfix_5 {α₁ α₂ α₃ α₄ α₅ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → β) : nat → α₁ → α₂ → α₃ → α₄ → α₅ → β
| 0     a₁ a₂ a₃ a₄ a₅ := base a₁ a₂ a₃ a₄ a₅
| (n+1) a₁ a₂ a₃ a₄ a₅ := rec (bfix_5 n) a₁ a₂ a₃ a₄ a₅

@[extern cpp inline "lean::fixpoint5(#8, #9, #10, #11, #12, #13)"]
def fix_core_5 {α₁ α₂ α₃ α₄ α₅ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → β :=
bfix_5 base rec usize_sz

@[inline] def fix_5 {α₁ α₂ α₃ α₄ α₅ β : Type u} [inhabited β] (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → β :=
fix_core_5 (λ _ _ _ _ _, default β) rec

def bfix_6 {α₁ α₂ α₃ α₄ α₅ α₆ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) : nat → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β
| 0     a₁ a₂ a₃ a₄ a₅ a₆ := base a₁ a₂ a₃ a₄ a₅ a₆
| (n+1) a₁ a₂ a₃ a₄ a₅ a₆ := rec (bfix_6 n) a₁ a₂ a₃ a₄ a₅ a₆

@[extern cpp inline "lean::fixpoint6(#9, #10, #11, #12, #13, #14, #15)"]
def fix_core_6 {α₁ α₂ α₃ α₄ α₅ α₆ β : Type u} (base : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β :=
bfix_6 base rec usize_sz

@[inline] def fix_6 {α₁ α₂ α₃ α₄ α₅ α₆ β : Type u} [inhabited β] (rec : (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β :=
fix_core_6 (λ _ _ _ _ _ _, default β) rec
