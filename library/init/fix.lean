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
def fix_core {α β : Type u} (base : @& (α → β)) (rec : (α → β) → α → β) (a : α) : β :=
bfix base rec usize_sz a

@[inline] def fix {α β : Type u} [inhabited β] (rec : (α → β) → α → β) (a : α) : β :=
fix_core (λ _, default β) rec a
