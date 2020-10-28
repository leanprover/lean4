/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
universes u

namespace Lean

inductive LOption (α : Type u)
| none  : LOption α
| some  : α → LOption α
| undef : LOption α

namespace LOption
variables {α : Type u}

instance : Inhabited (LOption α) := ⟨none⟩

instance [ToString α] : ToString (LOption α) :=
⟨fun o => match o with | none   => "none" | undef  => "undef" | (some a) => "(some " ++ toString a ++ ")"⟩

def beq [BEq α] : LOption α → LOption α → Bool
| none,   none   => true
| undef,  undef  => true
| some a, some b => a == b
| _,      _      => false

instance [BEq α] : BEq (LOption α) := ⟨beq⟩

end LOption
end Lean

def Option.toLOption {α : Type u} : Option α → Lean.LOption α
| none   => Lean.LOption.none
| some a => Lean.LOption.some a

@[inline] def toLOptionM {α} {m : Type → Type} [Monad m] (x : m (Option α)) : m (Lean.LOption α) := do
let b ← x
pure b.toLOption
