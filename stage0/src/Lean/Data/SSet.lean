/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.SMap

namespace Lean

/-- Staged set. It is just a simple wrapper on top of Staged maps. -/
def SSet (α : Type u) [BEq α] [Hashable α] := SMap α Unit

namespace SSet
variable {α : Type u} [BEq α] [Hashable α]

instance : Inhabited (SSet α) := inferInstanceAs (Inhabited (SMap ..))

abbrev empty : SSet α := SMap.empty

abbrev insert (s : SSet α) (a : α) : SSet α :=
  SMap.insert s a ()

abbrev contains (s : SSet α) (a : α) : Bool :=
  SMap.contains s a

abbrev forM [Monad m] (s : SSet α) (f : α → m PUnit) : m PUnit :=
  SMap.forM s fun a _ => f a

/-- Move from stage 1 into stage 2. -/
abbrev switch (s : SSet α) : SSet α :=
  SMap.switch s

abbrev fold (f : σ → α → σ) (init : σ) (s : SSet α) : σ :=
  SMap.fold (fun d a _ => f d a) init s

abbrev size (s : SSet α) : Nat :=
  SMap.size s

def toList (m : SSet α) : List α :=
  m.fold (init := []) fun es a => a::es

end SSet

end Lean

def List.toSSet [BEq α] [Hashable α] (es : List α) : Lean.SSet α :=
  es.foldl (init := {}) fun s a => s.insert a

instance {_ : BEq α} {_ : Hashable α} [Repr α] : Repr (Lean.SSet α) where
  reprPrec v prec := Repr.addAppParen (reprArg v.toList ++ ".toSSet") prec
