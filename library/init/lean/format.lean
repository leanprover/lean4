/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.control.except init.control.reader init.control.state
universes u v

namespace lean

inductive format
| nil          : format
| line         : format
| text         : string → format
| nest         : nat → format → format
| compose      : bool → format → format → format
| choice       : format → format → format

namespace format
instance : hasAppend format     := ⟨compose ff⟩
instance : hasCoe string format := ⟨text⟩

def join (xs : list format) : format :=
xs.foldl (++) ""

def flatten : format → format
| nil                  := nil
| line                 := text " "
| f@(text _)           := f
| (nest _ f)           := flatten f
| (choice f _)         := flatten f
| f@(compose tt _ _)   := f
| f@(compose ff f₁ f₂) := compose tt (flatten f₁) (flatten f₂)

def group : format → format
| nil                := nil
| f@(text _)         := f
| f@(compose tt _ _) := f
| f                  := choice (flatten f) f

structure spaceResult :=
(found    := ff)
(exceeded := ff)
(space    := 0)

/-
TODO: mark as `@[inline]` as soon as we fix the code inliner.
-/
private def merge (w : nat) (r₁ : spaceResult) (r₂ : thunk spaceResult) : spaceResult :=
if r₁.exceeded || r₁.found then r₁
else let y := r₂.get in
     if y.exceeded || y.found then y
     else let newSpace := r₁.space + y.space in
          { space := newSpace, exceeded := newSpace > w }

def spaceUptoLine : format → nat → spaceResult
| nil               w := {}
| line              w := { found := tt }
| (text s)          w := { space := s.length, exceeded := s.length > w }
| (compose _ f₁ f₂) w := merge w (spaceUptoLine f₁ w) (spaceUptoLine f₂ w)
| (nest _ f)        w := spaceUptoLine f w
| (choice f₁ f₂)    w := spaceUptoLine f₂ w

def spaceUptoLine' : list (nat × format) → nat → spaceResult
| []      w := {}
| (p::ps) w := merge w (spaceUptoLine p.2 w) (spaceUptoLine' ps w)

def be : nat → nat → string → list (nat × format) → string
| w k out []                           := out
| w k out ((i, nil)::z)                := be w k out z
| w k out ((i, (compose _ f₁ f₂))::z)  := be w k out ((i, f₁)::(i, f₂)::z)
| w k out ((i, (nest n f))::z)         := be w k out ((i+n, f)::z)
| w k out ((i, text s)::z)             := be w (k + s.length) (out ++ s) z
| w k out ((i, line)::z)               := be w i ((out ++ "\n").pushn ' ' i) z
| w k out ((i, choice f₁ f₂)::z)       :=
  let r := merge w (spaceUptoLine f₁ w) (spaceUptoLine' z w) in
  if r.exceeded then be w k out ((i, f₂)::z) else be w k out ((i, f₁)::z)

def pretty (f : format) (w : nat := 80) : string :=
be w 0 "" [(0, f)]

@[inline] def bracket (l : string) (f : format) (r : string) : format :=
group (nest l.length $ l ++ f ++ r)

@[inline] def paren (f : format) : format :=
bracket "(" f ")"

@[inline] def sbracket (f : format) : format :=
bracket "[" f "]"

end format

open lean.format

class hasToFormat (α : Type u) :=
(toFormat : α → format)

export lean.hasToFormat (toFormat)

def toFmt {α : Type u} [hasToFormat α] : α → format :=
toFormat

instance toStringToFormat {α : Type u} [hasToString α] : hasToFormat α :=
⟨text ∘ toString⟩

-- note: must take precendence over the above instance to avoid premature formatting
instance formatHasToFormat : hasToFormat format :=
⟨id⟩

instance stringHasToFormat : hasToFormat string := ⟨format.text⟩

def format.joinSep {α : Type u} [hasToFormat α] : list α → format → format
| []      sep  := nil
| [a]     sep := toFmt a
| (a::as) sep := toFmt a ++ sep ++ format.joinSep as sep

def format.prefixJoin {α : Type u} [hasToFormat α] (pre : format) : list α → format
| []      := nil
| (a::as) := pre ++ toFmt a ++ format.prefixJoin as

def format.joinSuffix {α : Type u} [hasToFormat α] : list α → format → format
| []      suffix := nil
| (a::as) suffix := toFmt a ++ suffix ++ format.joinSuffix as suffix

def list.toFormat {α : Type u} [hasToFormat α] : list α → format
| [] := "[]"
| xs := sbracket $ format.joinSep xs ("," ++ line)

instance listHasToFormat {α : Type u} [hasToFormat α] : hasToFormat (list α) :=
⟨list.toFormat⟩

instance prodHasToFormat {α : Type u} {β : Type v} [hasToFormat α] [hasToFormat β] : hasToFormat (prod α β) :=
⟨λ ⟨a, b⟩, paren $ toFormat a ++ "," ++ line ++ toFormat b⟩

instance natHasToFormat : hasToFormat nat    := ⟨λ n, toString n⟩
instance uint16HasToFormat : hasToFormat uint16 := ⟨λ n, toString n⟩
instance uint32HasToFormat : hasToFormat uint32 := ⟨λ n, toString n⟩
instance uint64HasToFormat : hasToFormat uint64 := ⟨λ n, toString n⟩
instance usizeHasToFormat : hasToFormat usize := ⟨λ n, toString n⟩

instance formatHasToString : hasToString format := ⟨pretty⟩

protected def format.repr : format → format
| nil := "format.nil"
| line := "format.line"
| (text s) := paren $ "format.text" ++ line ++ repr s
| (nest n f) := paren $ "format.nest" ++ line ++ repr n ++ line ++ format.repr f
| (compose b f₁ f₂) := paren $ "format.compose " ++ repr b ++ line ++ format.repr f₁ ++ line ++ format.repr f₂
| (choice f₁ f₂) := paren $ "format.choice" ++ line ++ format.repr f₁ ++ line ++ format.repr f₂

instance : hasRepr format := ⟨format.pretty ∘ format.repr⟩

end lean
