/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.lean.options init.data.array
universes u v

namespace Lean

inductive Format
| nil          : Format
| line         : Format
| text         : String → Format
| nest         : Nat → Format → Format
| compose      : Bool → Format → Format → Format
| choice       : Format → Format → Format

namespace Format
@[export lean.format_append_core]
protected def append (a b : Format) : Format :=
compose false a b

instance : HasAppend Format     := ⟨Format.append⟩
instance : HasCoe String Format := ⟨text⟩
instance : Inhabited Format     := ⟨nil⟩

def join (xs : List Format) : Format :=
xs.foldl (++) ""

def isNil : Format → Bool
| nil := true
| _   := false

def flatten : Format → Format
| nil                     := nil
| line                    := text " "
| f@(text _)              := f
| (nest _ f)              := flatten f
| (choice f _)            := flatten f
| f@(compose true _ _)    := f
| f@(compose false f₁ f₂) := compose true (flatten f₁) (flatten f₂)

@[export lean.format_group_core]
def group : Format → Format
| nil                  := nil
| f@(text _)           := f
| f@(compose true _ _) := f
| f                    := choice (flatten f) f

structure SpaceResult :=
(found    := false)
(exceeded := false)
(space    := 0)

@[inline] private def merge (w : Nat) (r₁ : SpaceResult) (r₂ : Thunk SpaceResult) : SpaceResult :=
if r₁.exceeded || r₁.found then r₁
else
  let y := r₂.get;
  if y.exceeded || y.found then y
  else
    let newSpace := r₁.space + y.space;
    { space := newSpace, exceeded := newSpace > w }

def spaceUptoLine : Format → Nat → SpaceResult
| nil               w := {}
| line              w := { found := true }
| (text s)          w := { space := s.length, exceeded := s.length > w }
| (compose _ f₁ f₂) w := merge w (spaceUptoLine f₁ w) (spaceUptoLine f₂ w)
| (nest _ f)        w := spaceUptoLine f w
| (choice f₁ f₂)    w := spaceUptoLine f₂ w

def spaceUptoLine' : List (Nat × Format) → Nat → SpaceResult
| []      w := {}
| (p::ps) w := merge w (spaceUptoLine p.2 w) (spaceUptoLine' ps w)

partial def be : Nat → Nat → String → List (Nat × Format) → String
| w k out []                           := out
| w k out ((i, nil)::z)                := be w k out z
| w k out ((i, (compose _ f₁ f₂))::z)  := be w k out ((i, f₁)::(i, f₂)::z)
| w k out ((i, (nest n f))::z)         := be w k out ((i+n, f)::z)
| w k out ((i, text s)::z)             := be w (k + s.length) (out ++ s) z
| w k out ((i, line)::z)               := be w i ((out ++ "\n").pushn ' ' i) z
| w k out ((i, choice f₁ f₂)::z)       :=
  let r := merge w (spaceUptoLine f₁ w) (spaceUptoLine' z w);
  if r.exceeded then be w k out ((i, f₂)::z) else be w k out ((i, f₁)::z)

@[inline] def bracket (l : String) (f : Format) (r : String) : Format :=
group (nest l.length $ l ++ f ++ r)

@[inline] def paren (f : Format) : Format :=
bracket "(" f ")"

@[inline] def sbracket (f : Format) : Format :=
bracket "[" f "]"

def defIndent  := 4
def defUnicode := true
def defWidth   := 120

def getWidth (o : Options) : Nat    := o.get `format.width  defWidth
def getIndent (o : Options) : Nat   := o.get `format.indent defIndent
def getUnicode (o : Options) : Bool := o.get `format.unicode defUnicode

@[init] def indentOption : IO Unit :=
registerOption `format.indent { defValue := defIndent, group := "format", descr := "indentation" }
@[init] def unicodeOption : IO Unit :=
registerOption `format.unicode { defValue := defUnicode, group := "format", descr := "unicode characters" }
@[init] def widthOption : IO Unit :=
registerOption `format.width { defValue := defWidth, group := "format", descr := "line width" }

@[export lean.format_pretty_core]
def prettyAux (f : Format) (w : Nat := defWidth) : String :=
be w 0 "" [(0, f)]

def pretty (f : Format) (o : Options := {}) : String :=
prettyAux f (getWidth o)

end Format

open Lean.Format

class HasFormat (α : Type u) :=
(format : α → Format)

export Lean.HasFormat (format)

def fmt {α : Type u} [HasFormat α] : α → Format :=
format

instance toStringToFormat {α : Type u} [HasToString α] : HasFormat α :=
⟨text ∘ toString⟩

-- note: must take precendence over the above instance to avoid premature formatting
instance formatHasFormat : HasFormat Format :=
⟨id⟩

instance stringHasFormat : HasFormat String := ⟨Format.text⟩

def Format.joinSep {α : Type u} [HasFormat α] : List α → Format → Format
| []      sep  := nil
| [a]     sep := format a
| (a::as) sep := format a ++ sep ++ Format.joinSep as sep

def Format.prefixJoin {α : Type u} [HasFormat α] (pre : Format) : List α → Format
| []      := nil
| (a::as) := pre ++ format a ++ Format.prefixJoin as

def Format.joinSuffix {α : Type u} [HasFormat α] : List α → Format → Format
| []      suffix := nil
| (a::as) suffix := format a ++ suffix ++ Format.joinSuffix as suffix

def List.format {α : Type u} [HasFormat α] : List α → Format
| [] := "[]"
| xs := sbracket $ Format.joinSep xs ("," ++ line)

instance listHasFormat {α : Type u} [HasFormat α] : HasFormat (List α) :=
⟨List.format⟩

instance prodHasFormat {α : Type u} {β : Type v} [HasFormat α] [HasFormat β] : HasFormat (Prod α β) :=
⟨λ ⟨a, b⟩, paren $ format a ++ "," ++ line ++ format b⟩

def Format.joinArraySep {α : Type u} [HasFormat α] (a : Array α) (sep : Format) : Format :=
a.iterate nil (λ i a r, if i.val > 0 then r ++ sep ++ format a else r ++ format a)

instance natHasFormat : HasFormat Nat       := ⟨λ n, toString n⟩
instance uint16HasFormat : HasFormat UInt16 := ⟨λ n, toString n⟩
instance uint32HasFormat : HasFormat UInt32 := ⟨λ n, toString n⟩
instance uint64HasFormat : HasFormat UInt64 := ⟨λ n, toString n⟩
instance usizeHasFormat : HasFormat USize   := ⟨λ n, toString n⟩
instance nameHasFormat : HasFormat Name     := ⟨λ n, n.toString⟩

protected def Format.repr : Format → Format
| nil := "Format.nil"
| line := "Format.line"
| (text s) := paren $ "Format.text" ++ line ++ repr s
| (nest n f) := paren $ "Format.nest" ++ line ++ repr n ++ line ++ Format.repr f
| (compose b f₁ f₂) := paren $ "Format.compose " ++ repr b ++ line ++ Format.repr f₁ ++ line ++ Format.repr f₂
| (choice f₁ f₂) := paren $ "Format.choice" ++ line ++ Format.repr f₁ ++ line ++ Format.repr f₂


instance formatHasToString : HasToString Format := ⟨Format.pretty⟩

instance : HasRepr Format := ⟨Format.pretty ∘ Format.repr⟩

def formatDataValue : DataValue → Format
| (DataValue.ofString v) := format (repr v)
| (DataValue.ofBool v)   := format v
| (DataValue.ofName v)   := "`" ++ format v
| (DataValue.ofNat v)    := format v
| (DataValue.ofInt v)    := format v

instance dataValueHasFormat : HasFormat DataValue := ⟨formatDataValue⟩

def formatEntry : Name × DataValue → Format
| (n, v) := format n ++ " := " ++ format v

instance entryHasFormat : HasFormat (Name × DataValue) := ⟨formatEntry⟩

def formatKVMap (m : KVMap) : Format :=
sbracket (Format.joinSep m.entries ", ")

instance kvMapHasFormat : HasFormat KVMap := ⟨formatKVMap⟩

end Lean
