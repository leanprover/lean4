/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Data.Options
universes u v

namespace Lean

inductive Format
| nil                 : Format
| line                : Format
| text                : String → Format
| nest (indent : Nat) : Format → Format
| append              : Format → Format → Format
| group               : Format → Format

namespace Format
@[export lean_format_append]
protected def appendEx (a b : Format) : Format :=
append a b

@[export lean_format_group]
protected def groupEx : Format → Format :=
group

instance : HasAppend Format     := ⟨Format.append⟩
instance : HasCoe String Format := ⟨text⟩
instance : Inhabited Format     := ⟨nil⟩

def join (xs : List Format) : Format :=
xs.foldl HasAppend.append ""

def isNil : Format → Bool
| nil => true
| _   => false

structure SpaceResult :=
(foundLine := false)
(space     := 0)

@[inline] private def merge (w : Nat) (r₁ : SpaceResult) (r₂ : Thunk SpaceResult) : SpaceResult :=
if r₁.space > w || r₁.foundLine then r₁
else
  let y := r₂.get;
  if y.space > w || y.foundLine then y
  else
    let newSpace := r₁.space + y.space;
    { space := newSpace }

def spaceUptoLine : Format → Bool → Nat → SpaceResult
| nil,          flatten, w => {}
| line,         flatten, w => if flatten then { space := 1 } else { foundLine := true }
| text s,       flatten, w => { space := s.length }
| append f₁ f₂, flatten, w => merge w (spaceUptoLine f₁ flatten w) (spaceUptoLine f₂ flatten w)
| nest _ f,     flatten, w => spaceUptoLine f flatten w
| group f,      flatten, w => spaceUptoLine f true w

def spaceUptoLine' : List (Bool × Nat × Format) → Nat → SpaceResult
| [],    w => {}
| (fl, _, f)::ps, w => merge w (spaceUptoLine f fl w) (spaceUptoLine' ps w)

partial def be : Nat → Nat → String → List (Bool × Nat × Format) → String
| w, k, out, []                       => out
| w, k, out, (fl, i, nil)::z          => be w k out z
| w, k, out, (fl, i, append f₁ f₂)::z => be w k out ((fl, i, f₁)::(fl, i, f₂)::z)
| w, k, out, (fl, i, nest n f)::z     => be w k out ((fl, i+n, f)::z)
| w, k, out, (fl, i, text s)::z       => be w (k + s.length) (out ++ s) z
-- flatten line = text " "
| w, k, out, (true,  i, line)::z      => be w (k + 1) (out ++ " ") z
| w, k, out, (false, i, line)::z      => be w i ((out ++ "\n").pushn ' ' i) z
-- flatten (group f) = flatten f
| w, k, out, (true,  i, group f)::z   => be w k out ((true, i, f)::z)
| w, k, out, (false, i, group f)::z   =>
  let r := spaceUptoLine' ((true, i, f) :: z) (w-k);
  if r.space > w-k then be w k out ((false, i, f)::z) else be w k out ((true, i, f)::z)

@[inline] def bracket (l : String) (f : Format) (r : String) : Format :=
group (nest l.length $ l ++ f ++ r)

@[inline] def paren (f : Format) : Format :=
bracket "(" f ")"

@[inline] def sbracket (f : Format) : Format :=
bracket "[" f "]"

def defIndent  := 2
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

@[export lean_format_pretty]
def prettyAux (f : Format) (w : Nat := defWidth) : String :=
be w 0 "" [(false, 0, f)]

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
| [],    sep  => nil
| [a],   sep => format a
| a::as, sep => format a ++ sep ++ Format.joinSep as sep

def Format.prefixJoin {α : Type u} [HasFormat α] (pre : Format) : List α → Format
| []    => nil
| a::as => pre ++ format a ++ Format.prefixJoin as

def Format.joinSuffix {α : Type u} [HasFormat α] : List α → Format → Format
| [],    suffix => nil
| a::as, suffix => format a ++ suffix ++ Format.joinSuffix as suffix

def List.format {α : Type u} [HasFormat α] : List α → Format
| [] => "[]"
| xs => sbracket $ Format.joinSep xs ("," ++ line)

instance listHasFormat {α : Type u} [HasFormat α] : HasFormat (List α) :=
⟨List.format⟩

instance arrayHasFormat {α : Type u} [HasFormat α] : HasFormat (Array α) :=
⟨fun a => "#" ++ fmt a.toList⟩

def Option.format {α : Type u} [HasFormat α] : Option α → Format
| none   => "none"
| some a => "some " ++ fmt a

instance optionHasFormat {α : Type u} [HasFormat α] : HasFormat (Option α) :=
⟨Option.format⟩

instance prodHasFormat {α : Type u} {β : Type v} [HasFormat α] [HasFormat β] : HasFormat (Prod α β) :=
⟨fun ⟨a, b⟩ => paren $ format a ++ "," ++ line ++ format b⟩

def Format.joinArraySep {α : Type u} [HasFormat α] (a : Array α) (sep : Format) : Format :=
a.iterate nil (fun i a r => if i.val > 0 then r ++ sep ++ format a else r ++ format a)

instance natHasFormat : HasFormat Nat       := ⟨fun n => toString n⟩
instance uint16HasFormat : HasFormat UInt16 := ⟨fun n => toString n⟩
instance uint32HasFormat : HasFormat UInt32 := ⟨fun n => toString n⟩
instance uint64HasFormat : HasFormat UInt64 := ⟨fun n => toString n⟩
instance usizeHasFormat : HasFormat USize   := ⟨fun n => toString n⟩
instance nameHasFormat : HasFormat Name     := ⟨fun n => n.toString⟩

protected def Format.repr : Format → Format
| nil => "Format.nil"
| line => "Format.line"
| text s   => paren $ "Format.text" ++ line ++ repr s
| nest n f   => paren $ "Format.nest" ++ line ++ repr n ++ line ++ Format.repr f
| append f₁ f₂ => paren $ "Format.append " ++ line ++ Format.repr f₁ ++ line ++ Format.repr f₂
| group f      => paren $ "Format.group" ++ line ++ Format.repr f


instance formatHasToString : HasToString Format := ⟨Format.pretty⟩

instance : HasRepr Format := ⟨Format.pretty ∘ Format.repr⟩

def formatDataValue : DataValue → Format
| DataValue.ofString v => format (repr v)
| DataValue.ofBool v   => format v
| DataValue.ofName v   => "`" ++ format v
| DataValue.ofNat v    => format v
| DataValue.ofInt v    => format v

instance dataValueHasFormat : HasFormat DataValue := ⟨formatDataValue⟩

def formatEntry : Name × DataValue → Format
| (n, v) => format n ++ " := " ++ format v

instance entryHasFormat : HasFormat (Name × DataValue) := ⟨formatEntry⟩

def formatKVMap (m : KVMap) : Format :=
sbracket (Format.joinSep m.entries ", ")

instance kvMapHasFormat : HasFormat KVMap := ⟨formatKVMap⟩

end Lean

def String.toFormat (s : String) : Lean.Format :=
Lean.Format.joinSep (s.splitOn "\n") Lean.Format.line
