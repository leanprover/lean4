/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Data.Options
universes u v

namespace Lean

namespace Format
inductive FlattenBehavior
| allOrNone
| fill

namespace FlattenBehavior
instance hasBeq : HasBeq FlattenBehavior :=
⟨fun b₁ b₂ => match b₁, b₂ with
  | allOrNone, allOrNone => true
  | fill,      fill      => true
  | _,         _         => false⟩
end FlattenBehavior
end Format

open Format

inductive Format
| nil                 : Format
| line                : Format
| text                : String → Format
| nest (indent : Int) : Format → Format
| append              : Format → Format → Format
| group               : Format → optParam FlattenBehavior FlattenBehavior.allOrNone → Format

namespace Format
def fill (f : Format) : Format :=
group f FlattenBehavior.fill

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

instance SpaceResult.inhabited : Inhabited SpaceResult :=
⟨{}⟩

@[inline] private def merge (w : Nat) (r₁ : SpaceResult) (r₂ : Nat → SpaceResult) : SpaceResult :=
if r₁.space > w || r₁.foundLine then r₁
else
  let r₂ := r₂ (w - r₁.space);
  { r₂ with space := r₁.space + r₂.space }

def spaceUptoLine : Format → Bool → Nat → SpaceResult
| nil,          flatten, w => {}
| line,         flatten, w => if flatten then { space := 1 } else { foundLine := true }
| text s,       flatten, w =>
  let p := s.posOf '\n';
  let off := s.offsetOfPos p;
  { foundLine := p != s.bsize, space := off }
| append f₁ f₂, flatten, w => merge w (spaceUptoLine f₁ flatten w) (spaceUptoLine f₂ flatten)
| nest _ f,     flatten, w => spaceUptoLine f flatten w
| group f _,    _,       w => spaceUptoLine f true w

structure WorkItem :=
(f : Format)
(indent : Int)

structure WorkGroup :=
(flatten : Bool)
(flb     : FlattenBehavior)
(items   : List WorkItem)

partial def spaceUptoLine' : List WorkGroup → Nat → SpaceResult
| [],                           w => {}
|   { items := [],    .. }::gs, w => spaceUptoLine' gs w
| g@{ items := i::is, .. }::gs, w => merge w (spaceUptoLine i.f g.flatten w) (spaceUptoLine' ({ g with items := is }::gs))

private def pushGroup (flb : FlattenBehavior) (items : List WorkItem) (gs : List WorkGroup) (w : Nat) : List WorkGroup :=
-- Flatten group if it fits in the remaining space. For `fill`, measure only up to the next (ungrouped) line break.
let g : WorkGroup := { flatten := flb == FlattenBehavior.allOrNone, flb := flb, items := items };
let r := spaceUptoLine' (g::gs) w;
{ g with flatten := r.space <= w }::gs

partial def be (w : Nat) : Nat → String → List WorkGroup → String
| k, out, []                           => out
| k, out,   { items := [],    .. }::gs => be k out gs
| k, out, g@{ items := i::is, .. }::gs =>
  let gs' (is' : List WorkItem) := { g with items := is' }::gs;
  match i.f with
  | nil => be k out (gs' is)
  | append f₁ f₂ => be k out (gs' ({ i with f := f₁ }::{ i with f := f₂ }::is))
  | nest n f => be k out (gs' ({ i with f := f, indent := i.indent + n }::is))
  | text s =>
    let p := s.posOf '\n';
    if p == s.bsize then be (k + s.length) (out ++ s) (gs' is)
    else
      let out := out ++ s.extract 0 p ++ "\n".pushn ' ' i.indent.toNat;
      let k := i.indent.toNat;
      let is := { i with f := s.extract (s.next p) s.bsize }::is;
      -- after a hard line break, re-evaluate whether to flatten the remaining group
      let gs := pushGroup g.flb is gs (w-k);
      be k out gs
  | line =>
    let g' := { g with items := is };
    let (flatten, g') := match g.flb : _ → Bool × WorkGroup with
      | FlattenBehavior.allOrNone => (g.flatten, g')
      | FlattenBehavior.fill =>
        let r := spaceUptoLine' ({ g' with flatten := false }::gs) (w-k);
        -- if preceding fill item fit in a single line, try to fit next one too
        if g.flatten && r.space <= w-k then (true, { g' with flatten := true })
        else
          -- else, try to fit it in a separate line
          let r := spaceUptoLine' ({ g' with flatten := false }::gs) w;
          (false, { g' with flatten := r.space <= w });
    if flatten then
      -- flatten line = text " "
      be (k + 1) (out ++ " ") (g'::gs)
    else
      be i.indent.toNat ((out ++ "\n").pushn ' ' i.indent.toNat) (g'::gs)
  | group f flb => if g.flatten then
      -- flatten (group f) = flatten f
      be k out (gs' ({ i with f := f }::is))
    else
      let gs := pushGroup flb [{ i with f := f }] (gs' is) (w-k);
      be k out gs

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
be w 0 "" [{ flb := FlattenBehavior.allOrNone, flatten := false, items := [{ f := f, indent := 0 }] }]

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
| group f FlattenBehavior.allOrNone => paren $ "Format.group" ++ line ++ Format.repr f
| group f FlattenBehavior.fill => paren $ "Format.fill" ++ line ++ Format.repr f


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
