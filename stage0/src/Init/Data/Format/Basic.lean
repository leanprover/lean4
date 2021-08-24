/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Control.State
import Init.Data.Int.Basic
import Init.Data.String.Basic

namespace Std

inductive Format.FlattenBehavior where
  | allOrNone
  | fill
  deriving Inhabited, BEq

open Format in
inductive Format where
  | nil                 : Format
  | line                : Format
  | text                : String → Format
  | nest (indent : Int) : Format → Format
  | append              : Format → Format → Format
  | group               : Format → (behavior : FlattenBehavior := FlattenBehavior.allOrNone) → Format
  /- Used for associating auxiliary information (e.g. `Expr`s) with `Format` objects. -/
  | tag                 : Nat → Format → Format
  deriving Inhabited

namespace Format
def fill (f : Format) : Format :=
  group f (behavior := FlattenBehavior.fill)

@[export lean_format_append]
protected def appendEx (a b : Format) : Format :=
  append a b

@[export lean_format_group]
protected def groupEx : Format → Format :=
  group

instance : Append Format     := ⟨Format.append⟩
instance : Coe String Format := ⟨text⟩

def join (xs : List Format) : Format :=
  xs.foldl (·++·) ""

def isNil : Format → Bool
  | nil => true
  | _   => false

private structure SpaceResult where
  foundLine              : Bool := false
  foundFlattenedHardLine : Bool := false
  space                  : Nat  := 0
  deriving Inhabited

@[inline] private def merge (w : Nat) (r₁ : SpaceResult) (r₂ : Nat → SpaceResult) : SpaceResult :=
  if r₁.space > w || r₁.foundLine then
    r₁
  else
    let r₂ := r₂ (w - r₁.space);
    { r₂ with space := r₁.space + r₂.space }

private def spaceUptoLine : Format → Bool → Nat → SpaceResult
  | nil,          flatten, w => {}
  | line,         flatten, w => if flatten then { space := 1 } else { foundLine := true }
  | text s,       flatten, w =>
    let p := s.posOf '\n';
    let off := s.offsetOfPos p;
    { foundLine := p != s.bsize, foundFlattenedHardLine := flatten && p != s.bsize, space := off }
  | append f₁ f₂, flatten, w => merge w (spaceUptoLine f₁ flatten w) (spaceUptoLine f₂ flatten)
  | nest _ f,     flatten, w => spaceUptoLine f flatten w
  | group f _,    _,       w => spaceUptoLine f true w
  | tag _ f,      flatten, w => spaceUptoLine f flatten w

private structure WorkItem where
  f : Format
  indent : Int
  activeTags : Nat

private structure WorkGroup where
  flatten : Bool
  flb     : FlattenBehavior
  items   : List WorkItem

private partial def spaceUptoLine' : List WorkGroup → Nat → SpaceResult
  |   [],                         w => {}
  |   { items := [],    .. }::gs, w => spaceUptoLine' gs w
  | g@{ items := i::is, .. }::gs, w => merge w (spaceUptoLine i.f g.flatten w) (spaceUptoLine' ({ g with items := is }::gs))

/-- A monad in which we can pretty-print `Format` objects. -/
class MonadPrettyFormat (m : Type → Type) where
  pushOutput (s : String)    : m Unit
  pushNewline (indent : Nat) : m Unit
  currColumn                 : m Nat
  /-- Start a scope tagged with `n`. -/
  startTag                   : Nat → m Unit
  /-- Exit the scope of `n`-many opened tags. -/
  endTags                    : Nat → m Unit
open MonadPrettyFormat

private def pushGroup (flb : FlattenBehavior) (items : List WorkItem) (gs : List WorkGroup) (w : Nat) [Monad m] [MonadPrettyFormat m] : m (List WorkGroup) := do
  let k  ← currColumn
  -- Flatten group if it + the remainder (gs) fits in the remaining space. For `fill`, measure only up to the next (ungrouped) line break.
  let g  := { flatten := flb == FlattenBehavior.allOrNone, flb := flb, items := items : WorkGroup }
  let r  := spaceUptoLine' [g] (w-k)
  let r' := merge (w-k) r (spaceUptoLine' gs);
  -- Prevent flattening if any item contains a hard line break, except within `fill` if it is ungrouped (=> unflattened)
  return { g with flatten := !r.foundFlattenedHardLine && r'.space <= w-k }::gs

private partial def be (w : Nat) [Monad m] [MonadPrettyFormat m] : List WorkGroup → m Unit
  | []                           => pure ()
  |   { items := [],    .. }::gs => be w gs
  | g@{ items := i::is, .. }::gs => do
    let gs' (is' : List WorkItem) := { g with items := is' }::gs;
    match i.f with
    | nil =>
      endTags i.activeTags
      be w (gs' is)
    | tag t f =>
      startTag t
      be w (gs' ({ i with f, activeTags := i.activeTags + 1 }::is))
    | append f₁ f₂ => be w (gs' ({ i with f := f₁, activeTags := 0 }::{ i with f := f₂ }::is))
    | nest n f => be w (gs' ({ i with f, indent := i.indent + n }::is))
    | text s =>
      let p := s.posOf '\n'
      if p == s.bsize then
        pushOutput s
        endTags i.activeTags
        be w (gs' is)
      else
        pushOutput (s.extract 0 p)
        pushNewline i.indent.toNat
        let is := { i with f := text (s.extract (s.next p) s.bsize) }::is
        -- after a hard line break, re-evaluate whether to flatten the remaining group
        pushGroup g.flb is gs w >>= be w
    | line =>
      match g.flb with
      | FlattenBehavior.allOrNone =>
        if g.flatten then
          -- flatten line = text " "
          pushOutput " "
          endTags i.activeTags
          be w (gs' is)
        else
          pushNewline i.indent.toNat
          endTags i.activeTags
          be w (gs' is)
      | FlattenBehavior.fill =>
        let breakHere := do
          pushNewline i.indent.toNat
          -- make new `fill` group and recurse
          endTags i.activeTags
          pushGroup FlattenBehavior.fill is gs w >>= be w
        -- if preceding fill item fit in a single line, try to fit next one too
        if g.flatten then
          let gs'@(g'::_) ← pushGroup FlattenBehavior.fill is gs (w - " ".length)
            | panic "unreachable"
          if g'.flatten then
            pushOutput " ";
            endTags i.activeTags
            be w gs'  -- TODO: use `return`
          else
            breakHere
        else
          breakHere
    | group f flb =>
      if g.flatten then
        -- flatten (group f) = flatten f
        be w (gs' ({ i with f }::is))
      else
        pushGroup flb [{ i with f }] (gs' is) w >>= be w

def prettyM (f : Format) (w : Nat) (indent : Nat := 0) [Monad m] [MonadPrettyFormat m] : m Unit :=
  be w [{ flb := FlattenBehavior.allOrNone, flatten := false, items := [{ f := f, indent, activeTags := 0 }]}]

@[inline] def bracket (l : String) (f : Format) (r : String) : Format :=
  group (nest l.length $ l ++ f ++ r)

@[inline] def paren (f : Format) : Format :=
  bracket "(" f ")"

@[inline] def sbracket (f : Format) : Format :=
  bracket "[" f "]"

@[inline] def bracketFill (l : String) (f : Format) (r : String) : Format :=
  fill (nest l.length $ l ++ f ++ r)

def defIndent  := 2
def defUnicode := true
def defWidth   := 120

def nestD (f : Format) : Format :=
  nest defIndent f

def indentD (f : Format) : Format :=
  nestD (Format.line ++ f)

private structure State where
  out    : String := ""
  column : Nat    := 0

instance : MonadPrettyFormat (StateM State) where
  -- We avoid a structure instance update, and write these functions using pattern matching because of issue #316
  pushOutput s       := modify fun ⟨out, col⟩ => ⟨out ++ s, col + s.length⟩
  pushNewline indent := modify fun ⟨out, col⟩ => ⟨out ++ "\n".pushn ' ' indent, indent⟩
  currColumn         := return (←get).column
  startTag n         := return ()
  endTags n          := return ()

/-- Pretty-print a `Format` object as a string with expected width `w`. -/
@[export lean_format_pretty]
def pretty (f : Format) (w : Nat := defWidth) : String :=
  let act: StateM State Unit := prettyM f w
  act {} |>.snd.out

end Format

class ToFormat (α : Type u) where
  format : α → Format

export ToFormat (format)

-- note: must take precendence over the above instance to avoid premature formatting
instance : ToFormat Format where
  format f := f

instance : ToFormat String where
  format s := Format.text s

def Format.joinSep {α : Type u} [ToFormat α] : List α → Format → Format
  | [],    sep => nil
  | [a],   sep => format a
  | a::as, sep => format a ++ sep ++ joinSep as sep

def Format.prefixJoin {α : Type u} [ToFormat α] (pre : Format) : List α → Format
  | []    => nil
  | a::as => pre ++ format a ++ prefixJoin pre as

def Format.joinSuffix {α : Type u} [ToFormat α] : List α → Format → Format
  | [],    suffix => nil
  | a::as, suffix => format a ++ suffix ++ joinSuffix as suffix

end Std
