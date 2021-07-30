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

open Format

inductive Format (τ := Empty) where
  | nil {}              : Format τ
  | line {}             : Format τ
  | text                : String → Format τ
  | nest (indent : Int) : Format τ → Format τ
  | append              : Format τ → Format τ → Format τ
  | group               : Format τ → (behavior : FlattenBehavior := FlattenBehavior.allOrNone) → Format τ
  /- Used for associating auxiliary information (e.g. `Expr`s) with `Format` objects. -/
  | tag                  : τ → Format τ → Format τ
  deriving Inhabited

namespace Format

def fill (f : Format τ) : Format τ :=
  group f (behavior := FlattenBehavior.fill)

@[export lean_format_append]
protected def appendEx (a b : Format) : Format :=
  append a b

@[export lean_format_group]
protected def groupEx : Format → Format :=
  group

instance : Append (Format τ)     := ⟨Format.append⟩
instance : Coe String (Format τ) := ⟨Format.text⟩

def join (xs : List (Format τ)) : Format τ :=
  xs.foldl (·++·) ""

def isNil : Format τ → Bool
  | nil _ => true
  | _     => false

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

private def spaceUptoLine : Format τ → Bool → Nat → SpaceResult
  | nil _,        flatten, w => {}
  | line _,       flatten, w => if flatten then { space := 1 } else { foundLine := true }
  | text s,       flatten, w =>
    let p := s.posOf '\n';
    let off := s.offsetOfPos p;
    { foundLine := p != s.bsize, foundFlattenedHardLine := flatten && p != s.bsize, space := off }
  | append f₁ f₂, flatten, w => merge w (spaceUptoLine f₁ flatten w) (spaceUptoLine f₂ flatten)
  | nest _ f,     flatten, w => spaceUptoLine f flatten w
  | group f _,    _,       w => spaceUptoLine f true w
  | tag _ f,      flatten, w => spaceUptoLine f flatten w

private structure WorkItem (τ) where
  f : Format τ
  indent : Int

private structure WorkGroup (τ) where
  flatten : Bool
  flb     : FlattenBehavior
  items   : List (WorkItem τ)

private partial def spaceUptoLine' : List (WorkGroup τ) → Nat → SpaceResult
  |   [],                         w => {}
  |   { items := [],    .. }::gs, w => spaceUptoLine' gs w
  | g@{ items := i::is, .. }::gs, w => merge w (spaceUptoLine i.f g.flatten w) (spaceUptoLine' ({ g with items := is }::gs))

private structure State where
  out    : String := ""
  column : Nat    := 0

private def pushGroup (flb : FlattenBehavior) (items : List (WorkItem τ)) (gs : List (WorkGroup τ)) (w : Nat) : StateM State (List (WorkGroup τ)) := do
  let k  := (← get).column
  -- Flatten group if it + the remainder (gs) fits in the remaining space. For `fill`, measure only up to the next (ungrouped) line break.
  let g  := { flatten := flb == FlattenBehavior.allOrNone, flb := flb, items := items : WorkGroup τ }
  let r  := spaceUptoLine' [g] (w-k)
  let r' := merge (w-k) r (spaceUptoLine' gs);
  -- Prevent flattening if any item contains a hard line break, except within `fill` if it is ungrouped (=> unflattened)
  return { g with flatten := !r.foundFlattenedHardLine && r'.space <= w-k }::gs

private def pushOutput (s : String) : StateM State Unit :=
  -- We avoid a structure instance update, and write this function using pattern matching because of issue #361
  modify fun ⟨out, col⟩ => ⟨out ++ s, col + s.length⟩

private def pushNewline (indent : Nat) : StateM State Unit :=
  modify fun st => { st with out := st.out ++ "\n".pushn ' ' indent, column := indent }

private partial def be (w : Nat) : List (WorkGroup τ) → StateM State Unit
  | []                           => pure ()
  |   { items := [],    .. }::gs => be w gs
  | g@{ items := i::is, .. }::gs => do
    let gs' (is' : List (WorkItem τ)) := { g with items := is' }::gs;
    match i.f with
    | nil _ => be w (gs' is)
    | tag _ f => be w (gs' ({ i with f }::is))
    | append f₁ f₂ => be w (gs' ({ i with f := f₁ }::{ i with f := f₂ }::is))
    | nest n f => be w (gs' ({ i with f := f, indent := i.indent + n }::is))
    | text s =>
      let p := s.posOf '\n'
      if p == s.bsize then
        pushOutput s
        be w (gs' is)
      else
        pushOutput (s.extract 0 p)
        pushNewline i.indent.toNat
        let is := { i with f := s.extract (s.next p) s.bsize }::is
        -- after a hard line break, re-evaluate whether to flatten the remaining group
        pushGroup g.flb is gs w >>= be w
    | line _ =>
      match g.flb with
      | FlattenBehavior.allOrNone =>
        if g.flatten then
          -- flatten line = text " "
          pushOutput " "
          be w (gs' is)
        else
          pushNewline i.indent.toNat
          be w (gs' is)
      | FlattenBehavior.fill =>
        let breakHere := do
          pushNewline i.indent.toNat
          -- make new `fill` group and recurse
          pushGroup FlattenBehavior.fill is gs w >>= be w
        -- if preceding fill item fit in a single line, try to fit next one too
        if g.flatten then
          let gs'@(g'::_) ← pushGroup FlattenBehavior.fill is gs (w - " ".length)
            | panic "unreachable"
          if g'.flatten then
            pushOutput " ";
            be w gs'  -- TODO: use `return`
          else
            breakHere
        else
          breakHere
    | group f flb =>
      if g.flatten then
        -- flatten (group f) = flatten f
        be w (gs' ({ i with f := f }::is))
      else
        pushGroup flb [{ i with f := f }] (gs' is) w >>= be w

@[inline] def bracket (l : String) (f : Format τ) (r : String) : Format τ :=
  group (nest l.length $ l ++ f ++ r)

@[inline] def paren (f : Format τ) : Format τ :=
  bracket "(" f ")"

@[inline] def sbracket (f : Format τ) : Format τ :=
  bracket "[" f "]"

@[inline] def bracketFill (l : String) (f : Format τ) (r : String) : Format τ :=
  fill (nest l.length $ l ++ f ++ r)

def defIndent  := 2
def defUnicode := true
def defWidth   := 120

def nestD (f : Format τ) : Format τ :=
  nest defIndent f

def indentD (f : Format τ) : Format τ :=
  nestD (Format.line τ ++ f)

def pretty (f : Format τ) (w : Nat := defWidth) : String :=
  let (_, st) := be w [{ flb := FlattenBehavior.allOrNone, flatten := false, items := [{ f := f, indent := 0 }] }] {};
  st.out

@[export lean_format_pretty]
protected def prettyEx (f : Format) (w : Nat := defWidth) : String :=
  pretty f w

end Format

class ToFormat (α : Type u) (τ : Type := Empty) where
  format : α → Format τ

def format {α : Type u} (a : α) (τ : Type := Empty) [ToFormat α τ] : Format τ :=
  ToFormat.format a

-- note: must take precendence over the above instance to avoid premature formatting
instance : ToFormat (Format τ) τ where
  format f := f

instance : ToFormat String τ where
  format s := Format.text s

def Format.joinSep {α : Type u} {τ : Type} [ToFormat α τ] : List α → Format τ → Format τ
  | [],    sep => nil τ
  | [a],   sep => format a τ
  | a::as, sep => format a τ ++ sep ++ joinSep as sep

def Format.prefixJoin {α : Type u} {τ : Type} [ToFormat α τ] (pre : Format τ) : List α → Format τ
  | []    => nil τ
  | a::as => pre ++ format a τ ++ prefixJoin pre as

def Format.joinSuffix {α : Type u} {τ : Type} [ToFormat α τ] : List α → Format τ → Format τ
  | [],    suffix => nil τ
  | a::as, suffix => format a τ ++ suffix ++ joinSuffix as suffix

end Std
