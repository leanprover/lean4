/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Init.Data.Int.Basic
public import Init.Data.String.Bootstrap
import Init.Control.State
import Init.Data.Nat.Bitwise.Basic

public section

namespace Std

/--
Determines how groups should have linebreaks inserted when the text would overfill its remaining
space.

- `allOrNone` will make a linebreak on every `Format.line` in the group or none of them.
  ```
  [1,
   2,
   3]
  ```
- `fill` will only make linebreaks on as few `Format.line`s as possible:
  ```
  [1, 2,
   3]
  ```
-/
inductive Format.FlattenBehavior where
  /--
  Either all `Format.line`s in the group will be newlines, or all of them will be spaces.
  -/
  | allOrNone
  /--
  As few `Format.line`s in the group as possible will be newlines.
  -/
  | fill
  deriving Inhabited, BEq

open Format in
/--
A representation of a set of strings, in which the placement of newlines and indentation differ.

Given a specific line width, specified in columns, the string that uses the fewest lines can be
selected.

The pretty-printing algorithm is based on Wadler's paper
[_A Prettier Printer_](https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf).
-/
inductive Format where
  /-- The empty format. -/
  | nil                 : Format
  /--
  A position where a newline may be inserted if the current group does not fit within the allotted
  column width.
  -/
  | line                : Format
  /--
  `align` tells the formatter to pad with spaces to the current indentation level, or else add a
  newline if we are already at or past the indent. No newline is added at the start of a row that
  is already at the indentation level, since that would leave a blank row of whitespace.

  If `force` is true, then it will pad to the indent even if it is in a flattened group.

  Example:
  ```lean example
  open Std Format in
  #eval IO.println (nest 2 <| "." ++ align ++ "a" ++ line ++ "b")
  ```
  ```lean output
  . a
    b
  ```
  -/
  | align (force : Bool) : Format
  /--
  A node containing a plain string.

  If the string contains newlines, the formatter emits them and then indents to the current level.
  -/
  | text                : String → Format
  /--
  `nest indent f` increases the current indentation level by `indent` while rendering `f`.

  Example:
  ```lean example
  open Std Format in
  def fmtList (l : List Format) : Format :=
    let f := joinSep l  ("," ++ Format.line)
    group (nest 1 <| "[" ++ f ++ "]")
  ```

  This will be written all on one line, but if the text is too large, the formatter will put in
  linebreaks after the commas and indent later lines by 1.
  -/
  | nest (indent : Int) (f : Format) : Format
  /-- Concatenation of two `Format`s. -/
  | append : Format → Format → Format
  /-- Creates a new flattening group for the given inner `Format`.  -/
  | group : Format → (behavior : FlattenBehavior := FlattenBehavior.allOrNone) → Format
  /-- Used for associating auxiliary information (e.g. `Expr`s) with `Format` objects. -/
  | tag : Nat → Format → Format
  deriving Inhabited

namespace Format

/-- Checks whether the given format contains no characters. -/
def isEmpty : Format → Bool
  | nil          => true
  | line         => false
  | align _      => true
  | text msg     => msg == ""
  | nest _ f     => f.isEmpty
  | append f₁ f₂ => f₁.isEmpty && f₂.isEmpty
  | group f _    => f.isEmpty
  | tag _ f      => f.isEmpty

/--
Creates a group in which as few `Format.line`s as possible are rendered as newlines.

This is an alias for `Format.group`, with `FlattenBehavior` set to `fill`.
-/
def fill (f : Format) : Format :=
  group f (behavior := FlattenBehavior.fill)

instance : Append Format     := ⟨Format.append⟩
instance : Coe String Format := ⟨text⟩

/--
Concatenates a list of `Format`s with `++`.
-/
def join (xs : List Format) : Format :=
  xs.foldl (·++·) ""

/--
Checks whether a `Format` is the constructor `Format.nil`.

This does not check whether the resulting rendered strings are always empty. To do that, use
`Format.isEmpty`.
-/
def isNil : Format → Bool
  | nil => true
  | _   => false

private inductive AlignAction where
  | pad (n : Nat)
  | newline

/--
The action an `align` at indentation level `indent` takes when the next output would be emitted at
column `col`.

`be` renders by this, `spaceUptoLine` measures by it, and `vetoFlatten` looks ahead with it. They
must all decide alike, or a group is measured at a width it never renders at.
-/
@[inline] private def alignAction (col : Nat) (indent : Int) : AlignAction :=
  if col < indent then .pad (indent - col).toNat else .newline

private structure SpaceResult where
  foundLine              : Bool := false
  foundFlattenedHardLine : Bool := false
  space                  : Nat  := 0
  deriving Inhabited

/-- `col` is the column the remainder is measured from; `w` is the line width. -/
@[inline] private def merge (w : Nat) (col : Nat) (r₁ : SpaceResult) (r₂ : Nat → SpaceResult) : SpaceResult :=
  if col + r₁.space > w || r₁.foundLine then
    r₁
  else
    let r₂ := r₂ (col + r₁.space);
    { r₂ with space := r₁.space + r₂.space }

/-- The space `f` needs up to its next line break, at line width `w`, rendered at indentation level
`indent` starting from column `col` -- the two quantities `be` compares. -/
private def spaceUptoLine (w : Nat) : Format → Bool → Int → Nat → SpaceResult
  | nil,          _,       _,      _   => {}
  | line,         flatten, _,      _   => if flatten then { space := 1 } else { foundLine := true }
  | align force,  flatten, indent, col =>
    if flatten && !force then {}
    else
      match alignAction col indent with
      | .pad n   => { space := n }
      | .newline => { foundLine := true }
  | text s,       flatten, _,      _   =>
    let p := String.Internal.posOf s '\n'
    let off := String.Internal.offsetOfPos s p
    { foundLine := p != s.rawEndPos, foundFlattenedHardLine := flatten && p != s.rawEndPos, space := off }
  | append f₁ f₂, flatten, indent, col =>
    merge w col (spaceUptoLine w f₁ flatten indent col) (spaceUptoLine w f₂ flatten indent)
  | nest n f,     flatten, indent, col => spaceUptoLine w f flatten (indent + n) col
  | group f _,    _,       indent, col => spaceUptoLine w f true indent col
  | tag _ f,      flatten, indent, col => spaceUptoLine w f flatten indent col

private structure WorkItem where
  f : Format
  indent : Int
  activeTags : Nat

/--
A directive indicating whether a given work group is able to be flattened.

- `allow` indicates that the group is allowed to be flattened; its argument is `true` if
  there is sufficient space for it to be flattened (and so it should be), or `false` if not.
- `disallow` means that this group should not be flattened irrespective of space concerns.
  This is used at levels of a `Format` outside of any flattening groups. It is necessary to track
  this so that, after a hard line break, we know whether to try to flatten the next line.
-/
inductive FlattenAllowability where
  | allow (fits : Bool)
  | disallow
  deriving BEq

/-- Whether the given directive indicates that flattening should occur. -/
def FlattenAllowability.shouldFlatten : FlattenAllowability → Bool
  | allow true => true
  | _ => false

private structure WorkGroup where
  fla   : FlattenAllowability
  flb   : FlattenBehavior
  items : List WorkItem

private partial def spaceUptoLine' (w : Nat) : List WorkGroup → Nat → SpaceResult
  |   [],                         _   => {}
  |   { items := [],    .. }::gs, col => spaceUptoLine' w gs col
  | g@{ items := i::is, .. }::gs, col =>
    merge w col
      (spaceUptoLine w i.f g.fla.shouldFlatten i.indent col)
      (spaceUptoLine' w ({ g with items := is }::gs))

/--
A monad that can be used to incrementally render `Format` objects.
-/
class MonadPrettyFormat (m : Type → Type) where
  /--
  Emits the string `s`.
  -/
  pushOutput (s : String) : m Unit
  /--
  Emits a newline followed by `indent` columns of indentation.
  -/
  pushNewline (indent : Nat) : m Unit
  /--
  Gets the current column at which the next string will be emitted.
  -/
  currColumn : m Nat
  /--
  Starts a region tagged with `tag`.
  -/
  startTag (tag : Nat) : m Unit
  /--
  Exits the scope of `count` opened tags.
  -/
  endTags (count : Nat) : m Unit
open MonadPrettyFormat

private def pushGroup (flb : FlattenBehavior) (items : List WorkItem) (gs : List WorkGroup) (w : Nat)
    (colOffset : Nat := 0) [Monad m] [MonadPrettyFormat m] : m (List WorkGroup) := do
  -- `colOffset` is output the caller emits before the group starts; charging it to the column keeps
  -- the group measured against the real line width
  let k  := (← currColumn) + colOffset
  -- Flatten group if it + the remainder (gs) fits in the remaining space. For `fill`, measure only up to the next (ungrouped) line break.
  let g  := { fla := .allow (flb == FlattenBehavior.allOrNone), flb := flb, items := items : WorkGroup }
  let r  := spaceUptoLine' w [g] k
  let r' := merge w k r (spaceUptoLine' w gs)
  -- Prevent flattening if any item contains a hard line break, except within `fill` if it is ungrouped (=> unflattened)
  return { g with fla := .allow (!r.foundFlattenedHardLine && k + r'.space <= w) }::gs

/--
The indentation level of the next output-producing work item, if it is a forced `align`.

Structure is decomposed as in `be` and anything emitting nothing is skipped; anything else stops the
search. The search crosses into the enclosing groups `gs`, since the next item to render is often
the first item of one of them, and past a `group`, which drops an unforced `align` when flattened
but renders a forced one either way.
-/
private partial def nextForcedAlign? : List WorkItem → List WorkGroup → Option Int
  | [], [] => none
  | [], g :: gs => nextForcedAlign? g.items gs
  | i :: is, gs =>
    match i.f with
    | nil => nextForcedAlign? is gs
    | text s => if String.Internal.isEmpty s then nextForcedAlign? is gs else none
    | append f₁ f₂ => nextForcedAlign? ({ i with f := f₁ } :: { i with f := f₂ } :: is) gs
    | nest n f => nextForcedAlign? ({ i with f, indent := i.indent + n } :: is) gs
    | tag _ f => nextForcedAlign? ({ i with f } :: is) gs
    | group f _ => nextForcedAlign? ({ i with f } :: is) gs
    | align true => some i.indent
    | align false => nextForcedAlign? is gs
    | _ => none

/--
Whether a `line` about to be flattened into a space at column `k` must break instead: the forced
`align` that follows it would break right after that space, stranding it as trailing whitespace.
-/
@[inline] private def vetoFlatten (k : Nat) (is : List WorkItem) (gs : List WorkGroup) : Bool :=
  match nextForcedAlign? is gs with
  | some indent =>
    match alignAction (k + 1) indent with
    | .newline => true
    | .pad _   => false
  | none => false

private partial def be (w : Nat) [Monad m] [MonadPrettyFormat m] (fresh : Bool) : List WorkGroup → m Unit
  | []                           => pure ()
  |   { items := [],    .. }::gs => be w fresh gs
  | g@{ items := i::is, .. }::gs => do
    let gs' (is' : List WorkItem) := { g with items := is' }::gs;
    match i.f with
    | nil =>
      endTags i.activeTags
      be w fresh (gs' is)
    | tag t f =>
      startTag t
      be w fresh (gs' ({ i with f, activeTags := i.activeTags + 1 }::is))
    | append f₁ f₂ => be w fresh (gs' ({ i with f := f₁, activeTags := 0 }::{ i with f := f₂ }::is))
    | nest n f => be w fresh (gs' ({ i with f, indent := i.indent + n }::is))
    | text s =>
      let p := String.Internal.posOf s '\n'
      if p == s.rawEndPos then
        pushOutput s
        endTags i.activeTags
        be w (fresh && String.Internal.isEmpty s) (gs' is)
      else
        pushOutput (String.Internal.extract s {} p)
        pushNewline i.indent.toNat
        let is := { i with f := text (String.Internal.extract s (String.Internal.next s p) s.rawEndPos) }::is
        -- after a hard line break, re-evaluate whether to flatten the remaining group
        -- note that we shouldn't start flattening after a hard break outside a group
        if g.fla == .disallow then
          be w true (gs' is)
        else
          pushGroup g.flb is gs w >>= be w true
    | line =>
      match g.flb with
      | FlattenBehavior.allOrNone =>
        if g.fla.shouldFlatten then
          if vetoFlatten (← currColumn) is gs then
            pushNewline i.indent.toNat
            endTags i.activeTags
            -- this `line` broke against the group's own decision, so the rest of the group was
            -- measured from a column it is no longer at: re-decide, as a hard line break does
            pushGroup g.flb is gs w >>= be w true
          else
            -- flatten line = text " "
            pushOutput " "
            endTags i.activeTags
            be w false (gs' is)
        else
          pushNewline i.indent.toNat
          endTags i.activeTags
          be w true (gs' is)
      | FlattenBehavior.fill =>
        let breakHere := do
          pushNewline i.indent.toNat
          -- make new `fill` group and recurse
          endTags i.activeTags
          pushGroup FlattenBehavior.fill is gs w >>= be w true
        -- if preceding fill item fit in a single line, try to fit next one too
        if g.fla.shouldFlatten then
          let gs'@(g'::_) ← pushGroup FlattenBehavior.fill is gs w
            (colOffset := String.Internal.length " ")
            | panic "unreachable"
          if g'.fla.shouldFlatten && !vetoFlatten (← currColumn) is gs then
            pushOutput " "
            endTags i.activeTags
            be w false gs'  -- TODO: use `return`
          else
            breakHere
        else
          breakHere
    | align force =>
      if g.fla.shouldFlatten && !force then
        -- flatten (align false) = nil
        endTags i.activeTags
        be w fresh (gs' is)
      else
        let k ← currColumn
        match alignAction k i.indent with
        | .pad n =>
          -- padding emits only spaces, so a row that was whitespace-only still is
          pushOutput (String.Internal.pushn "" ' ' n)
          endTags i.activeTags
          be w fresh (gs' is)
        | .newline =>
          -- a row that is still whitespace-only and already at the indentation level would be left
          -- blank by a newline
          if k != i.indent || !fresh then
            pushNewline i.indent.toNat
          endTags i.activeTags
          -- the rest of the group was measured from a column this break just left
          if g.fla == .disallow then
            be w true (gs' is)
          else
            pushGroup g.flb is gs w >>= be w true
    | group f flb =>
      if g.fla.shouldFlatten then
        -- flatten (group f) = flatten f
        be w fresh (gs' ({ i with f }::is))
      else
        pushGroup flb [{ i with f }] (gs' is) w >>= be w fresh

/- Render the given `f : Format` with a line width of `w`.
`indent` is the starting amount to indent each line by. -/
/--
Renders a `Format` using effects in the monad `m`, using the methods of `MonadPrettyFormat`.

Each line is emitted as soon as it is rendered, rather than waiting for the entire document to be
rendered.
* `w`: the total width
* `indent`: the initial indentation to use for wrapped lines (subsequent wrapping may increase the
  indentation)
-/
def prettyM (f : Format) (w : Nat) (indent : Nat := 0) [Monad m] [MonadPrettyFormat m] : m Unit :=
  be w true [{ flb := FlattenBehavior.allOrNone, fla := .disallow, items := [{ f := f, indent, activeTags := 0 }]}]

/--
Creates a format `l ++ f ++ r` with a flattening group, nesting the contents by the length of `l`.

The group's `FlattenBehavior` is `allOrNone`; for `fill` use `Std.Format.bracketFill`.
-/
@[inline] def bracket (l : String) (f : Format) (r : String) : Format :=
  group (nest (String.Internal.length l) $ l ++ f ++ r)

/--
Creates the format `"(" ++ f ++ ")"` with a flattening group, nesting by one space.
-/
@[inline] def paren (f : Format) : Format :=
  bracket "(" f ")"

/--
Creates the format `"[" ++ f ++ "]"` with a flattening group, nesting by one space.

`sbracket` is short for “square bracket”.
-/
@[inline] def sbracket (f : Format) : Format :=
  bracket "[" f "]"

/--
Creates a format `l ++ f ++ r` with a flattening group, nesting the contents by the length of `l`.

The group's `FlattenBehavior` is `fill`; for `allOrNone` use `Std.Format.bracket`.
-/
@[inline] def bracketFill (l : String) (f : Format) (r : String) : Format :=
  fill (nest (String.Internal.length l) $ l ++ f ++ r)

/-- The default indentation level, which is two spaces. -/
def defIndent  := 2
def defUnicode := true
/-- The default width of the targeted output, which is 120 columns. -/
def defWidth   := 120

/--
Increases the indentation level by the default amount.
-/
def nestD (f : Format) : Format :=
  nest defIndent f

/-- Insert a newline and then `f`, all nested by the default indent amount. -/
def indentD (f : Format) : Format :=
  nestD (Format.line ++ f)

/-- State for formatting a pretty string. -/
private structure State where
  out    : String := ""
  column : Nat    := 0

private instance : MonadPrettyFormat (StateM State) where
  -- We avoid a structure instance update, and write these functions using pattern matching because of issue #316
  pushOutput s       := modify fun ⟨out, col⟩ => ⟨String.Internal.append out s, col + (String.Internal.length s)⟩
  pushNewline indent := modify fun ⟨out, _⟩ => ⟨String.Internal.append out (String.Internal.pushn "\n" ' ' indent), indent⟩
  currColumn         := return (← get).column
  startTag _         := return ()
  endTags _          := return ()

/--
Renders a `Format` to a string.
* `width`: the total width
* `indent`: the initial indentation to use for wrapped lines
  (subsequent wrapping may increase the indentation)
* `column`: begin the first line wrap `column` characters earlier than usual
  (this is useful when the output String will be printed starting at `column`)
-/
def pretty (f : Format) (width : Nat := defWidth) (indent : Nat := 0) (column := 0) : String :=
  let act : StateM State Unit := prettyM f width indent
  State.out <| act.run (State.mk "" column) |>.snd

end Format

/--
Specifies a “user-facing” way to convert from the type `α` to a `Format` object. There is no
expectation that the resulting string is valid code.

The `Repr` class is similar, but the expectation is that instances produce valid Lean code.
-/
class ToFormat (α : Type u) where
  /--
  Converts a value to a `Format` object, with no expectation that the resulting string is valid
  code.
  -/
  format : α → Format

export ToFormat (format)

-- note: must take precedence over the above instance to avoid premature formatting
instance : ToFormat Format where
  format f := f

instance : ToFormat String where
  format s := Format.text s

/--
Intercalates the given list with the given `sep` format.

The list items are formatting using `ToFormat.format`.
-/
def Format.joinSep {α : Type u} [ToFormat α] : List α → Format → Format
  | [],    _   => nil
  | [a],   _   => format a
  | a::as, sep => as.foldl (· ++ sep ++ format ·) (format a)

/--
Concatenates the given list after prepending `pre` to each element.

The list items are formatting using `ToFormat.format`.
-/
def Format.prefixJoin {α : Type u} [ToFormat α] (pre : Format) : List α → Format
  | []    => nil
  | a::as => as.foldl (· ++ pre ++ format ·) (pre ++ format a)

/--
Concatenates the given list after appending the given suffix to each element.

The list items are formatting using `ToFormat.format`.
-/

def Format.joinSuffix {α : Type u} [ToFormat α] : List α → Format → Format
  | [],    _      => nil
  | a::as, suffix => as.foldl (· ++ format · ++ suffix) (format a ++ suffix)

end Std
