/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Init.Data.Hashable
import Init.Data.Array

public section

namespace Lean.Fmt

/--
Document height at which the format document is memoized when formatting.
Time-complexity-wise, this is sound because the format document is a binary tree, and so its height
bounds the amount of nodes in the tree.
-/
def memoHeightLimit : Nat := 6

/--
Computes the memoization height of a node in the format document with a child memoization height
of `memoHeight`.
-/
def nextMemoHeight (memoHeight : Nat) : Nat :=
  if memoHeight = 0 then
    memoHeightLimit
  else
    memoHeight - 1

/--
Bitmap that tracks whether there is a `Doc.full` node on the same line *before* the current document
that is being resolved by the formatter or on the same line *after* the current document.

In the formatter, we case split on the fullness state in several places and then prune subtrees
of the search when we notice that they are inconsistent with the actual document current being
resolved.
-/
@[expose]
def FullnessState := UInt8
  deriving BEq, Hashable

@[inline]
def FullnessState.mk (isFullBefore : Bool) (isFullAfter : Bool) : FullnessState :=
  (isFullBefore.toUInt8 <<< 1) ||| isFullAfter.toUInt8

@[inline]
def FullnessState.isFullBefore (s : FullnessState) : Bool :=
  let s : UInt8 := s
  (s &&& 0b10) == 1

@[inline]
def FullnessState.isFullAfter (s : FullnessState) : Bool :=
  let s : UInt8 := s
  (s &&& 0b1) == 1

@[inline]
def FullnessState.setFullBefore (s : FullnessState) (isFullBefore : Bool) : FullnessState :=
  let s : UInt8 := s
  (s &&& (0b11111101 : UInt8)) ||| (isFullBefore.toUInt8 <<< 1)

@[inline]
def FullnessState.setFullAfter (s : FullnessState) (isFullAfter : Bool) : FullnessState :=
  let s : UInt8 := s
  (s &&& (0b11111110 : UInt8)) ||| isFullAfter.toUInt8

/-- Whether resolving a document is guaranteed to fail in the given `FullnessState`. -/
abbrev FailureCond := FullnessState → Bool

/-- Input document consumed by the formatter, which chooses an optimal rendering of the document. -/
inductive Doc where
  /--
  Indicates that rendering this document is impossible. The formatter will always choose a rendering
  of the document without `failure` nodes if one is available.
  This is sometimes useful when defining custom combinators on a pre-existing document.

  Used when `flatten`ing a `newline none`.

  Example:
  ```
  either (text "a") failure
  ```
  produces
  ```
  a
  ```
  -/
  | failure
  /--
  Designates a newline in the document.

  Within a `flatten` node, all `newline (some flattened)` nodes are replaced with `text flattened`
  and all `newline none` nodes are replaced with `failure`, i.e. `newline none` can never be
  flattened.

  Any newline that is not flattened by an outer `flatten` node will yield `\n` followed by
  an amount of spaces corresponding to the current level of indentation as set by
  `indent`, `align` and `reset` in the rendered document.

  `flattened?` is irrelevant during formatting: before formatting, a preprocessing step eliminates
  all `flatten` nodes by replacing all `newline flattened?` nodes within each `flatten` node.

  Examples:

  ```
  indent 2
    (append
      (append
        (text "a")
        (newline (some " ")))
      (text "b"))
  ```
  produces
  ```
  a
    b
  ```
  ---
  ```
  flatten
    (append
      (append
        (text "a")
        (newline (some " ")))
      (text "b"))
  ```
  produces
  ```
  a b
  ```
  ---
  ```
  flatten
    (append
      (append
        (text "a")
        (newline none))
      (text "b"))
  ```
  produces
  ```
  <no output>
  ```
  -/
  | newline (flattened? : Option String)
  /--
  Designates a piece of text without newlines in the document.
  `text` nodes are never broken apart by the formatter.

  The formatter will never choose a rendering where a `text` node is placed on the same line
  after a `full` node.

  Examples:

  ```
  text "foo"
  ```
  produces
  ```
  foo
  ```
  ---
  ```
  either
    (append
      (full (text "a"))
      (text "b"))
    (text "c")
  ```
  produces
  ```
  c
  ```
  -/
  | text (s : String)
  /--
  Flattens an inner document by replacing all `newline (some flattened)` nodes in the inner
  document with `text flattened` and all `newline none` nodes in the inner document with `failure`.

  `flatten` is eliminated before formatting by a preprocessing step that replaces all
  `newline flattened?` nodes within each `flatten` node.

  Examples:

  ```
  flatten
    (append
      (append
        (text "a")
        (newline (some " ")))
      (text "b"))
  ```
  produces
  ```
  a b
  ```
  ---
  ```
  flatten
    (append
      (append
        (text "a")
        (newline none))
      (text "b"))
  ```
  produces
  ```
  <no output>
  ```
  -/
  | flatten (d : Doc)
  /--
  Adds `n` to the current level of indentation within an inner document.

  When rendering a newline, the formatter produces an amount of spaces corresponding to the
  current level of indentation after the newline.

  Example:

  ```
  indent 2
    (append
      (text "a")
      (indent 2
        (append
          (append
            (text "b")
            (newline (some " ")))
          (text "c"))))
  ```
  produces
  ```
  ab
    c
  ```
  -/
  | indent (n : Nat) (d : Doc)
  /--
  Sets the current level of indentation within an inner document to the current column position
  at the position where the `align` is rendered.

  When rendering a newline, the formatter produces an amount of spaces corresponding to the
  current level of indentation after the newline.

  Example:

  ```
  append
    (text "a")
    (align
      (append
        (newline (some " "))
        (text "b")))
  ```
  produces
  ```
  a
   b
  ```
  -/
  | align (d : Doc)
  /--
  Sets the current level of indentation within an inner document to 0.

  When rendering a newline, the formatter produces an amount of spaces corresponding to the
  current level of indentation after the newline.

  Example:

  ```
  indent 2
    (append
      (unindent
        (append
          (text "a")
          (newline (some " "))))
      (text "b"))
  ```
  produces
  ```
  a
  b
  ```
  -/
  | unindent (d : Doc)
  /--
  Enforces that no text can be placed on the same line after the inner document.

  Example:

  ```
  either
    (append
      (full (text "a"))
      (text "b"))
    (text "c")
  ```
  produces
  ```
  c
  ```
  -/
  | full (d : Doc)
  /--
  Represents a document that can be rendered to one of two alternatives.

  The formatter will always choose a non-failing alternative if one is available or fail otherwise.
  When both alternatives are not failing, it chooses an optimal rendering from both alternatives.

  Examples:

  ```
  either (text "a") failure
  ```
  produces
  ```
  a
  ```
  ---
  ```
  either
    (text "a")
    (append
      (append
        (text "b")
        (newline (some " ")))
      (text "c"))
  ```
  (assuming a lawful cost function) produces
  ```
  a
  ```
  -/
  | either (a b : Doc)
  /--
  Appends the second document to the last line of the first document.

  Example:

  ```
  append
    (append
      (append
        (text "a")
        (newline (some " ")))
      (text "b"))
    (text "c")
  ```
  produces
  ```
  a
  bc
  ```
  -/
  | append (a b : Doc)
with
  /--
  Determines whether resolving the document is guaranteed to fail in the given `FullnessState`.
  -/
  @[computed_field] isFailure : Doc → FailureCond
    | .failure => fun _ => true
    | .newline .. => (·.isFullAfter)
    | .text s => fun state =>
      match state.isFullBefore, state.isFullAfter with
      | false, false => false
      | true, false => true
      | false, true => true
      | true, true => ! s.isEmpty
    | .full _ => (! ·.isFullAfter)
    -- For all of the remaining inner nodes, whether resolving the document is guaranteed
    -- to fail depends on the nodes below the inner nodes.
    | _ => fun _ => false
  @[computed_field] maxNewlineCount? : Doc → Option Nat
    | .failure => none
    | .newline .. => some 1
    | .text _
    | .flatten _ => some 0
    | .indent _ d
    | .align d
    | .unindent d
    | .full d => maxNewlineCount? d
    | .either a b => .merge (max · ·) (maxNewlineCount? a) (maxNewlineCount? b)
    | .append a b => .merge (· + ·) (maxNewlineCount? a) (maxNewlineCount? b)
  @[computed_field] memoHeight : Doc → Nat
    | .failure
    | .newline ..
    | .text _ => memoHeightLimit
    | .flatten d
    | .indent _ d
    | .align d
    | .unindent d
    | .full d =>
      let n := memoHeight d
      nextMemoHeight n
    | .either a b
    | .append a b =>
      let n := min (memoHeight a) (memoHeight b)
      nextMemoHeight n
deriving Inhabited, Repr

def Doc.maybeFlattened (d : Doc) : Doc :=
  .either d d.flatten

def Doc.nl : Doc :=
  .newline (some " ")

def Doc.break : Doc :=
  .newline (some "")

def Doc.hardNl : Doc :=
  .newline none

def Doc.oneOf (ds : Array Doc) : Doc :=
  match ds[0]? with
  | none =>
    .failure
  | some d =>
    ds[1:].foldl (init := d) fun acc d => acc.either d

def Doc.join (ds : Array Doc) : Doc :=
  match ds[0]? with
  | none =>
    .text ""
  | some d =>
    ds[1:].foldl (init := d) fun acc d => acc.append d

def Doc.joinUsing (sep : Doc) (ds : Array Doc) : Doc :=
  match ds[0]? with
  | none =>
    .text ""
  | some d =>
    ds[1:].foldl (init := d) fun acc d => acc.append sep |>.append d

instance : Append Doc where
  append d1 d2 := d1.append d2

class ToDoc (α : Type) where
  toDoc : α → Doc

instance : ToDoc Doc where
  toDoc d := d

instance : ToDoc String where
  toDoc s := .text s

syntax:max "f'!" interpolatedStr(term) : term

macro_rules
  | `(f'! $interpStr) => do interpStr.expandInterpolatedStr (← `(Doc)) (← `(ToDoc.toDoc))
