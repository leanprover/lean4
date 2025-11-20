/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Init.Data.Hashable
import Init.Data.Array

/-!
Document language of the `Fmt` formatter.

This file implements the document language of 'A Pretty Expressive Printer' [1] by
Sorawee Porncharoenwase, Justin Pombrio and Emina Torlak.
This implementation is based on the Racket implementation of pretty-expressive [2].

[1] https://arxiv.org/pdf/2310.01530
[2] https://docs.racket-lang.org/pretty-expressive/
-/

public section

namespace Lean.Fmt

/--
Document height at which the formatting document is memoized when formatting.
Time-complexity-wise, this is sound because the formatting document is a binary tree, and so its
height bounds the amount of nodes in the tree.
-/
def memoHeightLimit : Nat := 6

/--
Computes the memoization height of a node in the formatting document with a child memoization height
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
of the search when we notice that they are inconsistent with the actual document currently being
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

  Used when a `flattened` document contains a `newline none`.

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

  Within `flattened`, all `newline (some f)` nodes are replaced with `text f`
  and all `newline none` nodes are replaced with `failure`, i.e. `newline none` can never be
  flattened.

  Any newline that is not flattened by an outer `flattened` node will yield `\n` followed by
  an amount of spaces corresponding to the current level of indentation as set by
  `indent`, `align` and `reset` in the rendered document.

  `f?` is irrelevant during formatting: before formatting, a preprocessing step eliminates
  all `flattened` nodes by replacing all `newline f?` nodes within each `flattened` node.

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
  flattened
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
  flattened
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
  | newline (f? : Option String)
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
  Flattens an inner document by replacing all `newline (some f)` nodes in the inner
  document with `text f` and all `newline none` nodes in the inner document with `failure`.

  `flattened` is eliminated before formatting by a preprocessing step that replaces all
  `newline f?` nodes within each `flattened` node.

  Examples:

  ```
  flattened
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
  flattened
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
  | flattened (d : Doc)
  /--
  Adds `n` to the current level of indentation within an inner document.

  When rendering a newline, the formatter produces an amount of spaces corresponding to the
  current level of indentation after the newline.

  Example:

  ```
  indented 2
    (append
      (text "a")
      (indented 2
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
  | indented (n : Nat) (d : Doc)
  /--
  Sets the current level of indentation within an inner document to the current column position
  at the position where the `aligned` is rendered.

  When rendering a newline, the formatter produces an amount of spaces corresponding to the
  current level of indentation after the newline.

  Example:

  ```
  append
    (text "a")
    (aligned
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
  | aligned (d : Doc)
  /--
  Sets the current level of indentation within an inner document to 0.

  When rendering a newline, the formatter produces an amount of spaces corresponding to the
  current level of indentation after the newline.

  Example:

  ```
  indented 2
    (append
      (unindented
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
  | unindented (d : Doc)
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
  Designates a document that can be rendered to one of two alternatives.

  The formatter will always choose a non-failing alternative if one is available or fail otherwise.
  When both alternatives are not failing, it chooses an optimal rendering from both alternatives.

  If the two subtrees of an `either` have the same structure, then this structure should be
  referentially shared between the two subtrees instead of duplicating them. This ensures that
  documents with lots of alternatives can still be formatted efficiently, as the formatter will be
  able to re-use state across these alternatives.

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
    -- `failure` always fails. All resolutions that contain `failure` can be pruned.
    | .failure => fun _ => true
    -- `newline` starts a new line, which can never be full at this point.
    -- Hence, resolutions in which `isFullAfter` is true directly after `newline` can be pruned.
    | .newline .. => (·.isFullAfter)
    | .text s => fun state =>
      match state.isFullBefore, state.isFullAfter with
      -- `text` nodes can be placed on non-full lines.
      | false, false => false
      -- `text` nodes cannot turn a line from being full to non-full.
      | true, false => true
      -- `text` nodes cannot turn a line from being non-full to full.
      | false, true => true
      -- Empty text nodes can be inserted on a full line, while non-empty text nodes cannot.
      | true, true => ! s.isEmpty
    -- `full` designates that the line is full.
    -- Hence, resolutions in which `isFullAfter` is false directly after `full` can be pruned.
    | .full _ => (! ·.isFullAfter)
    -- For all of the remaining inner nodes, whether resolving the document is guaranteed to fail
    -- depends on the child nodes below the inner node.
    | _ => fun _ => false
  /--
  Designates an overapproximation for the amount of newlines in a document.
  This is used by the formatter to choose renderings amongst multiple alternatives
  that all exceed a maximum optimality cutoff width, which bounds the total search space.
  -/
  @[computed_field] maxNewlineCount? : Doc → Option Nat
    | .failure => none
    | .newline .. => some 1
    | .text _
    | .flattened _ => some 0
    | .indented _ d
    | .aligned d
    | .unindented d
    | .full d => maxNewlineCount? d
    | .either a b => .merge (max · ·) (maxNewlineCount? a) (maxNewlineCount? b)
    | .append a b => .merge (· + ·) (maxNewlineCount? a) (maxNewlineCount? b)
  /--
  Memoization height of this document. Documents with a `memoHeight` of 0 are memoized when
  formatting.
  Time-complexity-wise, this is sound because the formatting document is a binary tree, and so its
  height bounds the amount of nodes in the tree.
  -/
  @[computed_field] memoHeight : Doc → Nat
    | .failure
    | .newline ..
    | .text _ => memoHeightLimit
    | .flattened d
    | .indented _ d
    | .aligned d
    | .unindented d
    | .full d =>
      let n := memoHeight d
      nextMemoHeight n
    | .either a b
    | .append a b =>
      let n := min (memoHeight a) (memoHeight b)
      nextMemoHeight n
deriving Inhabited, Repr

/--
Designates a document that either contains all newlines in an inner document or where all newlines
have been flattened.

The formatter will always choose a non-failing alternative if one is available or fail otherwise.
When both alternatives are not failing, it chooses an optimal rendering from both alternatives.

`maybeFlattened d` is equivalent to `either d (flattened d)`.

This construct corresponds to `group` in most traditional formatting languages.
-/
def Doc.maybeFlattened (d : Doc) : Doc :=
  .either d d.flattened

/--
Designates a newline that is flattened to a single space when placed inside of a `flattened` node.

Equivalent to `newline (some " ")`.
-/
def Doc.nl : Doc :=
  .newline (some " ")

/--
Designates a newline that is flattened to an empty string when placed inside of a `flattened` node.

Equivalent to `newline (some "")`.
-/
def Doc.break : Doc :=
  .newline (some "")

/--
Designates a newline that cannot be flattened and will produce a `failure` node when attempting
to flatten it.

Equivalent to `newline none`.
-/
def Doc.hardNl : Doc :=
  .newline none

/--
Designates a document that can be rendered to one of several alternatives.

The formatter will always choose a non-failing alternative if one is available or fail otherwise.
When more than one alternative is not failing, it chooses an optimal rendering from
the non-failing alternatives.

Equivalent to `failure` if the set of alternatives is empty.
-/
def Doc.oneOf (ds : Array Doc) : Doc :=
  match ds[0]? with
  | none =>
    .failure
  | some d =>
    ds[1:].foldl (init := d) fun acc d => acc.either d

/--
Appends multiple documents. Each document is appended to the last line of the preceding document.
-/
def Doc.join (ds : Array Doc) : Doc :=
  match ds[0]? with
  | none =>
    .text ""
  | some d =>
    ds[1:].foldl (init := d) fun acc d => acc.append d

/--
Appends multiple documents with a separator document between each pair of adjacent documents.
-/
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

syntax:max "fmt!" interpolatedStr(term) : term

macro_rules
  | `(fmt! $interpStr) => do interpStr.expandInterpolatedStr (← `(Doc)) (← `(ToDoc.toDoc))
