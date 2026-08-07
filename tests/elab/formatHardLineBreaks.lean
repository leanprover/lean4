import Lean.Data.Format
import Lean.Meta.Basic

/-! # Hard line breaks in `Format` text

Hard line breaks in `Format`s should not induce inescapable flattening groups, which they did in
previous versions of Lean.
-/

open Lean Meta

/--
info: A
B
C
-/
#guard_msgs (whitespace := exact) in
#eval
  let f : Format := .text "A\nB" ++ .line ++ "C"
  IO.println f.pretty

/--
info: A
  B
C
-/
#guard_msgs (whitespace := exact) in
run_meta do
  logInfo <| m!"A{indentD "B"}" ++ Format.line ++ "C"

/--
info: A
B
  C
D
-/
#guard_msgs (whitespace := exact) in
run_meta do
  let text := toMessageData
  let line := toMessageData Format.line
  logInfo <| text m!"A" ++ line ++ .nest 2 (m!"B" ++ line ++ m!"C") ++ line ++ "D"

/--
info: a
b
a b
-/
#guard_msgs (whitespace := exact) in
run_meta do logInfo (m!"a" ++ Format.line ++ m!"b" ++ Format.line ++ .group m!"a\nb")

/--
info: Indented expression:
  Nat
Bulleted list:
  • A
  • B
---
info: Indented expression:
  Nat
Bulleted list:
  • A
  • B
---
info: Bulleted list:
  • A
  • B
Indented expression:
  Nat
---
info: Bulleted list:
  • A
  • B
Indented expression:
  Nat
-/
#guard_msgs (whitespace := exact) in
run_meta do
  let e := m!"Indented expression:{indentExpr (.const `Nat [])}"
  let l := m!"Bulleted list:{indentD m!"• A\n• B"}"
  logInfo (e ++ .ofFormat (.text "\n") ++ l)
  logInfo (e ++ Format.line ++ l)
  logInfo (l ++ .ofFormat (.text "\n") ++ e)
  logInfo (l ++ Format.line ++ e)

-- *Within* flattening groups, flattening should be recomputed after a hard line break:
/--
info: A
A long line
B
C
D

A
A long line
B C
D
-/
#guard_msgs (whitespace := exact) in
#eval
  let f : Format := .text "A" ++ .line ++ .group ("A long line" ++ .line ++ .text "B" ++ .line ++ "C") ++ .line ++ "D"
  let f' : Format := .text "A" ++ .line ++ .group ("A long line\nB" ++ .line ++ "C") ++ .line ++ "D"
  do
  IO.println (f.pretty 10)
  IO.println ""
  IO.println (f'.pretty 10)

/-! # Forced `align` and flattening

A forced `align` past its indentation level renders a hard line break, so a `line` just before
it must break rather than flatten into trailing whitespace. If that `line` already breaks to
the `align`'s indentation level, the `align` is dropped rather than producing a whitespace-only
blank line.
-/

-- a `line` before a forced `align` with hard `\n` separators after it breaks at any width:
/--
info: iterate 1
  skip
  skip

iterate 1
  skip
  skip
-/
#guard_msgs (whitespace := exact) in
#eval
  let f : Format := .fill (.nest 2 (
    "iterate 1" ++ .line ++ Format.align true ++
    .fill (.nest 2 "skip") ++ .text "\n" ++ .fill (.nest 2 "skip")))
  do
  IO.println (f.pretty 100)
  IO.println ""
  IO.println (f.pretty 12)

-- a `line` that breaks to the `align`'s indentation level does not leave a blank line either:
/--
info: foo
  bar
  baz
-/
#guard_msgs (whitespace := exact) in
#eval
  let f : Format := .fill (.nest 2 (
    "foo" ++ .line ++ Format.align true ++
    .fill (.nest 2 "bar") ++ .text "\n" ++ .fill (.nest 2 "baz")))
  IO.println (f.pretty 4)

-- `align` rendering is otherwise unchanged: it pads from before the indentation level and
-- breaks at or past it:
/--
info: ab  cd
ab
  cd
-/
#guard_msgs (whitespace := exact) in
#eval do
  IO.println (Format.nest 4 ("ab" ++ Format.align true ++ "cd") |>.pretty 100)
  IO.println (Format.nest 2 ("ab" ++ Format.align true ++ "cd") |>.pretty 100)

-- a forced `align` breaks, but the header in front of it is still flattenable, so a group
-- containing one flattens as soon as its flattened form fits: the first row here is 10 columns
-- wide, and `where` stays on it at every width from 10 up.
/--
info: head where
  field

head where
  field

head where
  field
-/
#guard_msgs (whitespace := exact) in
#eval
  let f : Format := .group (
    "head" ++ .line ++ "where" ++ .nest 2 (Format.align true ++ "field"))
  do
  IO.println (f.pretty 10)
  IO.println ""
  IO.println (f.pretty 22)
  IO.println ""
  IO.println (f.pretty 23)

-- the measurement follows the column across work items, not only within the first one: `aa bb`
-- fits width 5 exactly, and at width 8 there is room for `dd` after the aligned `cc`.
/--
info: aa bb
   cc
dd
 ee

aa bb
   cc dd
 ee
-/
#guard_msgs (whitespace := exact) in
#eval
  let f : Format := .fill (
    "aa" ++ .line ++ "bb" ++ .nest 3 (Format.align true ++ "cc") ++
    .line ++ "dd" ++ .nest 1 (Format.align true ++ "ee"))
  do
  IO.println (f.pretty 5)
  IO.println ""
  IO.println (f.pretty 8)

-- flattening a group drops an unforced `align` but not a forced one, so a forced `align` at the
-- head of a group still breaks and the `line` in front of it must not flatten into a space:
/--
info: yyyy
   xxxx where
-/
#guard_msgs (whitespace := exact) in
#eval
  let f : Format := .group (
    "yyyy" ++ .line ++ .group (.nest 3 (Format.align true ++ "xxxx") ++ .line ++ "where"))
  IO.println (f.pretty 20)

-- a group is measured only up to its first line break, so the part after a breaking forced `align`
-- is not covered by that measurement: it gets its own, from the column the `align` broke to. At
-- width 10 the three fields go on rows of their own; at width 30 they share one.
/--
info: head where
  aaaa
  bbbb
  cccc

head where
  aaaa bbbb cccc
-/
#guard_msgs (whitespace := exact) in
#eval
  let f : Format := .group (
    "head" ++ .line ++ "where" ++
      .nest 2 (Format.align true ++ "aaaa" ++ .line ++ "bbbb" ++ .line ++ "cccc"))
  do
  IO.println (f.pretty 10)
  IO.println ""
  IO.println (f.pretty 30)

-- a `line` that breaks only because a forced `align` follows it breaks against the group's own
-- decision, so the rest of that group is measured afresh too -- otherwise `cccccc` would be
-- flattened onto the `bbbb` row on the strength of a measurement taken two rows earlier.
/--
info: aa
  bbbb
cccccc

aa
  bbbb cccccc
-/
#guard_msgs (whitespace := exact) in
#eval
  let f : Format := .group (
    "aa" ++ .line ++ .nest 2 (Format.align true ++ "bbbb") ++ .line ++ "cccccc")
  do
  IO.println (f.pretty 10)
  IO.println ""
  IO.println (f.pretty 30)
