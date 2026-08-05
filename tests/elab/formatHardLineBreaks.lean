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
