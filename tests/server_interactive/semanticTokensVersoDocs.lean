set_option doc.verso true
set_option doc.verso.suggestions false
/-!
This test checks that Verso docstring semantic tokens work as expected. In particular, it tests that
overlapping token handling does what we want, because the unannotated identifiers and the spaces in
the {lit}`code` elements are assigned the string type, while variables etc are given info-based
tokens. A code block's lines are tokenized one at a time, so an indented block's indentation is not
part of any token and an empty block contributes none. Inline code and math are tokenized one line
at a time as well, and a continuation line's indentation up to the docstring's base column is not
part of any token. Empty content, such as an image without alternate text or a link reference
without a URL, contributes no token. The final docstring exercises the remaining element kinds:
roles with named arguments, flags, and brackets, inline link targets, footnotes, display math,
description list terms, code blocks with arguments, and block commands.
-/
/-- {name}`foo1` {lean}`foo1 x` {assert}`foo1 4 = 5` -/
def foo1 (x : Nat) := x.succ
/-- {name}`foo1` {lean}`foo1 x` {assert}`foo2 = foo1` -/
def foo2 (x : Nat) := x |>.succ
def foo3 := helper where
  /--
  Indented {lit}`multi
  line` code and $`x
  y` math
  -/
  helper := 1
/--
*bold* _emph_ *_both_* {lit}`code` {syntax term}`x + 1`
```leanTerm
(fun _ => rfl : ∀ y : Unit, x = y)
```
```
a plain fence
```
```
```
* Indented fence
  ```
  def a := 1
  def b := 2
  ```
* List
* More list
  1. Nested list
  2. List

  : Term (nested)

    Description

# Header 1

## Header 2

[![link][url]][url]

> Quoted {lit}`code` and *bold*

[url]: http://example.com/example.gif

![](http://example.com/no-alt.gif) and [a link][empty]

[empty]:

{given (type := "Nat") -typeIsMeta +show}`k` and {lean}`k + 1` and {name}[`Nat.succ`] and
[inline link](http://example.com/inline) with a footnote[^note].

$$`E = mc^2`

[^note]: The note.

: Term {lit}`code`

  Body

```lean -error +show
def fromDoc := 1
```

{open Nat}

{set_option maxRecDepth 512}
-/
def x := ()

--^ collectDiagnostics
--^ textDocument/semanticTokens/full
