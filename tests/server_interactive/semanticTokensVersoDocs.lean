set_option doc.verso true
set_option doc.verso.suggestions false
/-!
This test checks that Verso docstring semantic tokens work as expected. In particular, it tests that
overlapping token handling does what we want, because the unannotated identifiers and the spaces in
the {lit}`code` elements are assigned the string type, while variables etc are given info-based
tokens. A code block's lines are tokenized one at a time, so an indented block's indentation is not
part of any token and an empty block contributes none.
-/
/-- {name}`foo1` {lean}`foo1 x` {assert}`foo1 4 = 5` -/
def foo1 (x : Nat) := x.succ
/-- {name}`foo1` {lean}`foo1 x` {assert}`foo2 = foo1` -/
def foo2 (x : Nat) := x |>.succ
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

-/
def x := ()

--^ collectDiagnostics
--^ textDocument/semanticTokens/full
