set_option doc.verso true
/-!
This test checks that Verso docstring semantic tokens work as expected. In particular, it tests that
overlapping token handling does what we want, because the unannotated identifiers and the spaces in
the {lit}`code` elements are assigned the string type, while variables etc are given info-based
tokens.
-/
/-- {name}`foo1` {lean}`foo1 x` {assert}`foo1 4 = 5` -/
def foo1 (x : Nat) := x.succ
/-- {name}`foo1` {lean}`foo1 x` {assert}`foo2 = foo1` -/
def foo2 (x : Nat) := x |>.succ
/--
*bold* _emph_ *_both_* {lit}`code`
```leanTerm
(fun _ => rfl : ∀ y : Unit, x = y)
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

[url]: http://example.com/example.gif

-/
def x := ()

--^ collectDiagnostics
--^ textDocument/semanticTokens/full
