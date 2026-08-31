set_option doc.verso true
/-!
This test checks that Verso docstring semantic tokens work as expected. In particular, it tests
overlapping token handling, where unannotated identifiers and spaces inside literal-code elements
receive the string type while variables and similar receive info-based tokens that override string.
It also checks that plain inline prose receives the markupDocText type, so themes can recolor
Verso-format docstring body text uniformly as documentation.
-/
/-- {name}`foo1` {lean}`foo1 x` {assert}`foo1 4 = 5` -/
def foo1 (x : Nat) := x.succ
/-- {name}`foo1` {lean}`foo1 x` {assert}`foo2 = foo1` -/
def foo2 (x : Nat) := x |>.succ

/--
Plain prose in a Verso docstring should be tagged as documentation: the leading sentence here, and
the trailing one, are pure inline text with no role markup, *with one piece of bold* and _one
piece of italic_, plus *_bold and italic combined_*. The role {lit}`mid` sits between them,
surrounded by ordinary spaces.

# Heading prose with *bold* and _italic_

> Blockquoted prose with *bold* and _italic_.

* Bullet item with *bold* and _italic_.
* Another item.
-/
def proseExample : Nat := 0
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
