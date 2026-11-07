import Lean.Elab.DocString
set_option doc.verso true
set_option doc.verso.suggestions false
/-!
This test checks that Verso docstring semantic tokens work as expected. In particular, it tests that
overlapping token handling does what we want, because the unannotated identifiers and the spaces in
the {lit}`code` elements are assigned the `markupInlineCode` type, while variables etc are given info-based
tokens. A code block's lines are tokenized one at a time, so an indented block's indentation is not
part of any token and an empty block contributes none. Inline code and math are tokenized one line
at a time as well, and a continuation line's indentation up to the docstring's base column is not
part of any token. Empty content, such as an image without alternate text or a link reference
without a URL, contributes no token. The final docstring exercises the remaining element kinds:
roles with named arguments, flags, and brackets, inline link targets, footnotes, display math,
description list terms, code blocks with arguments, directives, and block commands. Text, alternate
text, and link URLs that contain an escaped newline get one token per actual source line.
-/
open Lean Doc Elab Term in
/-- A directive whose content is its blocks, unchanged. -/
@[doc_directive]
def identity (content : TSyntaxArray ``Parser.block) : DocM (Block ElabInline ElabBlock) :=
  .concat <$> content.mapM elabBlock

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

:::identity
Inside a *directive*.
:::

{open Nat}

{set_option maxRecDepth 512}
-/
def x := ()

/--
Plain text in a Verso docstring should be tagged as documentation: the leading sentence here, and
the trailing one, are pure inline text with no role markup, *with one piece of bold* and _one
piece of italic_, plus *_bold and italic combined_*. The role {lit}`mid` sits between them,
surrounded by ordinary spaces, and {manual section "deriving-instances"}[a role applied to text]
ends the paragraph. A *bolded {manual section "deriving-instances"}[role applied to text]* follows.

# Heading text with *bold* and _italic_

> Blockquoted text with *bold* and _italic_.

* Bullet item with *bold* and _italic_.
* Another item.
-/
def textExample : Nat := 0

/--
Some text\
more text here

*bold* more text\
x

![alt\
text](https://example.com/x.png) and [a link](https://example.com/a\
b)
-/
def escapedNewlines : Nat := 0

def indentedEscapedNewlines := helper where
  /--
  Some text\
  more text here\
      indented past the base column

  ![alt\
  text](https://example.com/x.png) and [a link](https://example.com/a\
  b)
  -/
  helper : Nat := 0

--^ collectDiagnostics
--^ textDocument/semanticTokens/full
