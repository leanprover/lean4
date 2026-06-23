import Lean.Elab.Command
import Lean.DocString.Markdown

/-!
This test ensures that the rendering of all Verso docstrings to Markdown is sensible.

This rendering is used when showing Verso docstrings over LSP.
-/

open Lean Elab Command Term Doc

private def render (b : Block Empty Empty) : String :=
  MarkdownM.run' (ToMarkdown.toMarkdown b)

/--
Renders `b` to Markdown and prints it preceded by a blank line, so the rendered output reads cleanly
inside `#guard_msgs` expected output. The leading blank line keeps the first rendered line visually
separated from the `info:` marker.
-/
private def showMd (b : Block Empty Empty) : IO Unit := do
  IO.println ""
  IO.println (render b)

/-! Blockquote with one paragraph -/

/--
info:
> A
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.blockquote #[.para #[.text "A"]])

/-! Blockquote with two paragraphs -/

/--
info:
> A
>
> B
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.blockquote #[.para #[.text "A"], .para #[.text "B"]])

/-! Nested blockquote -/

/--
info:
> > X
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.blockquote #[.blockquote #[.para #[.text "X"]]])

/-! Blockquote with inline linebreak -/

/--
info:
> A
> B
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.blockquote #[.para #[.text "A", .linebreak "\n", .text "B"]])

/-! Blockquote inside an unordered list item -/

/--
info:
* > X
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.ul #[⟨#[.blockquote #[.para #[.text "X"]]]⟩])

/--
info:
* > X
  > Y
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.ul #[⟨#[.blockquote #[.para #[.text "X", .linebreak "\n", .text "Y"]]]⟩])

/--
info:
* > X

  > Y
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.ul #[⟨#[.blockquote #[.para #[.text "X"]], .blockquote #[.para #[.text "Y"]]]⟩])


/-! Blockquote of two paragraphs inside an unordered list item -/

/--
info:
* > A
  >
  > B
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.ul #[⟨#[.blockquote #[.para #[.text "A"], .para #[.text "B"]]]⟩])

/-! Blockquote of a fenced code block -/

/--
info:
> ```
> x = 1
> ```
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.blockquote #[.code "x = 1"])

/-! Blockquote → ordered list → blockquotes (multi-line; one item has two paragraphs) -/

/--
info:
> 1. > First line of item 1
>    >
>    > Second paragraph of item 1
>
> 2. > Item 2 line 1
>    > Item 2 line 2
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd <|
    .blockquote #[
      .ol 1 #[
        ⟨#[.blockquote #[
            .para #[.text "First line of item 1"],
            .para #[.text "Second paragraph of item 1"]]]⟩,
        ⟨#[.blockquote #[
            .para #[.text "Item 2 line 1", .linebreak "\n", .text "Item 2 line 2"]]]⟩
      ]
    ]

/-! List with two paragraphs -/

/--
info:
* X

  Y
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.ul #[⟨#[.para #[.text "X"], .para #[.text "Y"]]⟩])

/-! An ordered list with ≥ 10 items keeps continuation prefix width consistent -/

/--
info:
10. X

    Y
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.ol 10 #[⟨#[.para #[.text "X"], .para #[.text "Y"]]⟩])

/--
info:
1. X

   Y

2. X

   Y

3. X

   Y

4. X

   Y

5. X

   Y

6. X

   Y

7. X

   Y

8. X

   Y

9. X

   Y

10. X

    Y
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.ol 1 <| List.replicate 10 ⟨#[.para #[.text "X"], .para #[.text "Y"]]⟩ |>.toArray)

/-! Nested definition list (a `.dl` inside another `.dl`'s description) -/

/--
info:
* **outer**:
  * **inner**:
    value
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd <|
    .dl #[⟨#[.text "outer"], #[
      .dl #[⟨#[.text "inner"], #[.para #[.text "value"]]⟩]
    ]⟩]

/-! Definition list inside a blockquote -/

/--
info:
> * **k**:
>   v
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd <|
    .blockquote #[
      .dl #[⟨#[.text "k"], #[.para #[.text "v"]]⟩]
    ]

/-!
Definition list with a multi-paragraph descripti

The term is separated from the description by a blank line so a CommonMark
parser keeps `**k**:` as its own paragraph instead of fusing it with the first
description paragraph (the latter would produce `<p>**k**: v1</p>`).
-/

/--
info:
* **k**:

  v1

  v2
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd <|
    .dl #[⟨#[.text "k"], #[
      .para #[.text "v1"],
      .para #[.text "v2"]
    ]⟩]

/-! Definition list with a description that mixes a paragraph and a code block -/

/--
info:
* **fn**:

  Computes the answer.

  ```
  def f x := x
  ```
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd <|
    .dl #[⟨#[.text "fn"], #[
      .para #[.text "Computes the answer."],
      .code "def f x := x"
    ]⟩]

/-!
Definition list whose single-block description is itself a code blo

A code fence interrupts a paragraph cleanly in CommonMark, so the renderer
keeps the compact (term-glued) form for single-block descriptions even when
the block isn't a paragraph.
-/

/--
info:
* **fn**:
  ```
  def f x := x
  ```
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd <|
    .dl #[⟨#[.text "fn"], #[.code "def f x := x"]⟩]

/-!
## Inline constructor covera

Each `Inline` constructor (`text`, `emph`, `bold`, `code`, `math` (`inline`,
`display`), `linebreak`, `link`, `footnote`, `image`, `concat`, `other`) is
exercised below. The `other` case requires a non-`Empty` extension type and is
left to `versoDocMarkdown.lean`.
-/

/-! `.text`: plain text is rendered verbatim, with Markdown specials escaped -/

/--
info:
hello \(world\)
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.text "hello (world)"])

/-! `.text`: end-of-sentence periods are *not* escaped (only digit-`.` is, to avoid forming an ol marker) -/

/--
info:
A sentence. Another sentence.
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.text "A sentence. Another sentence."])

/--
info:
Step 1. do the thing.
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.text "Step 1. do the thing."])

/-! `.text`: `-`/`+` are only escaped at the start of a line followed by a space -/

/--
info:
\- bullet
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.text "- bullet"])

/--
info:
co-author and 1+1
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.text "co-author and 1+1"])

/-! `.text`: `!` is only escaped when followed by `[` (to avoid forming image syntax) -/

/--
info:
hello! world \!\[not an image\]
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.text "hello! world ![not an image]"])

/-! `.emph`: emphasis is wrapped in `*…*` -/

/--
info:
*italic*
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.emph #[.text "italic"]])

/-! `.bold`: strong emphasis is wrapped in `**…**` -/

/--
info:
**bold**
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.bold #[.text "bold"]])

/-!
`.code`: inline code is wrapped in backticks; adjacent code spans get a U+200B separat

The two adjacent code spans here would otherwise butt against each other; the
zero-width space (U+200B) keeps them syntactically distinct.
-/

/--
info:
`x`​`y`
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.code "x", .code "y"])

/-! `.math .inline`: inline math is wrapped in `$…$` -/

/--
info:
$x^2$
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.math .inline "x^2"])

/-! `.math .display`: display math is wrapped in `$$…$$` -/

/--
info:
$$x^2$$
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.math .display "x^2"])

/-! `.linebreak`: a hard line break inside a paragraph -/

/--
info:
left
right
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.text "left", .linebreak "\n", .text "right"])

/-! `.link`: a link rendered as `[text](url)` -/

/--
info:
[click](https://example.com)
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.link #[.text "click"] "https://example.com"])

/-! `.footnote`: a `[^name]` reference plus a `[^name]:body` flushed at the end -/

/--
info:
see [^fn1]

[^fn1]:the explanation
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.text "see ", .footnote "fn1" #[.text "the explanation"]])

/-! `.image`: an inline image rendered as `![alt](url)` -/

/--
info:
![cat](cat.png)
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.image "cat" "cat.png"])

/-! `.concat`: an inline `concat` aggregates adjacent inlines on one line -/

/--
info:
ab
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.concat #[.text "a", .text "b"]])

/-!
## Inline nestin

Combinations of `.emph`, `.bold`, `.link`, and `.image`. The renderer must avoid
double-emitting `*` / `**` markers when they're already open, and the `.link`
case must avoid emitting nested `[…](…)` when already inside a link.
-/

/-! Emph inside bold renders as `***…***` -/

/--
info:
***x***
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.bold #[.emph #[.text "x"]]])

/-! Bold inside emph renders as `***…***` -/

/--
info:
***x***
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.emph #[.bold #[.text "x"]]])

/-! Emph inside emph: the inner `*` markers are suppressed -/

/--
info:
*x*
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.emph #[.emph #[.text "x"]]])

/-! Bold inside bold: the inner `**` markers are suppressed -/

/--
info:
**x**
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.bold #[.bold #[.text "x"]]])

/-!
Emph with internal whitespace: leading/trailing spaces are hoisted outside the `*` marke

CommonMark refuses to parse `* x *` as emphasis (the markers can't be padded).
The renderer peels the whitespace out so the emphasized middle has tight markers.
-/

/--
info:
a *x* b
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.text "a", .emph #[.text " x "], .text "b"])

/-! Bold containing inline code: `**…`x`…**` -/

/--
info:
**a `x` b**
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.bold #[.text "a ", .code "x", .text " b"]])

/-! Emph inside a link: `[*x*](url)` -/

/--
info:
[*x*](https://example.com)
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.link #[.emph #[.text "x"]] "https://example.com"])

/-! Bold inside a link: `[**x**](url)` -/

/--
info:
[**x**](https://example.com)
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.link #[.bold #[.text "x"]] "https://example.com"])

/-! Inline code inside a link -/

/--
info:
[`x`](https://example.com)
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.link #[.code "x"] "https://example.com"])

/-! Link inside emph: `*[x](url)*` -/

/--
info:
*[x](https://example.com)*
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.emph #[.link #[.text "x"] "https://example.com"]])

/-! Link inside bold: `**[x](url)**` -/

/--
info:
**[x](https://example.com)**
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.bold #[.link #[.text "x"] "https://example.com"]])

/-!
Nested links: the inner link's URL is dropped and its text rendered inli

CommonMark does not allow nested `[…](…)`, so the renderer flattens the inner
link to its display text only.
-/

/--
info:
[outer x inner](https://outer.example.com)
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd <|
    .para #[.link #[
      .text "outer ",
      .link #[.text "x"] "https://inner.example.com",
      .text " inner"
    ] "https://outer.example.com"]

/-! Linked image: `[![alt](img)](url)` -/

/--
info:
[![cat](cat.png)](https://example.com)
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.link #[.image "cat" "cat.png"] "https://example.com"])

/-! Image alt text is escaped: Markdown specials in `alt` get backslash-escaped -/

/--
info:
![a \(b\) \*c\*](cat.png)
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.image "a (b) *c*" "cat.png"])

/-! Image inside bold: `**![alt](img)**` -/

/--
info:
**![cat](cat.png)**
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.bold #[.image "cat" "cat.png"]])

/-! Image inside emph: `*![alt](img)*` -/

/--
info:
*![cat](cat.png)*
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.para #[.emph #[.image "cat" "cat.png"]])

/-!
## Block constructor covera

`Block` constructors covered above: `para`, `code`, `ul`, `ol`, `dl`, `blockquote`.
The `concat` case is exercised below. `other` requires a non-`Empty` extension and
is left to `versoDocMarkdown.lean`.
-/

/-! `.concat`: a block `concat` joins adjacent blocks with a blank line between -/

/--
info:
A

B
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  showMd (.concat #[.para #[.text "A"], .para #[.text "B"]])
