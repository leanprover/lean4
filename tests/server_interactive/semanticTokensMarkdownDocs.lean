/-!
This test exercises plain (non-Verso) Markdown docstring highlighting. It
includes at least one instance of every CommonMark construct the Markdown
tokenizer recognizes and at least one instance of every `markup*` token
type the server emits, with the `markupBold` and `markupItalic` modifiers in
each block context (heading, blockquote, list).
-/

/--
# Heading 1

## Heading 2 with **bold** and *italic*

### Heading 3 with ***both***

Setext heading
==============

Paragraph with **bold**, *italic*, ***both***, `inline code`, a [link](https://example.com), an
![image](https://example.com/x.png "title"), an autolink <https://example.com>, and a hard break on\
the next line.

---

> Blockquote with **bold**, *italic*, and ***both***.
>
> > Nested blockquote.
>
> * List inside blockquote with *italic*

* Bullet list with **bold**
* Another item with *italic* and ***both***

1. Ordered with `code`
2. Another

```lean
example : True := trivial
```

    indented
    code block

[ref]: https://example.com "title"

A reference link: [text][ref] and a shortcut: [ref]. And a non-reference: [text][bogus]. And a
forward ref: [text][ref2]

[ref2]: https://example.com

A paragraph with *cross-line italic* and **cross-line bold** to verify multi-line emphasis is
recognised.

An angle-bracketed destination [with spaces](<https://example.com/a b>) and one in a
[reference][ang].

[ang]: <https://example.com/angle>
-/
def x := ()

def y := z
where
  /--
  An indented docstring with a paragraph
    whose continuation is indented two more columns,

      an indented code block,

  - a list item
    whose continuation is indented to its content

    and a second paragraph in the item.

    ```lean
    example : True := trivial
    ```
  -/
  z := ()

/--
A fence that is never closed continues to the end of the docstring:

```lean
example : True := trivial
-/
def unterminated := ()

/-- Inline HTML such as <kbd>Ctrl</kbd> and a comment <!-- note --> are inline code. -/
def inlineHtml := ()

/--
An HTML block is code up to the blank line that ends it:

<details>
<summary>More</summary>

Hidden *text*.

</details>
-/
def htmlBlock := ()

/-!
# Heading 1

## Heading 2 with **bold** and *italic*

### Heading 3 with ***both***

Setext heading
==============

Paragraph with **bold**, *italic*, ***both***, `inline code`, a [link](https://example.com), an
![image **with embedded content** [link[nonlink][ref]][ref]](https://example.com/x.png "title"), an
autolink <https://example.com>, and a hard break on the next line.

---

> Blockquote with **bold**, *italic*, and ***both***.
>
> > Nested blockquote.
>
> * List inside blockquote with *italic*

* Bullet list with **bold**
* Another item with *italic* and ***both***

1. Ordered with `code`
2. Another

```lean
example : True := trivial
```

    indented
    code block

[ref]: https://example.com "title"

A reference link: [text][ref] and a shortcut: [ref]. And a non-reference: [text][bogus]. And a
forward ref: [text][ref2]

[ref2]: https://example.com

A paragraph with *cross-line italic* and **cross-line bold** to verify multi-line emphasis is
recognised.
-/

--^ collectDiagnostics
--^ textDocument/semanticTokens/full
