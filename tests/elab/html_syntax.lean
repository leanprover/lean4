import Lean.Data.Html
import Std.Data.TreeMap

/-! Tests for the `html%{...}` literal syntax:
outer structure, tags and attributes, interpolation, comments,
text whitespace rules, character references, and error messages. -/

open Lean Html

/-- Example element to interpolate. -/
def bold : Html := html%{<b>x</b>}

/-! ## Basic tests -/

/-- info: seq #[] -/
#guard_msgs in
#eval html%{}

/-- info: text "hello world" -/
#guard_msgs in
#eval html%{hello world}

/-- info: element "p" #[] (text "a") -/
#guard_msgs in
#eval html%{<p>a</p>}

/-- info: seq #[element "p" #[] (text "a"), element "p" #[] (text "b")] -/
#guard_msgs in
#eval html%{<p>a</p><p>b</p>}

/-- info: text "hello world" -/
#guard_msgs in
#eval html%{{"hello world"}}

/-- info: element "b" #[] (text "x") -/
#guard_msgs in
#eval html%{{bold}}

/-- info: seq #[element "b" #[] (text "x"), element "b" #[] (text "x")] -/
#guard_msgs in
#eval html%{{#[bold, bold]}}

/-! ## Tags -/

/-- info: element "div" #[] (seq #[]) -/
#guard_msgs in
#eval html%{<div></div>}

/-- info: element "div" #[] (seq #[]) -/
#guard_msgs in
#eval html%{<div/>}

/-- info: element "div" #[] (seq #[]) -/
#guard_msgs in
#eval html%{<div />}

/-- info: element "br" #[] (seq #[]) -/
#guard_msgs in
#eval html%{<br/>}

/-- info: element "div" #[] (element "p" #[] (element "em" #[] (text "x"))) -/
#guard_msgs in
#eval html%{<div><p><em>x</em></p></div>}

-- Custom element names can contain hyphens.
/-- info: element "my-element" #[("foo", "1")] (element "other-el" #[] (seq #[])) -/
#guard_msgs in
#eval html%{<my-element foo="1"><other-el/></my-element>}

-- Tag names are parsed case-sensitively.
/-- info: element "svg" #[("viewBox", "0 0 1 1")] (element "foreignObject" #[] (seq #[])) -/
#guard_msgs in
#eval html%{<svg viewBox="0 0 1 1"><foreignObject/></svg>}

-- Uppercase tag names are ordinary elements.
/-- info: element "Foo" #[] (text "x") -/
#guard_msgs in
#eval html%{<Foo>x</Foo>}

-- End tags are matched case-insensitively; the start tag's spelling is kept.
/-- info: element "P" #[] (text "x") -/
#guard_msgs in
#eval html%{<P>x</p>}

/-! ## Attributes -/

/--
info: element "a" #[("href", "x"), ("data-foo", "1"), ("hidden", ""), ("aria-label", "y")] (seq #[])
-/
#guard_msgs in
#eval html%{<a href="x" data-foo="1" hidden aria-label="y"/>}

-- An empty attribute may be followed by further attributes or by whitespace.
/-- info: element "b" #[("disabled", ""), ("aria-label", "abc")] (seq #[]) -/
#guard_msgs in
#eval html%{<b disabled aria-label="abc"/>}

/-- info: element "b" #[("disabled", "")] (seq #[]) -/
#guard_msgs in
#eval html%{<b disabled
/>}

-- Attribute names may contain characters that are not allowed in Lean identifiers.
/--
info: element "a" #[("xlink:href", "x"), ("@click", "f"), (":prop", "1"), ("for", "y")] (seq #[])
-/
#guard_msgs in
#eval html%{<a xlink:href="x" @click="f" :prop="1" for="y"/>}

-- Attribute values are Lean string literals, so Lean escapes apply.
/-- info: element "a" #[("title", "a\"b\nc")] (seq #[]) -/
#guard_msgs in
#eval html%{<a title="a\"b\nc"/>}

-- Interpolated attribute value
/-- info: element "span" #[("id", "lorem")] (text "Lorem ipsum") -/
#guard_msgs in
#eval html%{<span id={"lo" ++ "rem"}>Lorem ipsum</span>}

-- Interpolated attribute
/-- info: element "span" #[("id", "lorem")] (text "Lorem ipsum") -/
#guard_msgs in
#eval html%{<span {("id", "lorem")}>Lorem ipsum</span>}

-- Interpolated attribute sequences
/-- info: element "span" #[("id", "lorem"), ("class", "fancy")] (text "Lorem ipsum") -/
#guard_msgs in
#eval html%{<span {... #[("id", "lorem"), ("class", "fancy")]}>Lorem ipsum</span>}

/-- info: element "span" #[("id", "lorem"), ("class", "fancy")] (seq #[]) -/
#guard_msgs in
#eval html%{<span {... [("id", "lorem"), ("class", "fancy")]}/>}

-- Any type with a `ForIn` instance works
/-- info: element "span" #[("id", "lorem")] (seq #[]) -/
#guard_msgs in
#eval html%{<span {... some ("id", "lorem")}/>}

/-- info: element "span" #[] (seq #[]) -/
#guard_msgs in
#eval html%{<span {... (none : Option (String × String))}/>}

/-- info: element "span" #[] (seq #[]) -/
#guard_msgs in
#eval html%{<span {... #[]}/>}

/-- info: element "span" #[("a", "1"), ("b", "2")] (seq #[]) -/
#guard_msgs in
#eval html%{<span {... Std.TreeMap.ofList [("b", "2"), ("a", "1")]}/>}

-- Attributes are kept in source order.
/-- info: element "span" #[("a", "1"), ("b", "2"), ("c", "3"), ("d", "4"), ("e", "5")] (seq #[]) -/
#guard_msgs in
#eval html%{<span a="1" {... #[("b", "2"), ("c", "3")]} {("d", "4")} e="5"/>}

/-! ## Whitespace and Lean comments -/

-- Whitespace inside tags is dropped.
-- It may contain Lean comments.
/-- info: element "p" #[("a", "1"), ("b", ""), ("c", "2")] (text "x") -/
#guard_msgs in
#eval html%{<p -- line comment
  a="1" /- block comment -/ b
  c=/- after the equals sign -/"2"
  >x</p -- in the end tag
>}

/-- info: element "br" #[] (seq #[]) -/
#guard_msgs in
#eval html%{<br /- c -/ />}

-- Lean comment syntax in text content is text.
/-- info: element "p" #[] (text "a -- b /- c -/ d") -/
#guard_msgs in
#eval html%{<p>a -- b /- c -/ d</p>}

-- Whitespace and comments inside tags are preserved in the syntax tree.
/-- info: html%{<p  a="1"  /- c -/  b   >x</p  >} -/
#guard_msgs in
#eval show CoreM Unit from do
  let src := "html%{<p  a=\"1\"  /- c -/  b   >x</p  >}"
  let .ok stx := Parser.runParserCategory (← getEnv) `term src | throwError "parse error"
  logInfo (stx.reprint.getD "")

/-! ## Interpolation -/

/-- info: element "p" #[] (element "b" #[] (text "x")) -/
#guard_msgs in
#eval html%{<p>{bold}</p>}

-- Strings coerce to text nodes.
/-- info: element "p" #[] (text "str") -/
#guard_msgs in
#eval html%{<p>{"str"}</p>}

/-- info: element "p" #[] (seq #[element "b" #[] (text "x"), element "b" #[] (text "x")]) -/
#guard_msgs in
#eval html%{<p>{#[bold, bold]}</p>}

/-- info: element "p" #[] (element "b" #[] (text "x")) -/
#guard_msgs in
#eval html%{<p>{[bold]}</p>}

/-- info: element "p" #[] (seq #[text "a ", element "b" #[] (text "x"), text " b"]) -/
#guard_msgs in
#eval html%{<p>a {bold} b</p>}

/-- info: element "p" #[] (seq #[element "b" #[] (text "x"), element "b" #[] (text "x")]) -/
#guard_msgs in
#eval html%{<p>{bold}{bold}</p>}

-- Whitespace between interpolations is a text node.
/--
info: element "p" #[] (seq #[element "b" #[] (text "x"), text " ", element "b" #[] (text "x")])
-/
#guard_msgs in
#eval html%{<p>{bold} {bold}</p>}

/--
info: element "p" #[] (seq #[element "b" #[] (text "x"), text " tail ", element "b" #[] (text "x")])
-/
#guard_msgs in
#eval html%{<p>{#[bold]} tail {bold}</p>}

-- Nested interpolation.
/-- info: element "ul" #[] (seq #[element "li" #[] (text "a"), element "li" #[] (text "b")]) -/
#guard_msgs in
#eval html%{<ul>{#["a", "b"].map fun (s : String) => html%{<li>{s}</li>}}</ul>}

-- Interpolated sequences of nodes: any type with a `ForIn` instance works.
/-- info: element "ul" #[] (seq #[element "li" #[] (text "a"), element "li" #[] (text "b")]) -/
#guard_msgs in
#eval html%{<ul>{... ["a", "b"].map fun (s : String) => html%{<li>{s}</li>}}</ul>}

/-- info: element "p" #[] (seq #[text "a ", element "b" #[] (text "x"), text " b"]) -/
#guard_msgs in
#eval html%{<p>a {... some bold} b</p>}

/-- info: element "p" #[] (seq #[]) -/
#guard_msgs in
#eval html%{<p>{... (none : Option Html)}</p>}

/-- info: seq #[element "b" #[] (text "x"), element "b" #[] (text "x"), text "y"] -/
#guard_msgs in
#eval html%{{... #[bold, bold]}y}

-- Tag names cannot be interpolated; construct the element in Lean instead.
def tagged (s : Bool) (h : Html) : Html := html%{
  <p>
    {.element (if s then "span" else "strong") #[] html%{<a href="example.com">{h}</a>}}
  </p>
}

/--
info: element "p" #[] (element "strong" #[] (element "a" #[("href", "example.com")] (text "x")))
-/
#guard_msgs in
#eval (tagged false "x")

/-! ## HTML comments -/

/-- info: seq #[] -/
#guard_msgs in
#eval html%{<!-- Comment -->}

/-- info: element "div" #[] (seq #[]) -/
#guard_msgs in
#eval html%{
  <!-- Comment -->
  <div><!-- Empty! --></div>
  <!-- After -->
}

-- Comments are transparent to whitespace normalization rules.
/-- info: element "p" #[] (text "a b") -/
#guard_msgs in
#eval html%{<p>a <!-- c --> b</p>}

/-- info: element "p" #[] (text "ab") -/
#guard_msgs in
#eval html%{<p>a<!-- c -->b</p>}

/--
info: element "p" #[] (seq #[element "b" #[] (text "x"), text " ", element "b" #[] (text "x")])
-/
#guard_msgs in
#eval html%{<p>{bold}<!-- c --> {bold}</p>}

/-- info: element "p" #[] (text " x ") -/
#guard_msgs in
#eval html%{<p><!-- c --> x <!-- -- - > --></p>}

/-! ## Whitespace in text -/

-- Whitespace that contains a newline (U+000A or U+000D),
-- and is not surrounded by text on both sides, is removed.

/-- info: seq #[element "span" #[] (text "foo"), element "span" #[] (text "bar")] -/
#guard_msgs in
#eval html%{
  <span>foo</span>
  <span>bar</span>
}

/-- info: seq #[element "span" #[] (text "foo"), element "span" #[] (text "bar")] -/
#guard_msgs in
#eval html%{
  <span>
    foo
  </span>
  <span>
    bar
  </span>
}

/-- info: seq #[text "foo", text "bar"] -/
#guard_msgs in
#eval html%{
  { "foo" }
  { "bar" }
}

/-- info: seq #[text "foo", text "bar"] -/
#guard_msgs in
#eval html%{
  foo
  { "bar" }
}

/-- info: seq #[text "foo", element "span" #[] (text "bar")] -/
#guard_msgs in
#eval html%{
  foo
  <span>bar</span>
}

/-- info: element "p" #[] (seq #[element "b" #[] (text "x"), element "i" #[] (text "y")]) -/
#guard_msgs in
#eval html%{<p>
  <b>x</b>
  <i>y</i>
</p>}

-- Other consecutive whitespace is kept and collapsed into a single space (U+0020).
/-- info: element "p" #[] (seq #[text "hello to HTML", element "br" #[] (seq #[])]) -/
#guard_msgs in
#eval html%{
  <p>
    hello  to
    HTML
    <br/>
  </p>
}

/-- info: element "p" #[] (seq #[text "The answer is ", text "4", text "!"]) -/
#guard_msgs in
#eval html%{
  <p>The answer is {.text s!"{2 + 2}"}!</p>
}

#guard html%{<p>The answer is {bold}, it really is!</p>} == html%{
  <p>
    The answer is {bold},
    it really is!
  </p>
}

#guard html%{<p>blah blah blah</p>} == html%{
  <p>
    blah blah
    blah
  </p>
}

/-- info: element "p" #[] (seq #[text "hello ", element "b" #[] (text "x")]) -/
#guard_msgs in
#eval html%{<p>hello {bold}</p>}

/-- info: element "p" #[] (seq #[element "b" #[] (text "x"), text " world"]) -/
#guard_msgs in
#eval html%{<p>{bold} world</p>}

/-- info: element "p" #[] (seq #[element "b" #[] (text "x"), text "world"]) -/
#guard_msgs in
#eval html%{<p>{bold}world</p>}

/--
info: element "p" #[] (seq #[element "b" #[] (text "x"), text " ", element "i" #[] (text "y")])
-/
#guard_msgs in
#eval html%{<p><b>x</b> <i>y</i></p>}

-- Only whitespace written literally is collapsed; character references are kept as they are.
/-- info: element "p" #[] (text "a\tb") -/
#guard_msgs in
#eval html%{<p>a&Tab;b</p>}

/-- info: element "p" #[] (text "a   b") -/
#guard_msgs in
#eval html%{<p>a &#32; b</p>}

/-- info: element "p" #[] (text "   ") -/
#guard_msgs in
#eval html%{<p> &#32; </p>}

-- Text is not tokenized as Lean, so it may start with characters such as `"` or `'`.
/-- info: element "p" #[] (text "\"a 'b") -/
#guard_msgs in
#eval html%{<p>"a 'b</p>}

-- Whitespace between content nodes survives syntax quotations.
macro "wrapped%" : term => `(html%{<div><b>x</b> <i>y</i> {bold} z</div>})

/--
info: element "div" #[]
  (seq
    #[element "b" #[] (text "x"), text " ", element "i" #[] (text "y"), text " ", element "b" #[] (text "x"),
      text " z"])
-/
#guard_msgs in
#eval wrapped%

/-! ## Character references -/

/-- info: element "p" #[] (text "a & b <c> \"d\" 'e' {f}") -/
#guard_msgs in
#eval html%{<p>a &amp; b &lt;c&gt; &quot;d&quot; &apos;e&apos; &lbrace;f&rbrace;</p>}

/-- info: element "p" #[] (text "ABC") -/
#guard_msgs in
#eval html%{<p>&#65;&#x42;&#X43;</p>}

#guard html%{<p>&nbsp;&NotEqualTilde;&#x1F600;&NewLine;</p>} == .element "p" #[] (.text " ≂̸😀\n")

-- Character references are decoded in quoted attribute values.
/-- info: element "a" #[("href", "?a=1&b=2")] (seq #[]) -/
#guard_msgs in
#eval html%{<a href="?a=1&amp;b=2"/>}

/-- info: element "a" #[("title", "<b> \"q\" AB")] (seq #[]) -/
#guard_msgs in
#eval html%{<a title="&lt;b&gt; &quot;q&quot; &#65;&#x42;"/>}

-- Lean's string escapes apply first; reference decoding happens on the resulting string.
/-- info: element "a" #[("title", "a & b")] (seq #[]) -/
#guard_msgs in
#eval html%{<a title="a \x26amp; b"/>}

-- Whitespace in an attribute value is kept.
/-- info: element "a" #[("title", "a  b")] (seq #[]) -/
#guard_msgs in
#eval html%{<a title="a  b"/>}

/--
error: Unterminated HTML character reference '&b'

Hint: Escape the ampersand
  &a̲m̲p̲;̲
-/
#guard_msgs in
#eval html%{<a href="?a=1&b=2"/>}

/-- error: Invalid HTML named character reference `&foo;` -/
#guard_msgs in
#eval html%{<a title="&foo;"/>}

/-! ## Errors -/

/--
error: Mismatched end tag, expected `p` but got `q`

Hint: Replace with start tag
  q̵p̲
-/
#guard_msgs in
#eval html%{<p></q>}

/--
error: Void element `br` cannot have children or an end tag

Hint: Make it self-closing
  <̵b̵r̵>̵<̵/̵b̵r̵>̵<̲b̲r̲/̲>̲
-/
#guard_msgs in
#eval html%{<br></br>}

-- The suggestion covers only the element, not surrounding content, and keeps its attributes.
/--
error: Void element `img` cannot have children or an end tag

Hint: Make it self-closing
  <img src="a" a̵l̵t̵=̵"̵b̵"̵>̵y̵<̵/̵i̵m̵g̵>̵a̲l̲t̲=̲"̲b̲"̲/̲>̲
-/
#guard_msgs in
#eval html%{<p>abc<img src="a" alt="b">y</img></p>}

/--
error: Unterminated HTML character reference '&'

Hint: Escape the ampersand
  &a̲m̲p̲;̲
-/
#guard_msgs in
#eval html%{<p>Tom & Jerry</p>}

/-- error: Invalid HTML named character reference `&foo;` -/
#guard_msgs in
#eval html%{<p>a &foo; b</p>}

/-- error: Invalid HTML numeric character reference `&#0;` -/
#guard_msgs in
#eval html%{<p>&#0;</p>}

/-- error: Invalid HTML numeric character reference `&#xD800;` -/
#guard_msgs in
#eval html%{<p>&#xD800;</p>}

/-- error: Invalid HTML numeric character reference `&#x110000;` -/
#guard_msgs in
#eval html%{<p>&#x110000;</p>}

/-- error: Invalid HTML numeric character reference `&#;` -/
#guard_msgs in
#eval html%{<p>&#;</p>}

/-- error: Invalid HTML numeric character reference `&#12a;` -/
#guard_msgs in
#eval html%{<p>&#12a;</p>}

/--
error: Type mismatch
  true
has type
  Bool
but is expected to have type
  String
-/
#guard_msgs in
#eval html%{<a href={true}/>}

/--
error: Type mismatch
  true
has type
  Bool
but is expected to have type
  Html
-/
#guard_msgs in
#eval html%{<p>{true}</p>}

/-! ## Pretty printing -/

open Lean in
/--
info: html%{<p class="a">hello <b>world</b>{"x"}<!-- c -->&amp;<br/></p>}
---
info: html%{<a {...#[]} n="v" {("k", "v")} hidden>x</a>}
---
info: html%{<a href="x"/><b>y</b> z {"w"} v}
---
info: html%{<p>{...#["y"]} x</p>}
---
info: html%{<p /- c -/ a="1" -- d
   b>x</p>}
-/
#guard_msgs in
#eval show CoreM Unit from do
  let stx ← `(html%{<p class="a">hello <b>world</b>{"x"}<!-- c -->&amp;<br/></p>})
  logInfo m!"{← PrettyPrinter.ppTerm stx}"
  let stx ← `(html%{<a {... #[]} n="v" {("k", "v")} hidden>x</a>})
  logInfo m!"{← PrettyPrinter.ppTerm stx}"
  -- Whitespace between content nodes is part of text nodes, so the pretty printer preserves it.
  let stx ← `(html%{<a href="x"/><b>y</b> z {"w"} v})
  logInfo m!"{← PrettyPrinter.ppTerm stx}"
  let stx ← `(html%{<p>{... #["y"]} x</p>})
  logInfo m!"{← PrettyPrinter.ppTerm stx}"
  -- Lean comments inside tags are preserved.
  let src := "html%{<p /- c -/ a=\"1\" -- d\n  b>x</p>}"
  let .ok stx := Parser.runParserCategory (← getEnv) `term src | throwError "parse error"
  logInfo m!"{← PrettyPrinter.ppTerm ⟨stx⟩}"
