import Lean.Data.Html
import Std.Data.TreeMap

/-! Tests for the `html%{...}` literal syntax:
outer structure, tags and attributes, interpolation, comments,
text whitespace rules, character references, and error messages. -/

open Lean Html

/-- Prints the compact JSON encoding of `h`, which shows the tree structure explicitly:
elements are objects, `seq` nodes are arrays, and text nodes are strings. -/
def dump (h : Html) : IO Unit := IO.println (toJson h).compress

def bold : Html := html%{<b>x</b>}

/-! ## Outer structure -/

/-- info: [] -/
#guard_msgs in
#eval dump html%{}

/-- info: {"a":[],"c":"a","t":"p"} -/
#guard_msgs in
#eval dump html%{<p>a</p>}

/-- info: [{"a":[],"c":"a","t":"p"},{"a":[],"c":"b","t":"p"}] -/
#guard_msgs in
#eval dump html%{<p>a</p><p>b</p>}

-- Whitespace between sibling elements is a text node, as in HTML.
/-- info: [{"a":[],"c":"a","t":"p"}," ",{"a":[],"c":"b","t":"p"}] -/
#guard_msgs in
#eval dump html%{
  <p>a</p>
  <p>b</p>
}

/-- info: "hello world" -/
#guard_msgs in
#eval dump html%{ hello
  world }

/-- info: {"a":[],"c":"x","t":"b"} -/
#guard_msgs in
#eval dump html%{{bold}}

/-- info: [{"a":[],"c":"x","t":"b"},{"a":[],"c":"x","t":"b"}] -/
#guard_msgs in
#eval dump html%{{#[bold, bold]}}

/-! ## Tags -/

/-- info: {"a":[],"c":[],"t":"div"} -/
#guard_msgs in
#eval dump html%{<div></div>}

/-- info: {"a":[],"c":[],"t":"div"} -/
#guard_msgs in
#eval dump html%{<div/>}

/-- info: {"a":[],"c":[],"t":"div"} -/
#guard_msgs in
#eval dump html%{<div />}

/-- info: {"a":[],"c":[],"t":"br"} -/
#guard_msgs in
#eval dump html%{<br/>}

/-- info: {"a":[],"c":{"a":[],"c":{"a":[],"c":"x","t":"em"},"t":"p"},"t":"div"} -/
#guard_msgs in
#eval dump html%{<div><p><em>x</em></p></div>}

-- Custom element names contain hyphens.
/-- info: {"a":[["foo","1"]],"c":{"a":[],"c":[],"t":"other-el"},"t":"my-element"} -/
#guard_msgs in
#eval dump html%{<my-element foo="1"><other-el/></my-element>}

-- SVG tag names are case-sensitive.
/-- info: {"a":[["viewBox","0 0 1 1"]],"c":{"a":[],"c":[],"t":"foreignObject"},"t":"svg"} -/
#guard_msgs in
#eval dump html%{<svg viewBox="0 0 1 1"><foreignObject/></svg>}

-- Uppercase tag names are ordinary elements in `html%`.
/-- info: {"a":[],"c":"x","t":"Foo"} -/
#guard_msgs in
#eval dump html%{<Foo>x</Foo>}

-- End tags are matched case-insensitively; the start tag's spelling is kept.
/-- info: {"a":[],"c":"x","t":"P"} -/
#guard_msgs in
#eval dump html%{<P>x</p>}

/-! ## Attributes -/

/-- info: {"a":[["href","x"],["data-foo","1"],["hidden",""],["aria-label","y"]],"c":[],"t":"a"} -/
#guard_msgs in
#eval dump html%{<a href="x" data-foo="1" hidden aria-label="y"/>}

-- An empty attribute may be followed by further attributes or by whitespace.
/-- info: {"a":[["disabled",""],["aria-label","abc"]],"c":[],"t":"b"} -/
#guard_msgs in
#eval dump html%{<b disabled aria-label="abc"/>}

/-- info: {"a":[["disabled",""]],"c":[],"t":"b"} -/
#guard_msgs in
#eval dump html%{<b disabled
/>}

-- Attribute names may contain characters that are not allowed in Lean identifiers.
/-- info: {"a":[["xlink:href","x"],["@click","f"],[":prop","1"],["for","y"]],"c":[],"t":"a"} -/
#guard_msgs in
#eval dump html%{<a xlink:href="x" @click="f" :prop="1" for="y"/>}

-- Attribute values are Lean string literals, so Lean escapes apply.
/-- info: {"a":[["title","a\"b\nc"]],"c":[],"t":"a"} -/
#guard_msgs in
#eval dump html%{<a title="a\"b\nc"/>}

-- Interpolated attribute value
/-- info: {"a":[["id","lorem"]],"c":"Lorem ipsum","t":"span"} -/
#guard_msgs in
#eval dump html%{<span id={"lo" ++ "rem"}>Lorem ipsum</span>}

-- Interpolated attribute
/-- info: {"a":[["id","lorem"]],"c":"Lorem ipsum","t":"span"} -/
#guard_msgs in
#eval dump html%{<span {("id", "lorem")}>Lorem ipsum</span>}

-- Interpolated attribute sequences
/-- info: {"a":[["id","lorem"],["class","fancy"]],"c":"Lorem ipsum","t":"span"} -/
#guard_msgs in
#eval dump html%{<span {... #[("id", "lorem"), ("class", "fancy")]}>Lorem ipsum</span>}

/-- info: {"a":[["id","lorem"],["class","fancy"]],"c":[],"t":"span"} -/
#guard_msgs in
#eval dump html%{<span {... [("id", "lorem"), ("class", "fancy")]}/>}

/-- info: {"a":[["id","lorem"]],"c":[],"t":"span"} -/
#guard_msgs in
#eval dump html%{<span {... some ("id", "lorem")}/>}

/-- info: {"a":[],"c":[],"t":"span"} -/
#guard_msgs in
#eval dump html%{<span {... (none : Option (String × String))}/>}

/-- info: {"a":[],"c":[],"t":"span"} -/
#guard_msgs in
#eval dump html%{<span {... #[]}/>}

/-- info: {"a":[["a","1"],["b","2"]],"c":[],"t":"span"} -/
#guard_msgs in
#eval dump html%{<span {... Std.TreeMap.ofList [("b", "2"), ("a", "1")]}/>}

-- Attributes are kept in source order.
/-- info: {"a":[["a","1"],["b","2"],["c","3"],["d","4"],["e","5"]],"c":[],"t":"span"} -/
#guard_msgs in
#eval dump html%{<span a="1" {... #[("b", "2"), ("c", "3")]} {("d", "4")} e="5"/>}

-- Whitespace after an interpolation inside a tag is skipped.
/-- info: {"a":[["a","1"],["b","2"]],"c":[],"t":"span"} -/
#guard_msgs in
#eval dump html%{<span {("a", "1")}
  {... #[("b", "2")]} />}

/-! ## Whitespace and Lean comments in tags -/

-- Whitespace inside tags may contain Lean comments.
/-- info: {"a":[["a","1"],["b",""],["c","2"]],"c":"x","t":"p"} -/
#guard_msgs in
#eval dump html%{<p -- line comment
  a="1" /- block comment -/ b
  c=/- after the equals sign -/"2"
  >x</p -- in the end tag
>}

/-- info: {"a":[],"c":[],"t":"br"} -/
#guard_msgs in
#eval dump html%{<br /- c -/ />}

-- Lean comment syntax in text content is text.
/-- info: {"a":[],"c":"a -- b /- c -/ d","t":"p"} -/
#guard_msgs in
#eval dump html%{<p>a -- b /- c -/ d</p>}

-- Whitespace and comments inside tags are stored in the syntax tree.
/-- info: html%{<p  a="1"  /- c -/  b   >x</p  >} -/
#guard_msgs in
#eval show CoreM Unit from do
  let src := "html%{<p  a=\"1\"  /- c -/  b   >x</p  >}"
  let .ok stx := Parser.runParserCategory (← getEnv) `term src | throwError "parse error"
  logInfo (stx.reprint.getD "")

/-! ## Interpolation -/

/-- info: {"a":[],"c":{"a":[],"c":"x","t":"b"},"t":"p"} -/
#guard_msgs in
#eval dump html%{<p>{bold}</p>}

-- Whitespace inside the braces is not text.
/-- info: {"a":[],"c":["a ",{"a":[],"c":"x","t":"b"}," b"],"t":"p"} -/
#guard_msgs in
#eval dump html%{<p>a { bold } b</p>}

-- Strings coerce to text nodes.
/-- info: {"a":[],"c":"str","t":"p"} -/
#guard_msgs in
#eval dump html%{<p>{"str"}</p>}

/-- info: {"a":[],"c":[{"a":[],"c":"x","t":"b"},{"a":[],"c":"x","t":"b"}],"t":"p"} -/
#guard_msgs in
#eval dump html%{<p>{#[bold, bold]}</p>}

/-- info: {"a":[],"c":{"a":[],"c":"x","t":"b"},"t":"p"} -/
#guard_msgs in
#eval dump html%{<p>{[bold]}</p>}

/-- info: {"a":[],"c":["a ",{"a":[],"c":"x","t":"b"}," b"],"t":"p"} -/
#guard_msgs in
#eval dump html%{<p>a {bold} b</p>}

/-- info: {"a":[],"c":[{"a":[],"c":"x","t":"b"},{"a":[],"c":"x","t":"b"}],"t":"p"} -/
#guard_msgs in
#eval dump html%{<p>{bold}{bold}</p>}

-- Whitespace between interpolations is a text node.
/-- info: {"a":[],"c":[{"a":[],"c":"x","t":"b"}," ",{"a":[],"c":"x","t":"b"}],"t":"p"} -/
#guard_msgs in
#eval dump html%{<p>{bold} {bold}</p>}

/-- info: {"a":[],"c":[{"a":[],"c":"x","t":"b"}," tail ",{"a":[],"c":"x","t":"b"}],"t":"p"} -/
#guard_msgs in
#eval dump html%{<p>{#[bold]} tail {bold}</p>}

/-- info: {"a":[],"c":[{"a":[],"c":"a","t":"li"},{"a":[],"c":"b","t":"li"}],"t":"ul"} -/
#guard_msgs in
#eval dump html%{<ul>{#["a", "b"].map fun (s : String) => html%{<li>{s}</li>}}</ul>}

-- Tag names cannot be interpolated; construct the element in Lean instead.
def tagged (s : Bool) (h : Html) : Html := html%{
  <p>
    {.element (if s then "span" else "strong") #[] html%{<a href="example.com">{h}</a>}}
  </p>
}

/-- info: {"a":[],"c":{"a":[],"c":{"a":[["href","example.com"]],"c":"x","t":"a"},"t":"strong"},"t":"p"} -/
#guard_msgs in
#eval dump (tagged false "x")

/-! ## Comments -/

/-- info: [] -/
#guard_msgs in
#eval dump html%{<!-- Comment -->}

/-- info: {"a":[],"c":[],"t":"div"} -/
#guard_msgs in
#eval dump html%{
  <!-- Comment -->
  <div><!-- Empty! --></div>
  <!-- After -->
}

-- Comments are transparent to the whitespace rules.
/-- info: {"a":[],"c":"a b","t":"p"} -/
#guard_msgs in
#eval dump html%{<p>a <!-- c --> b</p>}

/-- info: {"a":[],"c":"ab","t":"p"} -/
#guard_msgs in
#eval dump html%{<p>a<!-- c -->b</p>}

/-- info: {"a":[],"c":[{"a":[],"c":"x","t":"b"}," ",{"a":[],"c":"x","t":"b"}],"t":"p"} -/
#guard_msgs in
#eval dump html%{<p>{bold}<!-- c --> {bold}</p>}

/-- info: {"a":[],"c":"x","t":"p"} -/
#guard_msgs in
#eval dump html%{<p><!-- c --> x <!-- -- - > --></p>}

/-! ## Whitespace in text -/

-- Whitespace after the start tag and before the end tag is ignored;
-- other runs of whitespace collapse to a single space.
/-- info: {"a":[],"c":["hello to HTML ",{"a":[],"c":[],"t":"br"}],"t":"p"} -/
#guard_msgs in
#eval dump html%{
  <p>
    hello  to
    HTML
    <br/>
  </p>
}

/-- info: {"a":[],"c":["The answer is ","4","!"],"t":"p"} -/
#guard_msgs in
#eval dump html%{
  <p>The answer is {.text s!"{2 + 2}"}!
  </p>
}

-- Reformatting a literal by inserting newlines into existing whitespace does not change it.
#guard html%{<p>The answer is {bold}, it really is!</p>} == html%{
  <p>
    The answer is
    {bold}, it really is!
  </p>
}

#guard html%{<p>blah blah blah</p>} == html%{
  <p>
    blah blah
    blah
  </p>
}

/-- info: {"a":[],"c":["hello ",{"a":[],"c":"x","t":"b"}],"t":"p"} -/
#guard_msgs in
#eval dump html%{<p>hello {bold}</p>}

/-- info: {"a":[],"c":[{"a":[],"c":"x","t":"b"}," world"],"t":"p"} -/
#guard_msgs in
#eval dump html%{<p>{bold} world</p>}

/-- info: {"a":[],"c":[{"a":[],"c":"x","t":"b"},"world"],"t":"p"} -/
#guard_msgs in
#eval dump html%{<p>{bold}world</p>}

/-- info: {"a":[],"c":[{"a":[],"c":"x","t":"b"}," ",{"a":[],"c":"y","t":"i"}],"t":"p"} -/
#guard_msgs in
#eval dump html%{<p><b>x</b> <i>y</i></p>}

/-- info: {"a":[],"c":[{"a":[],"c":"x","t":"b"},{"a":[],"c":"y","t":"i"}],"t":"p"} -/
#guard_msgs in
#eval dump html%{<p><b>x</b><i>y</i></p>}

/-- info: {"a":[],"c":[{"a":[],"c":"x","t":"b"}," ",{"a":[],"c":"y","t":"i"}],"t":"p"} -/
#guard_msgs in
#eval dump html%{<p>
  <b>x</b>
  <i>y</i>
</p>}

/-- info: {"a":[],"c":"a\u0009b","t":"p"} -/
#guard_msgs in
#eval dump html%{<p>a&Tab;b</p>}

-- Only whitespace written literally is collapsed; character references are kept as they are.
/-- info: {"a":[],"c":"a   b","t":"p"} -/
#guard_msgs in
#eval dump html%{<p>a &#32; b</p>}

/-- info: {"a":[],"c":" ","t":"p"} -/
#guard_msgs in
#eval dump html%{<p> &#32; </p>}

-- Text is not tokenized as Lean, so it may start with characters such as `"` or `'`.
/-- info: {"a":[],"c":"\"a 'b","t":"p"} -/
#guard_msgs in
#eval dump html%{<p>"a 'b</p>}

-- Whitespace between content nodes is stored in text nodes, so it survives syntax quotations.
macro "wrapped%" : term => `(html%{<div><b>x</b> <i>y</i> {bold} z</div>})

/-- info: {"a":[],"c":[{"a":[],"c":"x","t":"b"}," ",{"a":[],"c":"y","t":"i"}," ",{"a":[],"c":"x","t":"b"}," z"],"t":"div"} -/
#guard_msgs in
#eval dump wrapped%

/-! ## Character references -/

/-- info: {"a":[],"c":"a & b <c> \"d\" 'e' {f}","t":"p"} -/
#guard_msgs in
#eval dump html%{<p>a &amp; b &lt;c&gt; &quot;d&quot; &apos;e&apos; &lbrace;f&rbrace;</p>}

/-- info: {"a":[],"c":"ABC","t":"p"} -/
#guard_msgs in
#eval dump html%{<p>&#65;&#x42;&#X43;</p>}

#guard html%{<p>&nbsp;&NotEqualTilde;&#x1F600;</p>} == .element "p" #[] (.text " ≂̸😀")

-- Some character references are escaped again when rendering.
/-- info: "<p>&amp;&lt;&gt;\"'</p>" -/
#guard_msgs in
#eval render html%{<p>&amp;&lt;&gt;&quot;&apos;</p>}

-- Character references are decoded in quoted attribute values.
/-- info: {"a":[["href","?a=1&b=2"]],"c":[],"t":"a"} -/
#guard_msgs in
#eval dump html%{<a href="?a=1&amp;b=2"/>}

-- Escapable characters are re-encoded as character references by `render`.
/-- info: "<a href=\"?a=1&amp;b=2\"></a>" -/
#guard_msgs in
#eval render html%{<a href="?a=1&amp;b=2"/>}

/-- info: {"a":[["title","<b> \"q\" AB"]],"c":[],"t":"a"} -/
#guard_msgs in
#eval dump html%{<a title="&lt;b&gt; &quot;q&quot; &#65;&#x42;"/>}

-- Lean's string escapes apply first; reference decoding happens on the resulting string.
/-- info: {"a":[["title","a & b"]],"c":[],"t":"a"} -/
#guard_msgs in
#eval dump html%{<a title="a \x26amp; b"/>}

-- Whitespace in an attribute value is significant.
/-- info: {"a":[["title","a  b"]],"c":[],"t":"a"} -/
#guard_msgs in
#eval dump html%{<a title="a  b"/>}

/-- error: Unterminated HTML character reference '&b' -/
#guard_msgs in
#eval dump html%{<a href="?a=1&b=2"/>}

/-- error: Invalid HTML named character reference `&foo;` -/
#guard_msgs in
#eval dump html%{<a title="&foo;"/>}

/-! ## Rendering -/

/-- info: "<p class=\"x\">a &amp; b<br/>c</p>" -/
#guard_msgs in
#eval render html%{<p class="x">a &amp; b<br/>c</p>}

/-- info: "<ul><li>one</li> <li>two</li></ul>" -/
#guard_msgs in
#eval render html%{
  <ul>
    <li>one</li>
    <li>two</li>
  </ul>
}

/-! ## Errors -/

/--
error: Mismatched end tag, expected `p` but got `q`

Hint: Replace with start tag
  q̵p̲
-/
#guard_msgs in
#eval dump html%{<p></q>}

/--
error: Void element `br` cannot have an end tag

Hint: Remove end tag
  <̵b̵r̵>̵x̵<̵/̵b̵r̵>̵<̲b̲r̲/̲>̲
-/
#guard_msgs in
#eval dump html%{<br>x</br>}

-- The suggestion covers only the element, not the content preceding it, and keeps its attributes.
/--
error: Void element `img` cannot have an end tag

Hint: Remove end tag
  <img src="a" a̵l̵t̵=̵"̵b̵"̵>̵y̵<̵/̵i̵m̵g̵>̵a̲l̲t̲=̲"̲b̲"̲/̲>̲
-/
#guard_msgs in
#eval dump html%{<p>abc<img src="a" alt="b">y</img></p>}

-- A void element with an end tag but no children gets its own message.
/--
error: Void element `br` cannot have an end tag

Hint: Remove end tag
  <̵b̵r̵>̵<̵/̵b̵r̵>̵<̲b̲r̲/̲>̲
-/
#guard_msgs in
#eval dump html%{<br></br>}

/-- error: Invalid HTML named character reference `&foo;` -/
#guard_msgs in
#eval dump html%{<p>a &foo; b</p>}

/-- error: Invalid HTML numeric character reference `&#0;` -/
#guard_msgs in
#eval dump html%{<p>&#0;</p>}

/-- error: Invalid HTML numeric character reference `&#xD800;` -/
#guard_msgs in
#eval dump html%{<p>&#xD800;</p>}

/-- error: Invalid HTML numeric character reference `&#x110000;` -/
#guard_msgs in
#eval dump html%{<p>&#x110000;</p>}

/-- error: Invalid HTML numeric character reference `&#;` -/
#guard_msgs in
#eval dump html%{<p>&#;</p>}

/-- error: Invalid HTML numeric character reference `&#12a;` -/
#guard_msgs in
#eval dump html%{<p>&#12a;</p>}

/--
error: Type mismatch
  true
has type
  Bool
but is expected to have type
  String
-/
#guard_msgs in
#eval dump html%{<a href={true}/>}

/--
error: Type mismatch
  true
has type
  Bool
but is expected to have type
  Html
-/
#guard_msgs in
#eval dump html%{<p>{true}</p>}

/-! ## Pretty printing -/

open Lean in
/--
info: html%{<p class="a">hello <b>world</b>{"x"}<!-- c -->&amp;<br/></p>}
---
info: html%{<a {...#[]} n="v" {("k", "v")} hidden>x</a>}
---
info: html%{<a href="x"/><b>y</b> z {"w"} v}
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
  -- Lean comments inside tags are preserved.
  let src := "html%{<p /- c -/ a=\"1\" -- d\n  b>x</p>}"
  let .ok stx := Parser.runParserCategory (← getEnv) `term src | throwError "parse error"
  logInfo m!"{← PrettyPrinter.ppTerm ⟨stx⟩}"
