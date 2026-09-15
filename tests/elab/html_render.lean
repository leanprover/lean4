import Lean.Data.Html

/-! Tests for HTML rendering:
element and attribute syntax, void elements, escaping text,
escaping attribute values, large nesting depth. -/

open Lean Html

/-! ## Basic -/

/-- info: "" -/
#guard_msgs in
#eval render <| .text ""

/-- info: "" -/
#guard_msgs in
#eval render <| .raw ""

/-- info: "" -/
#guard_msgs in
#eval render <| .seq #[]

/-- info: "lorem ipsum" -/
#guard_msgs in
#eval render <| .text "lorem ipsum"

/-- info: "lorem ipsum" -/
#guard_msgs in
#eval render <| .raw "lorem ipsum"

/-! ## Elements, attributes, and children -/

/-- info: "<div><p>lorem ipsum</p></div>" -/
#guard_msgs in
#eval render <| .element "div" #[] (.element "p" #[] "lorem ipsum")

/-- info: "<ul><li>one</li><li>two</li></ul>" -/
#guard_msgs in
#eval render <| .element "ul" #[] (.seq #[.element "li" #[] "one", .element "li" #[] "two"])

/-- info: "<span style=\"red\"></span>" -/
#guard_msgs in
#eval render <| .element "span" #[("style", "red")] .empty

/-- info: "<script defer></script>" -/
#guard_msgs in
#eval render <| .element "script" #[("defer", "")] .empty

/-- info: "<p data-x-foo=\"1\" hidden>x</p>" -/
#guard_msgs in
#eval render <| .element "p" #[("data-x-foo", "1"), ("hidden", "")] "x"

-- Empty non-void elements get an explicit end tag rather than a self-closing tag.
/-- info: "<div></div>" -/
#guard_msgs in
#eval render <| .element "div" #[] .empty

/-! ## Void elements -/

/-- info: "<input type=\"password\"/>" -/
#guard_msgs in
#eval render <| .element "input" #[("type", "password")] .empty

-- Tag names are matched case-insensitively against the void element table.
/-- info: "<BR/>" -/
#guard_msgs in
#eval render <| .element "BR" #[] .empty

-- Void elements with non-normalized empty children are rendered correctly.
/-- info: "<br/>" -/
#guard_msgs in
#eval render <| .element "br" #[] (.seq #[.seq #[]])

/-- info: "<br/>" -/
#guard_msgs in
#eval render <| .element "br" #[] ""

-- Void elements with children are rendered like normal elements.
/-- info: "<br>x</br>" -/
#guard_msgs in
#eval render <| .element "br" #[] "x"

/-! ## Escaping -/

/-- info: "a &amp; b &lt; c &gt; d \" e ' f" -/
#guard_msgs in
#eval render <| .text "a & b < c > d \" e ' f"

/-- info: "a & b < c > d \" e ' f" -/
#guard_msgs in
#eval render <| .raw "a & b < c > d \" e ' f"

/-- info: "<a title=\"a &amp; b < c > d &quot; e ' f\"></a>" -/
#guard_msgs in
#eval render <| .element "a" #[("title", "a & b < c > d \" e ' f")] .empty

/-- info: "<script>if (a < b && c > d) {}</script>" -/
#guard_msgs in
#eval render <| .element "script" #[] (.raw "if (a < b && c > d) {}")

-- `text` is still escaped when nested in raw text elements.
/-- info: "<script>if (a &lt; b &amp;&amp; c &gt; d) {}</script>" -/
#guard_msgs in
#eval render <| .element "script" #[] (.text "if (a < b && c > d) {}")

/-! ## Deep and wide trees -/

def deep (n : Nat) : Html := Id.run do
  let mut h : Html := "x"
  for _ in [0:n] do
    h := .element "div" #[] h
  return h

/-- info: 1100001 -/
#guard_msgs in
#eval (render (deep 100000)).length

/-- info: 100000 -/
#guard_msgs in
#eval (render (.seq (Array.replicate 100000 (.text "a")))).length
