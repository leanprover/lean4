import Lean
set_option doc.verso true

/-!
This test checks that indentation-specific Verso syntax in docstrings is processed relative to their
indentation, rather than an absolute column 0.
-/

open Lean Elab Command in
def printVersoDocstring (name : Name) : CommandElabM Unit := do
  match (← findInternalDocString? (← getEnv) name) with
  | none => IO.println s!"No docstring for {name}"
  | some (.inl md) => IO.println s!"Markdown:\n{md}"
  | some (.inr v) => IO.println (repr v.text); IO.println (repr v.subsections)

-- Test 1: Indented header on non-first line (e.g. inside where block)
def foo := bar where
  /--
  # Header in where block
  Content here
  -/
  bar := 1

/--
info: #[]
#[{ title := #[Lean.Doc.Inline.text "Header in where block"],
    titleString := "Header in where block",
    metadata := none,
    content := #[Lean.Doc.Block.para
                   #[Lean.Doc.Inline.text "Content here", Lean.Doc.Inline.linebreak "\n", Lean.Doc.Inline.text "  "]],
    subParts := #[] }]
-/
#guard_msgs in
#eval printVersoDocstring ``foo.bar

-- Test 2: Multiple headers at indentation level
namespace Indented
  /--
  # First header
  Some text.

  ## Second header
  More text.
  -/
  def baz := 1
end Indented

/--
info: #[]
#[{ title := #[Lean.Doc.Inline.text "First header"],
    titleString := "First header",
    metadata := none,
    content := #[Lean.Doc.Block.para #[Lean.Doc.Inline.text "Some text."]],
    subParts := #[{ title := #[Lean.Doc.Inline.text "Second header"],
                    titleString := "Second header",
                    metadata := none,
                    content := #[Lean.Doc.Block.para
                                   #[Lean.Doc.Inline.text "More text.", Lean.Doc.Inline.linebreak "\n",
                                     Lean.Doc.Inline.text "  "]],
                    subParts := #[] }] }]
-/
#guard_msgs in
#eval printVersoDocstring ``Indented.baz

-- Test 3: First-line header still works when indented
namespace FirstLine
  /-- # Inline header -/
  def qux := 1

  /-- # Inline header
  # Indented
  -/
  def quux := 1
end FirstLine

/--
info: #[]
#[{ title := #[Lean.Doc.Inline.text "Inline header "],
    titleString := "Inline header ",
    metadata := none,
    content := #[],
    subParts := #[] }]
-/
#guard_msgs in
#eval printVersoDocstring ``FirstLine.qux

/--
info: #[]
#[{ title := #[Lean.Doc.Inline.text "Inline header"],
    titleString := "Inline header",
    metadata := none,
    content := #[],
    subParts := #[] },
  { title := #[Lean.Doc.Inline.text "Indented"],
    titleString := "Indented",
    metadata := none,
    content := #[],
    subParts := #[] }]
-/
#guard_msgs in
#eval printVersoDocstring ``FirstLine.quux


-- Test 4: Indented code block fences
namespace CodeBlock
  /--
  # Code example
  Some intro text.

  ```
  example code
  ```
  -/
  def withCode := 1
end CodeBlock

/--
info: #[]
#[{ title := #[Lean.Doc.Inline.text "Code example"],
    titleString := "Code example",
    metadata := none,
    content := #[Lean.Doc.Block.para #[Lean.Doc.Inline.text "Some intro text."], Lean.Doc.Block.code "example code\n"],
    subParts := #[] }]
-/
#guard_msgs in
#eval printVersoDocstring ``CodeBlock.withCode

-- Test 5: Deeply nested indentation (column 8+)
namespace Deep
  namespace Deeper
    namespace Deepest
      /--
      # Deep header
      Content at depth.
      -/
      def deep := 1
    end Deepest
  end Deeper
end Deep

/--
info: #[]
#[{ title := #[Lean.Doc.Inline.text "Deep header"],
    titleString := "Deep header",
    metadata := none,
    content := #[Lean.Doc.Block.para
                   #[Lean.Doc.Inline.text "Content at depth.", Lean.Doc.Inline.linebreak "\n",
                     Lean.Doc.Inline.text "      "]],
    subParts := #[] }]
-/
#guard_msgs in
#eval printVersoDocstring ``Deep.Deeper.Deepest.deep


-- Test 6: Non-indented
/--
# Top-level header
Content.
-/
def topLevel := 1

/--
info: #[]
#[{ title := #[Lean.Doc.Inline.text "Top-level header"],
    titleString := "Top\\-level header",
    metadata := none,
    content := #[Lean.Doc.Block.para #[Lean.Doc.Inline.text "Content.", Lean.Doc.Inline.linebreak "\n"]],
    subParts := #[] }]
-/
#guard_msgs in
#eval printVersoDocstring ``topLevel


-- Test 7: Indented link reference
namespace Links
  /--
  # Header with link
  See [Lean][lean-link] for more.

  [lean-link]: https://lean-lang.org
  -/
  def withLink := 1
end Links


/--
info: #[]
#[{ title := #[Lean.Doc.Inline.text "Header with link"],
    titleString := "Header with link",
    metadata := none,
    content := #[Lean.Doc.Block.para
                   #[Lean.Doc.Inline.text "See ",
                     Lean.Doc.Inline.link #[Lean.Doc.Inline.text "Lean"] "https://lean-lang.org",
                     Lean.Doc.Inline.text " for more."],
                 Lean.Doc.Block.concat #[]],
    subParts := #[] }]
-/
#guard_msgs in
#eval printVersoDocstring ``Links.withLink

-- Test 8: Over-indented # is a syntax error (extra spaces beyond base column)
/--
@ +5:4...*
error: expected '#' (header) to start at column 2
-/
#guard_msgs (positions := true) in
def overIndented := bar where
  /--
  Some text.

    # Not a header
  -/
  bar := 1
