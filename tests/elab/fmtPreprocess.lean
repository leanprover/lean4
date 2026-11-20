module

meta import all Lean.Fmt.Core.Formatter

/-!
Tests the documents produced by `Lean.Fmt.Doc.preprocess`, which eliminates `flattened` and
`unflattenable` nodes before formatting.
-/

open Lean.Fmt

meta abbrev C := DefaultCost 100 200

/-- The number of distinct nodes of a document, where shared nodes are counted once. -/
meta unsafe def nodeCountImpl (d : Doc C) : Nat :=
  (go d).run {} |>.2.size
where
  go (d : Doc C) : StateM (Std.HashSet USize) Unit := do
    let p := ptrAddrUnsafe d
    if (← get).contains p then
      return
    modify (·.insert p)
    match d with
    | .tagged _ c | .flattened c | .unflattenable c | .indented _ _ c | .aligned c
    | .unindented _ c | .final c | .initial c | .free c | .guarded _ c | .costing _ c =>
      go c
    | .either a b | .append a b =>
      go a
      go b
    | _ =>
      pure ()

@[implemented_by nodeCountImpl]
meta opaque nodeCount (d : Doc C) : Nat

meta def render (d : Doc C) : String :=
  match format? 100 200 d (taintedResolution := false) with
  | .ok out => out.rendering
  | .error _ => "<no rendering>"

meta def word (tag : Nat) (s : String) : Doc C := .tagged tag (.text s)

/-! A document without newlines is shared between its flattened and its non-flattened form. -/

meta def noNewlines : Doc C := word 0 "a" ++ word 1 "b"

/-- info: 6 -/
#guard_msgs in
#eval nodeCount ((Doc.either noNewlines (.flattened noNewlines)).preprocess 200)

/-! Only the parts of a document with newlines are copied for its flattened form. -/

meta def withNewline : Doc C := word 0 "a" ++ .nl ++ word 1 "b"

/-- info: 11 -/
#guard_msgs in
#eval nodeCount ((Doc.either withNewline (.flattened withNewline)).preprocess 200)

/-- info: "a b" -/
#guard_msgs in
#eval render (.flattened withNewline)

/-! A text with a newline and an `unflattenable` node cannot be flattened. -/

/-- info: "a\nb" -/
#guard_msgs in
#eval render (.text "a\nb")

/-- info: "<no rendering>" -/
#guard_msgs in
#eval render (.flattened (.text "a\nb"))

/-- info: "x" -/
#guard_msgs in
#eval render (.unflattenable (.text "x"))

/-- info: "<no rendering>" -/
#guard_msgs in
#eval render (.flattened (.unflattenable (.text "x")))

/-! A subtree that always fails is replaced with `failure`, and alternatives that always fail are
dropped. -/

meta def withHardNewline : Doc C := word 0 "a" ++ .hardNl ++ word 1 "b"

/-- info: 1 -/
#guard_msgs in
#eval nodeCount ((Doc.flattened withHardNewline).preprocess 200)

/-- info: 7 -/
#guard_msgs in
#eval nodeCount ((Doc.either (.flattened withHardNewline) withHardNewline).preprocess 200)

/-- info: "a\nb" -/
#guard_msgs in
#eval render (Doc.either (.flattened withHardNewline) withHardNewline)

/-! Equal subtrees of the result are shared, even if they are not shared in the input. -/

/-- info: 3 -/
#guard_msgs in
#eval show IO Nat from do
  -- Two equal documents that are not shared, since they are built from separate runtime values.
  let tag₁ ← IO.rand 0 0
  let tag₂ ← IO.rand 0 0
  return nodeCount ((Doc.either (word tag₁ "a") (word tag₂ "a")).preprocess 200)

/-! Adjacent texts are merged, including the texts that flattening produces from newlines. -/

/-- info: 1 -/
#guard_msgs in
#eval nodeCount ((Doc.text "a" ++ .text "b" ++ .text "c" : Doc C).preprocess 200)

meta def textsWithNewline : Doc C := .text "a" ++ .nl ++ .text "b"

/-- info: 1 -/
#guard_msgs in
#eval nodeCount ((Doc.flattened textsWithNewline).preprocess 200)

/-- info: "a b" -/
#guard_msgs in
#eval render (.flattened textsWithNewline)

/-- info: "a\nb" -/
#guard_msgs in
#eval render textsWithNewline

-- Merged texts are at most `maxTextLength` characters long.
/-- info: 3 -/
#guard_msgs in
#eval nodeCount ((Doc.text "ab" ++ .text "cd" ++ .text "ef" : Doc C).preprocess 4)
