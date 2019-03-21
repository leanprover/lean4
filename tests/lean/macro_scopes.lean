import init.Lean.Expander init.IO
open Lean.Expander  -- for coercions
open Lean.Parser
open Lean.Parser.Term

local attribute [reducible] MacroScope

-- TODO(Sebastian): `Syntax.toFormat` should probably propagate scopes by itself in the end

#eval (do {
  let stx := review pi {op := Syntax.atom {val := "Π"}, binders := ["a"], range := review sort sort.View.Type},
  -- tag root with {1}
  let stx := stx.flipScopes [1],
  IO.println stx,
  -- tag root with {2} and propagate once
  let stx := stx.flipScopes [2],
  some n ← pure stx.asNode,
  let stx := Syntax.mkNode n.kind n.args,
  IO.println stx,
  -- flip {2}
  let stx := stx.flipScopes [2],
  IO.println stx,
  -- propagate once, only {1} remains
  some n ← pure stx.asNode,
  let stx := Syntax.mkNode n.kind n.args,
  IO.println stx
} : ExceptT String IO Unit)
