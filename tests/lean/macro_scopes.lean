import init.lean.expander init.io
open lean.expander  -- for coercions
open lean.parser
open lean.parser.term

local attribute [reducible] macro_scope

-- TODO(Sebastian): `syntax.to_format` should probably propagate scopes by itself in the end

#eval (do {
  let stx := review pi {op := syntax.atom {val := "Π"}, binders := ["a"], range := review sort sort.view.Type},
  -- tag root with {1}
  let stx := stx.flip_scopes [1],
  io.println stx,
  -- propagate once and tag root with {2}
  some n ← pure stx.as_node,
  let stx := syntax.mk_node n.kind n.args,
  let stx := stx.flip_scopes [2],
  io.println stx,
  -- flip {1}
  let stx := stx.flip_scopes [1],
  io.println stx,
  -- propagate once, only {2} remains
  some n ← pure stx.as_node,
  let stx := syntax.mk_node n.kind n.args,
  io.println stx
} : except_t string io unit)
