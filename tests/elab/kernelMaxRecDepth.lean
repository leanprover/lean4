import Lean

/-!
The kernel bounds its recursion depth by the `maxRecDepth` option. Checking a sufficiently
deeply nested declaration fails deterministically with `(kernel) deep recursion detected` when
`maxRecDepth` is small, and succeeds once the limit is raised.
-/

open Lean

/-- `Nat.succ (Nat.succ ... Nat.zero)` nested `n` deep. -/
private partial def mkDeepNat : Nat → Expr
  | 0     => .const ``Nat.zero []
  | n + 1 => .app (.const ``Nat.succ []) (mkDeepNat n)

-- The kernel allows a multiple of `maxRecDepth` before bailing out, so the term has to be nested
-- deeper than that multiple times the `maxRecDepth` of 256 used below.
private def addDeepDef (name : Name) : MetaM Unit :=
  Lean.addDecl <| .defnDecl {
    name, levelParams := [], type := .const ``Nat [],
    value := mkDeepNat 8000, hints := .opaque, safety := .safe
  }

/-- error: (kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit -/
#guard_msgs in
set_option maxRecDepth 256 in
run_meta addDeepDef `tooDeep

set_option maxRecDepth 100000 in
run_meta addDeepDef `deepEnough
