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

/-!
Huge `maxRecDepth` values must not wrap around to a small kernel limit (#15973), neither when
converted to `USize` nor when scaled by the kernel's multiplier.
-/

private def addDeepDefWith (name : Name) (maxRecDepth : Nat) : MetaM Unit :=
  withOptions (Lean.maxRecDepth.set · maxRecDepth) (addDeepDef name)

-- Smallest value whose scaled kernel limit overflows: used to wrap to 0.
run_meta addDeepDefWith `scaledWrapZero ((USize.size - 1) / 16 + 1)
-- Used to wrap to a scaled limit of 16.
run_meta addDeepDefWith `scaledWrapSmall ((USize.size - 1) / 16 + 2)
run_meta addDeepDefWith `usizeMax (USize.size - 1)
-- Used to reach the kernel as 1 after `Nat.toUSize`.
run_meta addDeepDefWith `usizeWrap (USize.size + 1)
