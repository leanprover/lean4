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

/-- `g n x` reduces to `Nat.succ` nested `n` deep around `x`. The kernel reduces `Nat.succ a` by
reducing `a` first, so reducing `g n x` recurses `n` deep through `whnf`. -/
def g : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => Nat.succ (g n x)

/-- `∀ x, Nat.beq (g 8000 x) 0 = false`, which the kernel checks by reducing `g 8000 x`. -/
private def addDeepWhnf (name : Name) : MetaM Unit :=
  Meta.withLocalDeclD `x (.const ``Nat []) fun x => do
    let lhs := mkApp2 (.const ``Nat.beq []) (mkApp2 (.const ``g []) (mkRawNatLit 8000) x) (mkRawNatLit 0)
    let type ← Meta.mkForallFVars #[x] (← Meta.mkEq lhs (.const ``Bool.false []))
    let value ← Meta.mkLambdaFVars #[x] (← Meta.mkEqRefl (.const ``Bool.false []))
    Lean.addDecl <| .thmDecl { name, levelParams := [], type, value }

/-- error: (kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit -/
#guard_msgs in
set_option maxRecDepth 256 in
run_meta addDeepWhnf `tooDeepWhnf

set_option maxRecDepth 100000 in
run_meta addDeepWhnf `deepEnoughWhnf
