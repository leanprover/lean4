import Lean

/-!
After instance synthesis, `applyAbstractResult?` runs `check` on the result to propagate universe
constraints (#796). The query below contains `Bar.{?w, v} X`, which is type-correct only modulo the
constraint `max ?w v =?= max u v`. That constraint is not a pattern, so `isDefEq` postpones it where
`?w` is assignable. One metavariable depth deeper, `?w` is read-only, and `check` used to throw
`Application type mismatch` out of `synthInstance?` (as in Mathlib's
`ModuleCat.FilteredColimits.colimitCocone` under the strict instance checks). Now synthesis keeps
the result, because the query itself is not type-correct at that depth either.
-/

open Lean Meta

universe u v w
structure Bar (α : Type (max w v)) : Type where
class Foo (β : Type) : Type where
instance instFoo (β : Type) : Foo β := ⟨⟩

def run (deeper : Bool) : MetaM Unit := do
  let u := mkLevelParam `u
  let v := mkLevelParam `v
  withLocalDeclD `X (mkSort (mkLevelSucc (mkLevelMax u v))) fun X => do
    let w ← mkFreshLevelMVar
    let q := mkApp (mkConst ``Foo) (mkApp (mkConst ``Bar [w, v]) X)
    let go : MetaM Unit := do
      logInfo m!"result: {← synthInstance? q}"
    if deeper then withNewMCtxDepth go else go

/-- info: result: instFoo (Bar X) -/
#guard_msgs in
#eval run false

/-- info: result: instFoo (Bar X) -/
#guard_msgs in
#eval run true
