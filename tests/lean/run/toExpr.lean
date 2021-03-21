import Lean

open Lean

unsafe def test {α : Type} [ToString α] [ToExpr α] [BEq α] (a : α) : CoreM Unit := do
let env ← getEnv;
let auxName := `_toExpr._test;
let decl := Declaration.defnDecl {
  name        := auxName,
  levelParams := [],
  value       := toExpr a,
  type        := toTypeExpr α,
  hints       := ReducibilityHints.abbrev,
  safety      := DefinitionSafety.safe
};
IO.println (toExpr a);
(match env.addAndCompile {} decl with
| Except.error _ => throwError "addDecl failed"
| Except.ok env  =>
  match env.evalConst α {} auxName with
  | Except.error ex => throwError ex
  | Except.ok b => do
    IO.println b;
    unless a == b do
      throwError "toExpr failed";
    pure ())

#eval test #[(1, 2), (3, 4)]
#eval test ['a', 'b', 'c']
#eval test ("hello", true)
#eval test ((), 10)
