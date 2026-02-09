import Lean

open Lean

unsafe def test {α : Type} [ToString α] [ToExpr α] [BEq α] (a : α) : CoreM Unit := do
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
let oldEnv ← getEnv;
addAndCompile decl;
let newEnv ← getEnv
setEnv oldEnv
match newEnv.evalConst α {} auxName with
| Except.error ex => throwError ex
| Except.ok b => do
  IO.println b;
  unless a == b do
    throwError "toExpr failed";
  pure ()

#eval test #[(1, 2), (3, 4)]
#eval test ['a', 'b', 'c']
#eval test ("hello", true)
#eval test ((), 10)
#eval test (1:Rat)
#eval test (-1:Rat)
#eval test (2:Rat)
#eval test (-2:Rat)
#eval test (1/(-2):Rat)
#eval test (-2/3:Rat)
#eval test (-2/1:Rat)
#eval test (-20/3:Rat)
#eval test (-1.234:Rat)
#eval test (0.67:Rat)

open Lean Meta
def testRat (n : Rat) : MetaM Unit := do
  let e := toExpr n
  IO.println e
  let some n' ← getRatValue? e | throwError "`Rat` expected{indentExpr e}"
  IO.println n'
  assert! n == n'

#eval testRat 0
#eval testRat 1
#eval testRat (1/2)
#eval testRat (1/(-2))
#eval testRat (2/3)
#eval testRat (0.67)
#eval testRat (1.67)
#eval testRat (1.68)
#eval testRat (-1.67)
#eval testRat (-2)
#eval testRat (-0.67)
