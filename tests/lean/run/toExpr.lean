import Init.Lean

open Lean

unsafe def test {α : Type} [HasToString α] [ToExpr α] [HasBeq α] (a : α) : MetaIO Unit := do
env ← MetaIO.getEnv;
let auxName := `_toExpr._test;
let decl := Declaration.defnDecl {
  name     := auxName,
  lparams  := [],
  value    := toExpr a,
  type     := toTypeExpr α,
  hints    := ReducibilityHints.abbrev,
  isUnsafe := false
};
IO.println (toExpr a);
match env.addAndCompile {} decl with
| Except.error _ => throw $ IO.userError "addDecl failed"
| Except.ok env  => do
  match env.evalConst α auxName with
  | Except.error ex => throw $ IO.userError ex
  | Except.ok b => do
    IO.println b;
    unless (a == b) $
      throw $ IO.userError "toExpr failed";
    pure ()

#eval test #[(1, 2), (3, 4)]
#eval test ['a', 'b', 'c']
#eval test ("hello", true)
#eval test ((), 10)
