import Lean
open Lean


def foo (x : Nat) : Nat :=
  x + x + x

#eval (do
  let env ← getEnv
  IR.emitC env `myModule |> IO.println 
  let res ← IR.emitLLVM env `myModule 
  IO.println res
  : MetaM Unit)

def test : MetaM Unit := do
  let env ← getEnv
  -- let module := env.mainModule
  let res ← IR.emitLLVM env `myModule
  IO.println res

-- #eval test

def test2 : MetaM Unit := do
  let env ← getEnv
  let module := env.mainModule
  IO.println $ (IR.getDecls env).map (·.name)

-- #eval test2

def showIR (n : Name) : MetaM Unit := do
  let env ← getEnv
  let myDecls := IR.getDecls env
  if let some decl := IR.findEnvDecl env n then
    IO.println decl
  else
    throwError "not found"

#eval showIR ``foo
-- #eval showIR `test._rarg._closed_1
