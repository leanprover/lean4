import init.lean.environment
open Lean

def mkMyExt : IO (EnvExtension (Array Nat)) :=
registerEnvExtension [1, 2, 3].toArray

@[init mkMyExt]
constant myExt : EnvExtension (Array Nat) := default _

def showMyExt (env : Environment) : IO Unit :=
IO.println $ myExt.getState env

def addVal (env : Environment) (n : Nat) : Environment :=
myExt.modifyState env $ λ as, as.push n

def main : IO Unit :=
do
env ← mkEmptyEnvironment,
showMyExt env,
let env := addVal env 10,
showMyExt env,
let env := addVal env 20,
showMyExt env,
pure ()
