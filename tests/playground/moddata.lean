import init.lean.environment
open Lean

def saveTestFile (fn : String) : IO Unit :=
saveModuleData fn {
  imports    := [`foo, `bla].toArray,
  constants  := Array.empty,
  entries    := Array.empty,
  serialized := [1, 2, 3, 4].toByteArray
}

def openTestFile (fn : String) : IO Unit :=
do m ← readModuleData fn,
   IO.println m.imports,
   IO.println m.serialized,
   pure ()

def main (xs : List String) : IO Unit :=
let fn := xs.head in
saveTestFile fn *>
openTestFile fn
