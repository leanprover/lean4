import Lean

inductive Foo where
  | a | b | c

namespace Foo

scoped instance (priority := 10) inst1 : Inhabited Foo :=
  ⟨.a⟩

instance inst2 : Inhabited Foo :=
  ⟨.b⟩

open Lean Meta
def test (declName : Name)  : CoreM Unit := do
  IO.println s!"{declName}, priority: {← getInstancePriority? declName}, kind: {← getInstanceAttrKind? declName}"

#eval test `Foo.inst1
#eval test `Foo.inst2
