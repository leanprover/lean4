/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Attributes
import Lean.Declaration
import Lean.MonadEnv
import Lean.Elab.InfoTree

namespace Lean.Compiler

/--
Instructs the compiler to use a different function as implementation for a function.
Similarly to `@[extern]`, this causes the function to not be compiled and all compiler related
attributes (e.g. `noncomputable`, `@[inline]`) to be ignored.

The most common use cases of `@[implemented_by]` are to provide an efficient unsafe implementation
and to make an unsafe function accessible through an opaque function:

```
unsafe def fooUnsafe (x : Bool) : UInt8 := unsafeCast x

@[implemented_by fooUnsafe]
def foo : Bool → UInt8 | false => 0 | true => 1

unsafe def barUnsafe (x : Nat) : Nat := ...

@[implemented_by barUnsafe]
opaque bar (x : Nat) : Nat
```

Note: the provided implementation will not be checked to be correct, thus making it possible to
prove `False` with `native_decide` using incorrect implementations. For a safer variant of this
attribute that however only works for providing safe implementations, see `@[csimp]`.
-/
@[builtin_doc]
builtin_initialize implementedByAttr : ParametricAttribute Name ← registerParametricAttribute {
  name := `implemented_by
  descr := "name of the Lean (probably unsafe) function that implements opaque constant"
  getParam := fun declName stx => do
    let decl ← getConstInfo declName
    let fnNameStx ← Attribute.Builtin.getIdent stx
    let fnName ← Elab.realizeGlobalConstNoOverloadWithInfo fnNameStx
    let fnDecl ← getConstVal fnName
    unless decl.levelParams.length == fnDecl.levelParams.length do
      throwError "invalid 'implemented_by' argument '{fnName}', '{fnName}' has {fnDecl.levelParams.length} universe level parameter(s), but '{declName}' has {decl.levelParams.length}"
    let declType := decl.type
    let fnType ← Core.instantiateTypeLevelParams fnDecl (decl.levelParams.map mkLevelParam)
    unless declType == fnType do
      throwError "invalid 'implemented_by' argument '{fnName}', '{fnName}' has type{indentExpr fnType}\nbut '{declName}' has type{indentExpr declType}"
    if decl.name == fnDecl.name then
      throwError "invalid 'implemented_by' argument '{fnName}', function cannot be implemented by itself"
    return fnName
}

@[export lean_get_implemented_by]
def getImplementedBy? (env : Environment) (declName : Name) : Option Name :=
  implementedByAttr.getParam? env declName

def setImplementedBy (env : Environment) (declName : Name) (impName : Name) : Except String Environment :=
  implementedByAttr.setParam env declName impName

end Compiler

def setImplementedBy {m} [Monad m] [MonadEnv m] [MonadError m] (declName : Name) (impName : Name) : m Unit := do
  let env ← getEnv
  match Compiler.setImplementedBy env declName impName with
  | Except.ok env   => setEnv env
  | Except.error ex => throwError ex

end Lean
