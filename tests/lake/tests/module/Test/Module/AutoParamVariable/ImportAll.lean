module
import Lean
import all Test.Module.AutoParamVariable.A
import all Test.Module.AutoParamVariable.B

/-! Regression test for #14708: public and private autoParam helpers coexist under `import all`. -/

example : True.intro = True.intro := AutoParamVariableA.explicitPublic
example : True.intro = True.intro := AutoParamVariableB.sectionPublic
example : True.intro = True.intro := AutoParamVariableA.privateTheorem

open Lean Elab Command in
run_cmd do
  let .forallE _ type _ _ := (← getConstInfo ``AutoParamVariableA.privateTheorem).type
    | throwError "expected binder"
  let some (.const helper _) := type.getAutoParamTactic? | throwError "expected helper"
  unless isPrivateName helper do
    throwError "expected private helper"
  withExporting do
    if (← getEnv).contains helper then
      throwError "private helper must not be exported"
