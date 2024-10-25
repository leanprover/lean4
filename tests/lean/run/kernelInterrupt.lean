import Lean.CoreM

/-!
Check that C++ exceptions are properly translated to Lean data.
In particular, runtime exceptions such as `interrupted_exception` should properly transition from
`libInit_shared` to `libleanshared`, which requires correct linking of the unwinding library.
 -/

open Lean
#guard_msgs in
#eval show CoreM _ from do
  let env ← getEnv
  let envPromise ← IO.Promise.new
  let tk ← IO.CancelToken.new
  let t := Task.spawn fun _ =>
    let env := envPromise.result.get
    let decl := .axiomDecl {
      name := `test
      levelParams := []
      type := mkConst `Nat
      isUnsafe := false
    }
    env.addDeclCore 1000 decl tk
  tk.set
  envPromise.resolve env
  assert! t.get matches .error .interrupted
