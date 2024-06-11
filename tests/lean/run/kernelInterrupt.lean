import Lean.CoreM

/-!
Check that C++ exceptions are properly translated to Lean data.
In particular, runtime exceptions such as `interrupted_exception` should properly transition from
`libInit_shared` to `libleanshared`, which requires correct linking of the unwinding library.
 -/

open Lean
/-- info: -/
#guard_msgs in
#eval show CoreM _ from do
  let env ← getEnv
  let envPromise ← IO.Promise.new
  let t := Task.spawn fun _ =>
    let env := envPromise.result.get
    Kernel.whnf env {} (mkApp2 (mkConst `Nat.add) (mkNatLit 1) (mkNatLit 2))
  IO.cancel t
  envPromise.resolve env
  assert! t.get matches .error .interrupted
