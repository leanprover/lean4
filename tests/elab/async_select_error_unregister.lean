import Std.Async.Select
open Std Async

private def trackingSelector (unregCount : IO.Ref Nat) : Selector Unit where
  tryFn := pure none
  registerFn _ := pure ()
  unregisterFn := unregCount.modify (· + 1)

private def delayedErrorSelector (ms : UInt32) (e : IO.Error) : Selector Unit where
  tryFn := pure none

  registerFn waiter := discard <| IO.asTask (prio := .dedicated) do
    IO.sleep ms
    waiter.race (lose := pure ()) (win := fun p => p.resolve (.error e))

  unregisterFn := pure ()

private def throwingRegisterSelector (e : IO.Error) : Selector Unit where
  tryFn := pure none
  registerFn _ := throw e
  unregisterFn := pure ()

def testErrorResolutionUnregistersSiblings : Async Bool := do
  let mut ok := true
  for _ in List.range 50 do
    let cnt ← IO.mkRef 0
    let mut threw := false
    try
      discard <| Selectable.one #[
        .case (delayedErrorSelector 5 (.userError "boom")) fun _ => pure 0,
        .case (trackingSelector cnt) fun _ => pure 0,
      ]
    catch _ =>
      threw := true
    if !threw || (← cnt.get) != 1 then ok := false
  return ok

/-- info: true -/
#guard_msgs in
#eval testErrorResolutionUnregistersSiblings.block

def testRegisterFailureUnregistersSiblings : Async Bool := do
  let mut ok := true
  for _ in List.range 50 do
    let cnt ← IO.mkRef 0
    let mut threw := false
    try
      discard <| Selectable.one #[
        .case (throwingRegisterSelector (.userError "register boom")) fun _ => pure 0,
        .case (trackingSelector cnt) fun _ => pure 0,
      ]
    catch _ =>
      threw := true
    if !threw || (← cnt.get) != 1 then ok := false
  return ok

/-- info: true -/
#guard_msgs in
#eval testRegisterFailureUnregistersSiblings.block
