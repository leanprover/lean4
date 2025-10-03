import Std.Internal.UV
open Std.Internal.UV

def assertElapsed (t1 t2 : Nat) (should : Nat) (eps : Nat) : IO Unit := do
  let dur := t2 - t1
  if (Int.ofNat dur - Int.ofNat should).natAbs > eps then
    throw <| .userError s!"elapsed time was too different, measured {dur}, should: {should}, tolerance: {eps}"

def assertDuration (should : Nat) (eps : Nat) (x : IO α) : IO α := do
  let t1 ← IO.monoMsNow
  let res ← x
  let t2 ← IO.monoMsNow
  assertElapsed t1 t2 should eps
  return res


def BASE_DURATION : Nat := 1000

-- generous tolerance for slow CI systems
def EPS : Nat := 150

def await (x : Task α) : IO α := pure x.get


def cancelBehaviorNoRepeat : IO Unit := do
  let timer ← Timer.mk BASE_DURATION.toUInt64 false
  let prom ← timer.next
  assert! (← IO.getTaskState prom.result?) != IO.TaskState.finished
  timer.cancel
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  let prom ← timer.next
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished

def stopBehaviorNoRepeat : IO Unit := do
  let timer ← Timer.mk BASE_DURATION.toUInt64 false
  let prom ← timer.next
  assert! (← IO.getTaskState prom.result?) != IO.TaskState.finished
  timer.stop
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  assert! prom.result?.get == none
  let prom ← timer.next
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  assert! prom.result?.get == none
  let prom ← timer.next
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  assert! prom.result?.get == none
  let prom ← timer.next
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  assert! prom.result?.get == none
  let prom ← timer.next
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  assert! prom.result?.get == none

def cancelBehaviorRepeat : IO Unit := do
  let timer ← Timer.mk BASE_DURATION.toUInt64 true
  let prom ← timer.next
  IO.sleep 10
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  let prom ← timer.next
  IO.sleep 10
  assert! (← IO.getTaskState prom.result?) != IO.TaskState.finished
  timer.cancel
  IO.sleep 10
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  let prom ← timer.next
  IO.sleep 10
  assert! (← IO.getTaskState prom.result?) != IO.TaskState.finished
  timer.cancel
  IO.sleep 10
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  assert! prom.result?.get == none

def stopBehaviorRepeat : IO Unit := do
  let timer ← Timer.mk BASE_DURATION.toUInt64 true
  let prom ← timer.next
  assert! (← IO.getTaskState prom.result?) != IO.TaskState.finished
  IO.sleep 10
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  let prom ← timer.next
  IO.sleep 10
  assert! (← IO.getTaskState prom.result?) != IO.TaskState.finished
  timer.stop
  IO.sleep 10
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  assert! prom.result?.get == none

def stopCancelRepeat : IO Unit := do
  let timer ← Timer.mk 1000 true
  let prom ← timer.next
  assert! prom.result?.get == some ()
  let prom ← timer.next
  timer.stop
  timer.cancel
  timer.stop
  timer.cancel
  timer.stop
  timer.cancel
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  assert! prom.result?.get == none

def cancelStopRepeat : IO Unit := do
  let timer ← Timer.mk 1000 true
  let prom ← timer.next
  assert! prom.result?.get == some ()
  let prom ← timer.next
  timer.cancel
  timer.stop
  timer.cancel
  timer.stop
  timer.cancel
  timer.stop
  timer.cancel
  timer.stop
  IO.sleep 10
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  assert! prom.result?.get == none

def stopCancelNoRepeat : IO Unit := do
  let timer ← Timer.mk 1000 false
  let prom ← timer.next
  timer.stop
  timer.cancel
  timer.stop
  timer.cancel
  timer.stop
  timer.cancel
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  assert! prom.result?.get == none

def cancelStopNoRepeat : IO Unit := do
  let timer ← Timer.mk 1000 false
  let prom ← timer.next
  timer.cancel
  timer.stop
  timer.cancel
  timer.stop
  timer.cancel
  timer.stop
  timer.cancel
  timer.stop
  IO.sleep 10
  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  assert! prom.result?.get == none

def stopRepeat : IO Unit := do
  let timer ← Timer.mk 1000 true
  let prom ← timer.next

  assert! prom.result?.get == some ()

  timer.stop

  let prom ← timer.next

  assert! (← IO.getTaskState prom.result?) == IO.TaskState.finished
  assert! prom.result?.get == none

def cancelRepeat : IO Unit := do
  let timer ← Timer.mk 1000 true
  timer.cancel

  let prom ← timer.next
  assert! prom.result?.get == some ()

#eval cancelBehaviorNoRepeat
#eval stopBehaviorNoRepeat
#eval cancelBehaviorRepeat
#eval stopBehaviorRepeat

#eval stopCancelRepeat
#eval cancelStopRepeat
#eval stopCancelNoRepeat
#eval cancelStopNoRepeat

#eval stopRepeat
#eval cancelRepeat
