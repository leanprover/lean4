import Lean.Elab.Command

open Lean Elab Command

elab tk:"#guard_msg_kind " kind:ident " in " cmd:command : command => do
  let initMsgs ← modifyGet fun st => (st.messages, {st with messages := {}})
  elabCommandTopLevel cmd
  let msgs ← modifyGet fun st => (st.messages, {st with messages := initMsgs})
  let kind := kind.getId
  for msg in msgs.toList do
    if msg.kind != kind then
      logErrorAt tk s!"expected {kind}, got {msg.kind}"

/- Test inferring kind from a tag. -/
#guard_msg_kind custom in
run_cmd do logInfo <| .tagged `custom ""

/- Test trace message kind. -/
#guard_msg_kind trace in
set_option trace.Elab.step true in
def trace := ()

/- Test linter kind. -/
#guard_msg_kind linter.unusedVariables in
#guard_msgs (info) in -- hack to avoid re-triggering the linter
def unused (x : Unit) := ()
