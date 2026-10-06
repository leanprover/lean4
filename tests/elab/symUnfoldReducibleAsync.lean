import Lean

/-!
`cbv` preprocesses the local context with `Sym`, which hash-conses the value of `h` and looks up
the reducibility of every constant in that value, including the theorem `waiter`. The proof of
`waiter` finishes only after the proof of `user` runs `cbv`, so the reducibility lookup of `waiter`
must not wait for the proof of `waiter`.
-/

set_option Elab.async true

def marker : System.FilePath := "symUnfoldReducibleAsync.marker"

#eval show IO Unit from do if ← marker.pathExists then IO.FS.removeFile marker

elab "await_marker" : tactic => do
  for _ in [0:400] do
    if ← marker.pathExists then
      IO.FS.removeFile marker
      return
    IO.sleep 50
  throwError "`user` did not finish `cbv` within 20 seconds"

elab "signal_marker" : tactic => IO.FS.writeFile marker ""

theorem waiter : True := by
  await_marker
  trivial

theorem user : 2 + 2 = 4 := by
  have h := And.intro waiter waiter
  cbv
  signal_marker
