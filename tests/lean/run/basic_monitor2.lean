meta def basic_monitor : vm_monitor nat :=
{ init := 1000,
  step := λ sz, do
    csz ← vm.call_stack_size,
    if sz = csz then return sz
    else do
      fn ← vm.curr_fn,
      vm.trace (to_fmt "[" ++ csz ++ "]: " ++ to_fmt fn),
      return csz }

run_command vm_monitor.register `basic_monitor

set_option debugger true

def f : nat → nat
| 0     := 0
| (a+1) := f a

vm_eval trace "a" (λ u, f 4)
