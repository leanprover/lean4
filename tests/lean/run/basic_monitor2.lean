meta def get_file (fn : name) : vm format :=
do {
  d ← vm.get_decl fn,
  some n ← return (vm_decl.olean d) | failure,
  return (to_fmt n)
}
<|>
return (to_fmt "<curr file>")

meta def pos_info (fn : name) : vm format :=
do {
  d                ← vm.get_decl fn,
  some (line, col) ← return (vm_decl.pos d) | failure,
  file             ← get_file fn,
  return (file ++ ":" ++ line ++ ":" ++ col)
}
<|>
return (to_fmt "<position not available>")

meta def basic_monitor : vm_monitor nat :=
{ init := 1000,
  step := λ sz, do
    csz ← vm.call_stack_size,
    if sz = csz then return sz
    else do
      fn  ← vm.curr_fn,
      pos ← pos_info fn,
      vm.trace (to_fmt "[" ++ csz ++ "]: " ++ to_fmt fn ++ " @ " ++ pos),
      return csz }

run_command vm_monitor.register `basic_monitor

set_option debugger true

def f : nat → nat
| 0     := 0
| (a+1) := f a

vm_eval trace "a" (λ u, f 4)
