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

meta def obj_fmt (o : vm_obj) : vm format :=
match o^.kind with
| vm_obj_kind.tactic_state :=
     return (to_fmt "state:" ++ format.nest 8 (format.line ++ o^.to_tactic_state^.to_format))
| _ := do s ← vm.obj_to_string o, return $ to_fmt s
end

meta def display_args_aux : nat → vm unit
| i := do
   sz ← vm.stack_size,
   if i = sz then return ()
   else do
     o ← vm.stack_obj i,
     (n, t) ← vm.stack_obj_info i,
     fmt ← obj_fmt o,
     vm.trace (to_fmt "  " ++ to_fmt n ++ " := " ++ fmt),
     display_args_aux (i+1)

meta def display_args : vm unit :=
do bp ← vm.bp,
   display_args_aux bp

meta def basic_monitor : vm_monitor nat :=
{ init := 1000,
  step := λ sz, do
    csz ← vm.call_stack_size,
    if sz = csz then return sz
    else
      do {
      fn  ← vm.curr_fn,
      pos ← pos_info fn,
      vm.trace (to_fmt "[" ++ csz ++ "]: " ++ to_fmt fn ++ " @ " ++ pos),
      display_args,
      return csz
      }
      <|>
      return csz -- curr_fn failed
}


run_command vm_monitor.register `basic_monitor

set_option debugger true
open tactic

example (a b : Prop) : a → b → a ∧ b :=
by (intros >> constructor >> repeat assumption)
