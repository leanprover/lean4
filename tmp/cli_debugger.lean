namespace debugger

inductive mode
| init | step | run | done

instance : decidable_eq mode :=
by tactic.mk_dec_eq_instance

structure state :=
(md         : mode)
(csz        : nat)
(fn_bps     : list name)
(active_bps : list (nat × name))

def init_state : state :=
{ md := mode.init, csz := 0,
  fn_bps := [], active_bps := [] }

def is_space (c : char) : bool :=
if c = ' ' ∨ c = char.of_nat 11 ∨ c = '\n' then tt else ff

def split_core : string → string → list string
| (c::cs) [] :=
  if is_space c then split_core cs [] else split_core cs [c]
| (c::cs) r  :=
  if is_space c then r^.reverse :: split_core cs [] else split_core cs (c::r)
| []      [] := []
| []      r  := [r^.reverse]

def split (s : string) : list string :=
(split_core s [])^.reverse

def to_qualified_name_core : string → string → name
| []      r := if r = [] then name.anonymous else mk_simple_name r^.reverse
| (c::cs) r :=
  if is_space c then to_qualified_name_core cs r
  else if c = '.' then
       if r = [] then to_qualified_name_core cs []
       else           name.mk_string r^.reverse (to_qualified_name_core cs [])
  else to_qualified_name_core cs (c::r)

def to_qualified_name (s : string) : name :=
to_qualified_name_core s []

meta def get_file (fn : name) : vm string :=
do {
  d ← vm.get_decl fn,
  some n ← return (vm_decl.olean d) | failure,
  return n
}
<|>
return "<curr file>"

meta def pos_info (fn : name) : vm string :=
do {
  d                ← vm.get_decl fn,
  some (line, col) ← return (vm_decl.pos d) | failure,
  file             ← get_file fn,
  return (file ++ ":" ++ line^.to_string ++ ":" ++ col^.to_string)
}
<|>
return "<position not available>"

meta def display_curr_fn (header : string) : vm unit :=
do fn ← vm.curr_fn,
   pos ← pos_info fn,
   sz ← vm.call_stack_size,
   vm.put_str ("[" ++ sz^.to_string ++ "] " ++ header ++ " " ++ fn^.to_string ++ " at " ++ pos ++ "\n")

meta def display_help : vm unit :=
do
 vm.put_str "exit      - stop debugger\n",
 vm.put_str "help      - display this message\n",
 vm.put_str "run       - continue execution\n",
 vm.put_str "step      - execute until another function in on the top of the stack\n",
 vm.put_str "breakpoints\n",
 vm.put_str " break fn  - add breakpoint for fn\n",
 vm.put_str " rbreak fn - remove breakpoint\n",
 vm.put_str " bs        - show breakpoints\n"

meta def is_valid_fn_prefix (p : name) : vm bool :=
do env ← vm.get_env,
   return $ env^.fold ff (λ d r,
     r ||
     let n := d^.to_name in
     p^.is_prefix_of n)

meta def add_breakpoint (s : state) (args : list string) : vm state :=
match args with
| [arg] := do
  fn ← return $ to_qualified_name arg,
  ok ← is_valid_fn_prefix fn,
  if ok then
    return {s with fn_bps := fn :: list.filter (λ fn', fn ≠ fn') s^.fn_bps}
  else
    vm.put_str "invalid 'break' command, given name is not the prefix for any function\n" >>
    return s
| _     :=
  vm.put_str "invalid 'break <fn>' command, incorrect number of arguments\n" >>
  return s
end

meta def remove_breakpoint (s : state) (args : list string) : vm state :=
match args with
| [arg] := do
  fn ← return $ to_qualified_name arg,
  return {s with fn_bps := list.filter (λ fn', fn ≠ fn') s^.fn_bps}
| _     :=
  vm.put_str "invalid 'rbreak <fn>' command, incorrect number of arguments\n" >>
  return s
end

meta def show_breakpoints : list name → vm unit
| []        := return ()
| (fn::fns) := do
  vm.put_str "  ",
  vm.put_str fn^.to_string,
  vm.put_str "\n",
  show_breakpoints fns

meta def cmd_loop : state → list string → vm state
| s default_cmd := do
  is_eof ← vm.eof,
  if is_eof then do
    vm.put_str "stopping debugger... 'end of file' has been found\n",
    return {s with md := mode.done }
  else do
    vm.put_str "% ",
    l ← vm.get_line,
    tks ← return $ split l,
    tks ← return $ if tks = [] then default_cmd else tks,
    match tks with
    | []          := cmd_loop s default_cmd
    | (cmd::args) :=
      if cmd = "help" then display_help >> cmd_loop s default_cmd
      else if cmd = "exit" then return {s with md := mode.done }
      else if cmd = "run" ∨ cmd = "r" then return {s with md := mode.run }
      else if cmd = "step" ∨ cmd = "s" then return {s with md := mode.step }
      else if cmd = "break" ∨ cmd = "b" then do new_s ← add_breakpoint s args, cmd_loop new_s default_cmd
      else if cmd = "rbreak" then do new_s ← remove_breakpoint s args, cmd_loop new_s default_cmd
      else if cmd = "bs" then do
        vm.put_str "breakpoints\n",
        show_breakpoints s^.fn_bps,
        cmd_loop s default_cmd
      else do vm.put_str "unknown command, type 'help' for help\n", cmd_loop s default_cmd
    end

def prune_active_bps_core (csz : nat) : list (nat × name) → list (nat × name)
| []              := []
| ((csz', n)::ls) := if csz < csz' then prune_active_bps_core ls else ((csz',n)::ls)

meta def prune_active_bps (s : state) : vm state :=
do sz ← vm.call_stack_size,
   return {s with active_bps := prune_active_bps_core sz s^.active_bps}

meta def updt_csz (s : state) : vm state :=
do sz ← vm.call_stack_size,
   return {s with csz := sz}

meta def init_transition (s : state) : vm state :=
do opts ← vm.get_options,
   if opts^.get_bool `server ff then return {s with md := mode.done}
   else do
     bps   ← vm.get_attribute `breakpoint,
     new_s ← return {s with fn_bps := bps},
     vm.put_str "Lean debugger\n",
     display_curr_fn "debugging",
     vm.put_str "type 'help' for help\n",
     cmd_loop new_s []

meta def step_transition (s : state) : vm state :=
do
  sz ← vm.call_stack_size,
  if sz = s^.csz then return s
  else do
    display_curr_fn "step",
    cmd_loop s ["s"]

meta def bp_reached (s : state) : vm bool :=
do fn    ← vm.curr_fn,
   return $ s^.fn_bps^.any (λ p, p^.is_prefix_of fn)

meta def in_active_bps (s : state) : vm bool :=
do sz ← vm.call_stack_size,
   match s^.active_bps with
   | []          := return ff
   | (csz, _)::_ := return $ to_bool (sz = csz)
   end

meta def run_transition (s : state) : vm state :=
do b1 ← in_active_bps s,
   b2 ← bp_reached s,
   if b1 ∨ not b2 then return s
   else do
     display_curr_fn "breakpoint",
     fn    ← vm.curr_fn,
     sz    ← vm.call_stack_size,
     new_s ← return $ {s with active_bps := (sz, fn) :: s^.active_bps},
     cmd_loop new_s ["r"]

meta def step_fn (s : state) : vm state :=
do s ← prune_active_bps s,
   if s^.md = mode.init then do new_s ← init_transition s, updt_csz new_s
   else if s^.md = mode.done then return s
   else if s^.md = mode.step then do new_s ← step_transition s, updt_csz new_s
   else if s^.md = mode.run  then do new_s ← run_transition s, updt_csz new_s
   else return s

meta def monitor : vm_monitor state :=
{ init := init_state, step := step_fn }

def attr : user_attribute :=
{ name  := `breakpoint,
  descr := "breakpoint for debugger" }

end debugger

run_command vm_monitor.register `debugger.monitor
run_command attribute.register `debugger.attr

set_option debugger true

def g (a : nat) := a + 1

def h (a : nat) := g a + 1

def s (a : nat) := h a + h a

local attribute [breakpoint] h

def f : nat → nat
| 0     := s 0
| (a+1) := f a

vm_eval f 3
