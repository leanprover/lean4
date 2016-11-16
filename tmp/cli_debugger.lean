namespace cli_debugger

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
 vm.put_str "exit     - stop debugger\n",
 vm.put_str "help     - display this message\n",
 vm.put_str "run      - continue execution\n",
 vm.put_str "break fn - add breakpoint for fn\n",
 vm.put_str "bs       - show breakpoints\n",
 vm.put_str "step     - execute until another function in on the top of the stack\n"

meta def add_breakpoint (s : state) (args : list string) : vm state :=
match args with
| [arg] := do
  fn ← return $ to_qualified_name arg,
  return {s with fn_bps := fn :: list.filter (λ fn', fn ≠ fn') s^.fn_bps}
| _     :=
  vm.put_str "invalid 'break <fn>' command, incorrect number of arguments\n" >>
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
      else if cmd = "run" then return {s with md := mode.run }
      else if cmd = "step" ∨ cmd = "s" then return {s with md := mode.step }
      else if cmd = "break" ∨ cmd = "b" then do new_s ← add_breakpoint s args, cmd_loop new_s default_cmd
      else if cmd = "bs" then do
        vm.put_str "breakpoints\n",
        show_breakpoints s^.fn_bps,
        cmd_loop s default_cmd
      else do vm.put_str "unknown command, type 'help' for help\n", cmd_loop s default_cmd
    end

def updt_active_bps (csz : nat) : list (nat × name) → list (nat × name)
| []              := []
| ((csz', n)::ls) := if csz < csz' then updt_active_bps ls else ((csz',n)::ls)

meta def updt_state (s : state) : vm state :=
do sz ← vm.call_stack_size,
   return {s with csz := sz, active_bps := updt_active_bps sz s^.active_bps}

meta def init_transition (s : state) : vm state :=
do opts ← vm.get_options,
   if opts^.get_bool `server ff then return {s with md := mode.done}
   else do
     vm.put_str "Lean debugger\n",
     display_curr_fn "debugging",
     vm.put_str "type 'help' for help\n",
     sz ← vm.call_stack_size,
     new_s ← cmd_loop s [],
     updt_state new_s

meta def step_transition (s : state) : vm state :=
do
  sz ← vm.call_stack_size,
  if sz = s^.csz then return s
  else do
    display_curr_fn "step",
    new_s ← cmd_loop s ["s"],
    updt_state new_s

meta def run_transition (s : state) : vm state :=
-- TODO(Leo): check breakpoints
updt_state s

meta def step_fn (s : state) : vm state :=
if s^.md = mode.init then init_transition s
else if s^.md = mode.done then return s
else if s^.md = mode.step then step_transition s
else if s^.md = mode.run  then run_transition s
else return s

meta def monitor : vm_monitor state :=
{ init := init_state, step := step_fn }

end cli_debugger

run_command vm_monitor.register `cli_debugger.monitor

set_option debugger true

def g (a : nat) := a + 1

def f : nat → nat
| 0     := g 0
| (a+1) := f a

vm_eval f 3
