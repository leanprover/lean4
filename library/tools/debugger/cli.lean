/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Simple command line interface for debugging Lean programs and tactics.
-/
import tools.debugger.util

namespace debugger

@[derive decidable_eq]
inductive mode
| init | step | run | done

structure state :=
(md         : mode)
(csz        : nat)
(fn_bps     : list name)
(active_bps : list (nat × name))

def init_state : state :=
{ md := mode.init, csz := 0,
  fn_bps := [], active_bps := [] }

meta def show_help : vm unit :=
do
 vm.put_str "exit       - stop debugger\n",
 vm.put_str "help       - display this message\n",
 vm.put_str "run        - continue execution\n",
 vm.put_str "step       - execute until another function in on the top of the stack\n",
 vm.put_str "stack trace\n",
 vm.put_str " up        - move up in the stack trace\n",
 vm.put_str " down      - move down in the stack trace\n",
 vm.put_str " vars      - display variables in the current stack frame\n",
 vm.put_str " stack     - display all functions on the call stack\n",
 vm.put_str " print var - display the value of variable named 'var' in the current stack frame\n",
 vm.put_str " pidx  idx - display the value of variable at position #idx in the current stack frame\n",
 vm.put_str "breakpoints\n",
 vm.put_str " break fn  - add breakpoint for fn\n",
 vm.put_str " rbreak fn - remove breakpoint\n",
 vm.put_str " bs        - show breakpoints\n"

meta def add_breakpoint (s : state) (args : list string) : vm state :=
match args with
| [arg] := do
  fn ← return $ to_qualified_name arg,
  ok ← is_valid_fn_prefix fn,
  if ok then
    return { fn_bps := fn :: list.filter (λ fn', fn ≠ fn') s.fn_bps, ..s }
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
  return { fn_bps := list.filter (λ fn', fn ≠ fn') s.fn_bps, ..s }
| _     :=
  vm.put_str "invalid 'rbreak <fn>' command, incorrect number of arguments\n" >>
  return s
end

meta def show_breakpoints : list name → vm unit
| []        := return ()
| (fn::fns) := do
  vm.put_str "  ",
  vm.put_str fn.to_string,
  vm.put_str "\n",
  show_breakpoints fns

meta def up_cmd (frame : nat) : vm nat :=
if frame = 0 then return 0
else show_frame (frame - 1) >> return (frame - 1)

meta def down_cmd (frame : nat) : vm nat :=
do sz ← vm.call_stack_size,
   if frame >= sz - 1 then return frame
   else show_frame (frame + 1) >> return (frame + 1)

meta def pidx_cmd : nat → list string → vm unit
| frame [arg] := do
  idx     ← return $ arg.to_nat,
  sz      ← vm.stack_size,
  (bp, ep) ← vm.call_stack_var_range frame,
  if bp + idx >= ep then
    vm.put_str "invalid 'pidx <idx>' command, index out of bounds\n"
  else do
    v       ← vm.pp_stack_obj (bp+idx),
    (n, t)  ← vm.stack_obj_info (bp+idx),
    opts    ← vm.get_options,
    vm.put_str n.to_string,
    vm.put_str " := ",
    vm.put_str $ v.to_string opts,
    vm.put_str "\n"
| _ _ :=
  vm.put_str "invalid 'pidx <idx>' command, incorrect number of arguments\n"

meta def print_var : nat → nat → name → vm unit
| i ep v := do
  if i = ep then vm.put_str "invalid 'print <var>', unknown variable\n"
  else do
    (n, t) ← vm.stack_obj_info i,
    if n = v then do
       v    ← vm.pp_stack_obj i,
       opts ← vm.get_options,
       vm.put_str n.to_string,
       vm.put_str " := ",
       vm.put_str $ v.to_string opts,
       vm.put_str "\n"
    else
       print_var (i+1) ep v

meta def print_cmd : nat → list string → vm unit
| frame [arg] := do
  (bp, ep) ← vm.call_stack_var_range frame,
  print_var bp ep (to_qualified_name arg)
| _ _ :=
  vm.put_str "invalid 'print <var>' command, incorrect number of arguments\n"

meta def cmd_loop_core : state → nat → list string → vm state
| s frame default_cmd := do
  is_eof ← vm.eof,
  if is_eof then do
    vm.put_str "stopping debugger... 'end of file' has been found\n",
    return { md := mode.done, ..s }
  else do
    vm.put_str "% ",
    l ← vm.get_line,
    tks ← return $ split l,
    tks ← return $ if tks = [] then default_cmd else tks,
    match tks with
    | []          := cmd_loop_core s frame default_cmd
    | (cmd::args) :=
      if cmd = "help" ∨ cmd = "h" then show_help >> cmd_loop_core s frame []
      else if cmd = "exit" then return { md := mode.done, ..s }
      else if cmd = "run" ∨ cmd = "r" then return { md := mode.run, ..s }
      else if cmd = "step" ∨ cmd = "s" then return { md := mode.step, ..s }
      else if cmd = "break" ∨ cmd = "b" then do new_s ← add_breakpoint s args, cmd_loop_core new_s frame []
      else if cmd = "rbreak" then do new_s ← remove_breakpoint s args, cmd_loop_core new_s frame []
      else if cmd = "bs" then do
        vm.put_str "breakpoints\n",
        show_breakpoints s.fn_bps,
        cmd_loop_core s frame default_cmd
      else if cmd = "up" ∨ cmd = "u" then do frame ← up_cmd frame, cmd_loop_core s frame ["u"]
      else if cmd = "down" ∨ cmd = "d" then do frame ← down_cmd frame, cmd_loop_core s frame ["d"]
      else if cmd = "vars" ∨ cmd = "v" then do show_vars frame, cmd_loop_core s frame []
      else if cmd = "stack" then do show_stack, cmd_loop_core s frame []
      else if cmd = "pidx" then do pidx_cmd frame args, cmd_loop_core s frame []
      else if cmd = "print" ∨ cmd = "p" then do print_cmd frame args, cmd_loop_core s frame []
      else do vm.put_str "unknown command, type 'help' for help\n", cmd_loop_core s frame default_cmd
    end

meta def cmd_loop (s : state) (default_cmd : list string) : vm state :=
do csz ← vm.call_stack_size,
   cmd_loop_core s (csz - 1) default_cmd

def prune_active_bps_core (csz : nat) : list (nat × name) → list (nat × name)
| []              := []
| ((csz', n)::ls) := if csz < csz' then prune_active_bps_core ls else ((csz',n)::ls)

meta def prune_active_bps (s : state) : vm state :=
do sz ← vm.call_stack_size,
   return { active_bps := prune_active_bps_core sz s.active_bps, ..s }

meta def updt_csz (s : state) : vm state :=
do sz ← vm.call_stack_size,
   return { csz := sz, ..s }

meta def init_transition (s : state) : vm state :=
do opts ← vm.get_options,
   if opts.get_bool `server ff then return { md := mode.done, ..s }
   else do
     bps   ← vm.get_attribute `breakpoint,
     new_s ← return { fn_bps := bps, ..s },
     if opts.get_bool `debugger.autorun ff then
       return { md := mode.run, ..new_s }
     else do
       vm.put_str "Lean debugger\n",
       show_curr_fn "debugging",
       vm.put_str "type 'help' for help\n",
       cmd_loop new_s []

meta def step_transition (s : state) : vm state :=
do
  sz ← vm.call_stack_size,
  if sz = s.csz then return s
  else do
    show_curr_fn "step",
    cmd_loop s ["s"]

meta def bp_reached (s : state) : vm bool :=
(do fn    ← vm.curr_fn,
    return $ s.fn_bps.any (λ p, p.is_prefix_of fn))
<|>
return ff

meta def in_active_bps (s : state) : vm bool :=
do sz ← vm.call_stack_size,
   match s.active_bps with
   | []          := return ff
   | (csz, _)::_ := return (sz = csz)
   end

meta def run_transition (s : state) : vm state :=
do b1 ← in_active_bps s,
   b2 ← bp_reached s,
   if b1 ∨ not b2 then return s
   else do
     show_curr_fn "breakpoint",
     fn    ← vm.curr_fn,
     sz    ← vm.call_stack_size,
     new_s ← return $ { active_bps := (sz, fn) :: s.active_bps, ..s },
     cmd_loop new_s ["r"]

meta def step_fn (s : state) : vm state :=
do s ← prune_active_bps s,
   if s.md = mode.init then do new_s ← init_transition s, updt_csz new_s
   else if s.md = mode.done then return s
   else if s.md = mode.step then do new_s ← step_transition s, updt_csz new_s
   else if s.md = mode.run  then do new_s ← run_transition s, updt_csz new_s
   else return s

@[vm_monitor]
meta def monitor : vm_monitor state :=
{ init := init_state, step := step_fn }
end debugger
