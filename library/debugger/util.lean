/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
namespace debugger
def is_space (c : char) : bool :=
if c = #" " ∨ c = char.of_nat 11 ∨ c = #"\n" then tt else ff

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
  else if c = #"." then
       if r = [] then to_qualified_name_core cs []
       else           name.mk_string r^.reverse (to_qualified_name_core cs [])
  else to_qualified_name_core cs (c::r)

def to_qualified_name (s : string) : name :=
to_qualified_name_core s []

def olean_to_lean (s : string) :=
list.dropn 5 s ++ "lean"

meta def get_file (fn : name) : vm string :=
do {
  d ← vm.get_decl fn,
  some n ← return (vm_decl.olean d) | failure,
  return (olean_to_lean n)
}
<|>
return "[current file]"

meta def pos_info (fn : name) : vm string :=
do {
  d                ← vm.get_decl fn,
  some (line, col) ← return (vm_decl.pos d) | failure,
  file             ← get_file fn,
  return (file ++ ":" ++ line^.to_string ++ ":" ++ col^.to_string)
}
<|>
return "<position not available>"

meta def show_fn (header : string) (fn : name) (frame : nat) : vm unit :=
do pos ← pos_info fn,
   vm.put_str ("[" ++ frame^.to_string ++ "] " ++ header),
   if header = "" then return () else vm.put_str " ",
   vm.put_str (fn^.to_string ++ " at " ++ pos ++ "\n")

meta def show_curr_fn (header : string) : vm unit :=
do fn ← vm.curr_fn,
   sz ← vm.call_stack_size,
   show_fn header fn (sz-1)

meta def is_valid_fn_prefix (p : name) : vm bool :=
do env ← vm.get_env,
   return $ env^.fold ff (λ d r,
     r ||
     let n := d^.to_name in
     p^.is_prefix_of n)

meta def show_frame (frame_idx : nat) : vm unit :=
do sz ← vm.call_stack_size,
   fn ← if frame_idx >= sz then vm.curr_fn else vm.call_stack_fn frame_idx,
   show_fn "" fn frame_idx

meta def type_to_string : option expr → nat → vm string
| none i := do
  o ← vm.stack_obj i,
  match o^.kind with
  | vm_obj_kind.simple       := return "[tagged value]"
  | vm_obj_kind.constructor  := return "[constructor]"
  | vm_obj_kind.closure      := return "[closure]"
  | vm_obj_kind.mpz          := return "[big num]"
  | vm_obj_kind.name         := return "name"
  | vm_obj_kind.level        := return "level"
  | vm_obj_kind.expr         := return "expr"
  | vm_obj_kind.declaration  := return "declaration"
  | vm_obj_kind.environment  := return "environment"
  | vm_obj_kind.tactic_state := return "tactic_state"
  | vm_obj_kind.format       := return "format"
  | vm_obj_kind.options      := return "options"
  | vm_obj_kind.other        := return "[other]"
  end
| (some type) i := do
  fmt ← vm.pp_expr type,
  opts ← vm.get_options,
  return (fmt^.to_string opts)

meta def show_vars_core : nat → nat → nat → vm unit
| c i e :=
  if i = e then return ()
  else do
    (n, type) ← vm.stack_obj_info i,
    type_str  ← type_to_string type i,
    vm.put_str $ "#" ++ c^.to_string ++ " " ++ n^.to_string ++ " : " ++ type_str ++ "\n",
    show_vars_core (c+1) (i+1) e

meta def show_vars (frame : nat) : vm unit :=
do (s, e) ← vm.call_stack_var_range frame,
   show_vars_core 0 s e

meta def show_stack_core : nat → vm unit
| 0     := return ()
| (i+1) := do
  fn ← vm.call_stack_fn i,
  show_fn "" fn i,
  show_stack_core i

meta def show_stack : vm unit :=
do sz ← vm.call_stack_size,
   show_stack_core sz
end debugger
