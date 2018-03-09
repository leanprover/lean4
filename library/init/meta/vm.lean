/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.category.option
import init.meta.mk_dec_eq_instance

meta constant vm_obj : Type

@[derive decidable_eq]
inductive vm_obj_kind
| simple | constructor | closure | native_closure | mpz
| name | level | expr | declaration
| environment | tactic_state | format
| options | other

namespace vm_obj
meta constant kind            : vm_obj → vm_obj_kind
/-- For simple and constructor vm_obj's, it returns the constructor tag/index.
   Return 0 otherwise. -/
meta constant cidx            : vm_obj → nat
/-- For closure vm_obj's, it returns the internal function index. -/
meta constant fn_idx          : vm_obj → nat
/-- For constructor vm_obj's, it returns the data stored in the object.
   For closure vm_obj's, it returns the local arguments captured by the closure. -/
meta constant fields          : vm_obj → list vm_obj
/-- For simple and mpz vm_obj's -/
meta constant to_nat          : vm_obj → nat
/-- For name vm_obj's, it returns the name wrapped by the vm_obj. -/
meta constant to_name         : vm_obj → name
/-- For level vm_obj's, it returns the universe level wrapped by the vm_obj. -/
meta constant to_level        : vm_obj → level
/-- For expr vm_obj's, it returns the expression wrapped by the vm_obj. -/
meta constant to_expr         : vm_obj → expr
/-- For declaration vm_obj's, it returns the declaration wrapped by the vm_obj. -/
meta constant to_declaration  : vm_obj → declaration
/-- For environment vm_obj's, it returns the environment wrapped by the vm_obj. -/
meta constant to_environment  : vm_obj → environment
/-- For tactic_state vm_obj's, it returns the tactic_state object wrapped by the vm_obj. -/
meta constant to_tactic_state : vm_obj → tactic_state
/-- For format vm_obj's, it returns the format object wrapped by the vm_obj. -/
meta constant to_format       : vm_obj → format
end vm_obj

meta constant vm_decl : Type

inductive vm_decl_kind
| bytecode | builtin | cfun

/-- Information for local variables and arguments on the VM stack.
   Remark: type is only available if it is a closed term at compilation time. -/
meta structure vm_local_info :=
(id : name) (type : option expr)

namespace vm_decl
meta constant kind      : vm_decl → vm_decl_kind
meta constant to_name   : vm_decl → name
/-- Internal function index associated with the given VM declaration. -/
meta constant idx       : vm_decl → nat
/-- Number of arguments needed to execute the given VM declaration. -/
meta constant arity     : vm_decl → nat
/-- Return source position if available -/
meta constant pos       : vm_decl → option pos
/-- Return .olean file where the given VM declaration was imported from. -/
meta constant olean     : vm_decl → option string
/-- Return names .olean file where the given VM declaration was imported from. -/
meta constant args_info : vm_decl → list vm_local_info
end vm_decl

meta constant vm_core : Type → Type
meta constant vm_core.map {α β : Type} : (α → β) → vm_core α → vm_core β
meta constant vm_core.ret {α : Type} : α → vm_core α
meta constant vm_core.bind {α β : Type} : vm_core α → (α → vm_core β) → vm_core β

meta instance : monad vm_core :=
{ map := @vm_core.map, pure := @vm_core.ret, bind := @vm_core.bind }

@[reducible] meta def vm (α : Type) : Type := option_t vm_core α

namespace vm
meta constant get_env              : vm environment
meta constant get_decl             : name → vm vm_decl
meta constant get_options          : vm options
meta constant stack_size           : vm nat
/-- Return the vm_obj stored at the given position on the execution stack.
   It fails if position >= vm.stack_size -/
meta constant stack_obj            : nat → vm vm_obj
/-- Return (name, type) for the object at the given position on the execution stack.
   It fails if position >= vm.stack_size.
   The name is anonymous if vm_obj is a transient value created by the compiler.
   Type information is only recorded if the type is a closed term at compilation time. -/
meta constant stack_obj_info       : nat → vm (name × option expr)
/-- Pretty print the vm_obj at the given position on the execution stack. -/
meta constant pp_stack_obj         : nat → vm format
/-- Pretty print the given expression. -/
meta constant pp_expr              : expr → vm format
/-- Number of frames on the call stack. -/
meta constant call_stack_size      : vm nat
/-- Return the function name at the given stack frame.
   Action fails if position >= vm.call_stack_size. -/
meta constant call_stack_fn        : nat → vm name
/-- Return the range [start, end) for the given stack frame.
   Action fails if position >= vm.call_stack_size.
   The values start and end correspond to positions at the execution stack.
   We have that 0 <= start < end <= vm.stack_size -/
meta constant call_stack_var_range : nat → vm (nat × nat)
/-- Return the name of the function on top of the call stack. -/
meta constant curr_fn              : vm name
/-- Return the base stack pointer for the frame on top of the call stack. -/
meta constant bp                   : vm nat
/-- Return the program counter. -/
meta constant pc                   : vm nat
/-- Convert the given vm_obj into a string -/
meta constant obj_to_string        : vm_obj → vm string
meta constant put_str              : string → vm unit
meta constant get_line             : vm string
/-- Return tt if end of the input stream has been reached.
   For example, this can happen if the user presses Ctrl-D -/
meta constant eof                  : vm bool
/-- Return the list of declarations tagged with the given attribute. -/
meta constant get_attribute        : name → vm (list name)

meta def trace {α : Type} [has_to_format α] (a : α) : vm unit :=
do fmt ← return $ to_fmt a,
   return $ _root_.trace_fmt fmt (λ u, ())

end vm

/-- A Lean VM monitor. Monitors are registered using the [vm_monitor] attribute.

    If option 'debugger' is true, then the VM will initialize the vm_monitor state using the
    'init' field, and will invoke the function 'step' before each instruction is invoked. -/
meta structure vm_monitor (α : Type) :=
(init : α) (step : α → vm α)
