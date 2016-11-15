/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.option

meta constant vm_obj : Type

inductive vm_obj_kind
| vm_simple
| vm_constructor
| vm_closure
| vm_mpz
| vm_name
| vm_level
| vm_expr
| vm_tactic_state
| vm_format
| vm_other

namespace vm_obj
meta constant kind            : vm_obj → vm_obj_kind
meta constant cidx            : vm_obj → nat
meta constant fn_idx          : vm_obj → nat
meta constant fields          : vm_obj → list vm_obj
meta constant to_nat          : vm_obj → nat
meta constant to_name         : vm_obj → name
meta constant to_level        : vm_obj → level
meta constant to_expr         : vm_obj → expr
meta constant to_tactic_state : vm_obj → tactic_state
meta constant to_format       : vm_obj → format
end vm_obj

meta constant vm_decl : Type

inductive vm_decl_kind
| bytecode | builtin | cfun

structure vm_local_info :=
(id : name) (pos : option (nat × nat))

namespace vm_decl
meta constant kind      : vm_decl → vm_decl_kind
meta constant to_name   : vm_decl → name
meta constant idx       : vm_decl → nat
meta constant arity     : vm_decl → nat
meta constant pos       : vm_decl → option (nat × nat)
meta constant olean     : vm_decl → option name
meta constant args_info : vm_decl → list vm_local_info
end vm_decl

meta constant vm_core : Type → Type
meta constant vm_core.map {A B : Type} : (A → B) → vm_core A → vm_core B
meta constant vm_core.ret {A : Type} : A → vm_core A
meta constant vm_core.bind {A B : Type} : vm_core A → (A → vm_core B) → vm_core B

meta instance : monad vm_core :=
⟨@vm_core.map, @vm_core.ret, @vm_core.bind⟩

@[reducible] meta def vm (A : Type) : Type := optionT.{1 1} vm_core A

namespace vm
meta constant get_decl        : name → vm vm_decl
meta constant stack_size      : vm nat
meta constant stack_obj       : nat → vm vm_obj
meta constant stack_obj_info  : nat → vm (name × option expr)
meta constant call_stack_size : vm nat
meta constant call_stack_fn   : nat → vm name
meta constant curr_fn         : vm name
meta constant bp              : vm nat
meta constant pc              : vm nat

meta def trace {A : Type} [has_to_format A] (a : A) : vm unit :=
do fmt ← return $ to_fmt a,
   return $ _root_.trace_fmt fmt (λ u, ())

end vm

meta structure vm_monitor (s : Type) :=
(init : s) (step : s → vm s)

/- Registers a new virtual machine monitor. The argument must be the name of a definition of type
   `vm_monitor S`. The command will override the last monitor. -/
meta constant vm_monitor.register : name → command
