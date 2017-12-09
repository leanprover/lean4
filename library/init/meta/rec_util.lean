/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper tactic for showing that a type has decidable equality.
-/
prelude
import init.meta.tactic init.data.option.basic

namespace tactic
open expr

/-- Return tt iff e's type is of the form `(I_name ...)` -/
meta def is_type_app_of (e : expr) (I_name : name) : tactic bool :=
do t ← infer_type e,
   return $ is_constant_of (get_app_fn t) I_name

/- Auxiliary function for using brec_on "dictionary" -/
private meta def mk_rec_inst_aux : expr → nat → tactic expr
| F 0     := do
  P ← mk_app `pprod.fst [F],
  mk_app `pprod.fst [P]
| F (n+1) := do
  F' ← mk_app `pprod.snd [F],
  mk_rec_inst_aux F' n

/-- Construct brec_on "recursive value". F_name is the name of the brec_on "dictionary".
   Type of the F_name hypothesis should be of the form (below (C ...)) where C is a constructor.
   The result is the "recursive value" for the (i+1)-th recursive value of the constructor C. -/
meta def mk_brec_on_rec_value (F_name : name) (i : nat) : tactic expr :=
do F ← get_local F_name,
   mk_rec_inst_aux F i

meta def constructor_num_fields (c : name) : tactic nat :=
do env     ← get_env,
   decl    ← env.get c,
   ctype   ← return decl.type,
   arity   ← get_pi_arity ctype,
   I       ← env.inductive_type_of c,
   nparams ← return (env.inductive_num_params I),
   return $ arity - nparams

private meta def mk_name_list_aux : name → nat → nat → list name → list name × nat
| p i 0     l := (list.reverse l, i)
| p i (j+1) l := mk_name_list_aux p (i+1) j (mk_num_name p i :: l)

private meta def mk_name_list (p : name) (i : nat) (n : nat) : list name × nat :=
mk_name_list_aux p i n []

/-- Return a list of names of the form [p.i, ..., p.{i+n}] where n is
   the number of fields of the constructor c -/
meta def mk_constructor_arg_names (c : name) (p : name) (i : nat) : tactic (list name × nat) :=
do nfields ← constructor_num_fields c,
   return $ mk_name_list p i nfields

private meta def mk_constructors_arg_names_aux : list name → name → nat → list (list name) → tactic (list (list name))
| []      p i r := return (list.reverse r)
| (c::cs) p i r := do
  v : list name × nat ← mk_constructor_arg_names c p i,
  match v with (l, i') := mk_constructors_arg_names_aux cs p i' (l :: r) end

/-- Given an inductive datatype I with k constructors and where constructor i has n_i fields,
   return the list [[p.1, ..., p.n_1], [p.{n_1 + 1}, ..., p.{n_1 + n_2}], ..., [..., p.{n_1 + ... + n_k}]] -/
meta def mk_constructors_arg_names (I : name) (p : name) : tactic (list (list name)) :=
do env ← get_env,
   cs  ← return $ env.constructors_of I,
   mk_constructors_arg_names_aux cs p 1 []

private meta def mk_fresh_arg_name_aux : name → nat → name_set → tactic (name × name_set)
| n i s :=
  do r ← get_unused_name n (some i),
     if s.contains r then
        mk_fresh_arg_name_aux n (i+1) s
     else
        return (r, s.insert r)

private meta def mk_fresh_arg_name (n : name) (s : name_set) : tactic (name × name_set) :=
do r ← get_unused_name n,
   if s.contains r then
      mk_fresh_arg_name_aux n 1 s
   else
      return (r, s.insert r)

private meta def mk_constructor_fresh_names_aux : nat → expr → name_set → tactic (list name × name_set)
| nparams ty s := do
  ty ← whnf ty,
  match ty with
  | expr.pi n bi d b :=
     if nparams = 0 then do {
       (n', s') ← mk_fresh_arg_name n s,
       x        ← mk_local' n' bi d,
       let ty' := b.instantiate_var x,
       (ns, s'') ← mk_constructor_fresh_names_aux 0 ty' s',
       return (n'::ns, s'')
     } else do {
       x        ← mk_local' n bi d,
       let ty' := b.instantiate_var x,
       mk_constructor_fresh_names_aux (nparams - 1) ty' s
     }
  | _ := return ([], s)
  end

meta def mk_constructor_fresh_names (nparams : nat) (c : name) (s : name_set) : tactic (list name × name_set) :=
do d    ← get_decl c,
   let t := d.type,
   mk_constructor_fresh_names_aux nparams t s

private meta def mk_constructors_fresh_names_aux : nat → list name → name_set → list (list name) → tactic (list (list name))
| np []      s r := return (list.reverse r)
| np (c::cs) s r := do
  (ns, s') ← mk_constructor_fresh_names np c s,
  mk_constructors_fresh_names_aux np cs s' (ns::r)

meta def mk_constructors_fresh_names (I : name) : tactic (list (list name)) :=
do env ← get_env,
   let cs := env.constructors_of I,
   let nparams := env.inductive_num_params I,
   mk_constructors_fresh_names_aux nparams cs mk_name_set []

end tactic
