/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.level init.lean.kvmap

namespace lean

inductive literal
| nat_val (val : nat)
| str_val (val : string)

inductive binder_info
| default | implicit | strict_implicit | inst_implicit | aux_decl

/-
TODO(Leo): fix the `mvar` constructor.
In Lean3 (and Lean4), we have two kinds of metavariables: regular and temporary.
The type of regular metavariables is stored in the metavar_context.
The type of temporary metavariables is stored in the metavar itself. This decision is legacy from Lean2.
Moreover, the `name` in temporary metavariables are supposed to be (small) numerals. So,
we can store their assignment as an array. Actually, it is a numeral with a hidden unique prefix.
The decision of storing the type of the tmp metavar is also debatable.
For example, we can avoid this by have another array with their types.
For regular metavariables, the `expr` field is a dummy value.

We should have two different constructors:
`| mvar : name → expr` for regular metavariables
and
`| tmvar : usize → expr` for temporary metavariables
The `usize` makes it clear that we can use arrays to store tmp metavar assignments and their types.
-/
inductive expr
| bvar  : nat → expr                                -- bound variables
| fvar  : name → expr                               -- free variables
| mvar  : name → expr → expr                        -- (temporary) meta variables
| sort  : level → expr                              -- Sort
| const : name → list level → expr                  -- constants
| app   : expr → expr → expr                        -- application
| lam   : name → binder_info → expr → expr → expr   -- lambda abstraction
| pi    : name → binder_info → expr → expr → expr   -- Pi
| elet  : name → expr → expr → expr → expr          -- let expressions
| lit   : literal → expr                            -- literals
| mdata : kvmap → expr → expr                       -- metadata
| proj  : name → nat → expr → expr                  -- projection

instance expr_is_inhabited : inhabited expr :=
⟨expr.sort level.zero⟩

namespace expr
def mk_app (fn : expr) (args : list expr) : expr :=
args.foldl expr.app fn

def mk_capp (fn : name) (args : list expr) : expr :=
mk_app (expr.const fn []) args
end expr
end lean
