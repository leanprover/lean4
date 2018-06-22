/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.level init.lean.kvmap

namespace lean

inductive literal
| str_val (val : string)
| nat_val (val : nat)

inductive binder_info
| default | implicit | strict_implicit | inst_implicit | aux_decl

inductive expr
| bvar  : nat → expr                                -- bound variables
| fvar  : name → expr                               -- free variables
| sort  : level → expr                              -- Sort
| const : name → list level → expr                  -- constants
| mvar  : name → expr → expr                        -- (temporary) meta variables
| app   : expr → expr → expr                        -- application
| lam   : name → binder_info → expr → expr → expr   -- lambda abstraction
| pi    : name → binder_info → expr → expr → expr   -- Pi
| elet  : name → expr → expr → expr → expr          -- let expressions
| lit   : literal → expr                            -- literals
| mdata : kvmap → expr → expr                       -- metadata
| proj  : nat → expr → expr                         -- projection
-- TODO: quote constructor will be deleted.
| quote : bool → expr → expr

instance expr_is_inhabited : inhabited expr :=
⟨expr.sort level.zero⟩

end lean
