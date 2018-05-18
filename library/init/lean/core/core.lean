/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.name init.data.rbmap
universes u
/- The compiler uses a core language similar to the one used in Haskell.
   Like Haskell, the core language is based on System Fw. -/
namespace lean
namespace core

def id : Type := name
instance id_has_lt : has_lt id := (name.has_lt_quick : has_lt name)

-- TODO: move to a different module?
inductive literal
| from_nat    : nat → literal
| from_string : string → literal

-- TODO: move to a different module?
-- TODO: decide what we put inside meta_data
inductive meta_data
| from_name : name → meta_data

inductive kind
| star  : kind
| arrow : kind → kind

inductive type
| bvar  : nat → type
| fvar  : id → type
| const : id → type
| arrow : type → type
| all   : id → kind → type
| app   : type → type
| any   : type

inductive alt (expr : Type u)
| cnstr   : id → expr → alt
| default : expr → alt

inductive expr
| bvar    : nat → expr
| fvar    : id → expr
| const   : id → expr
| lit     : literal → expr
| mdata   : meta_data → expr → expr
| lam     : id → type → expr
| app     : expr → expr → expr
| lam_ty  : id → kind → expr
| app_ty  : expr → type → expr
| elet    : id → bool → type → expr → expr
| case    : expr → list (alt expr) → expr
| cast    : type → expr → expr

inductive declaration
| defn        (n : id) (ty : type) (val : expr)
| data        (n : id) (k : kind) (cnstrs : list (id × type))
| cnstr       (n : id) (ty : type) (d : id)
| proj        (n : id) (idx : nat) (ty : type) (d : id)
| external    (n : id) (ty : type)
| external_ty (n : id) (k : kind)

def environment : Type := name → option declaration

structure context :=
(type_ctx : rbmap id kind (<))
(expr_ctx : rbmap id (type × option expr) (<))

end core
end lean
