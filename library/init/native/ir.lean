/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude
import init.meta.name

namespace ir

inductive tag_ty
| mk

inductive ty
| object : ty
| ref : ty → ty
| mut_ref : ty → ty
| tag : tag_ty → ty → ty
-- these are temporary
| int : ty
| object_buffer : ty
| name : name → ty

inductive literal
| nat : nat → literal

-- inductive value : Type
-- | name : name → value
-- | lit : literal → value

-- TODO: eventually model ty.object, mk_object, project, etc in the IR itself
mutual inductive expr, stmt
with expr : Type
| call : name → list name → expr
| global : name → expr
| lit : literal → expr
| mk_object : nat → list name → expr
| locl : name → expr
| block : stmt → expr
| project : name → nat → expr
| panic : string → expr
| mk_native_closure : name → list name → expr
| invoke : name → list name → expr
| assign : name → expr → expr
| uninitialized : expr
| constructor : name → list name → expr
| address_of : name → expr
-- hack for now, do in secon pass clean up
| equals : expr → expr → expr
| sub : expr → expr → expr
| raw_int : nat → expr
-- | value : value → expr
with stmt : Type
| ite : name → stmt → stmt → stmt
| switch : name → list (nat × stmt) → stmt → stmt
| letb : name → ty → expr → stmt → stmt
| e : expr → stmt
-- use a list here
| seq : list stmt → stmt
| return : expr → stmt
| nop : stmt

inductive defn
| mk : name → list (name × ty) → ty → stmt → defn

inductive decl
| mk : name → list (name × ty) → ty → decl

inductive item
| defn : defn → item
| decl : decl → item

end ir

-- def map (K V : Type) : Type :=
--   list (K × V)

-- def lookup {K V} (key : K) (map : map K V) : option V :=
--   sorry

-- def context :=
--   map name ir_decl

-- inductive value
-- | int : nat → value

-- def local_context :=
--   map name ir_expr

-- def call_fn (ctxt : context) (local_cx : local_context) (fn_name : name) (args : list name) : option ir_expr :=
--   sorry

-- -- We fix the global context during evaluation.
-- inductive step_expr (ctxt : context) : local_context → ir_expr → value → Prop
-- | call :
--   forall n args local_cx retval,
--    call_fn ctxt local_cx n args = option.some retval →
--    step_expr local_cx (ir_expr.call n args) retval
-- | local_name :
--   forall n e local_cx retval,
--     lookup n local_cx = option.some e →
--     step_expr local_cx n e

-- inductive step_stmt : context → local_context → ir_stmt → ir_stmt → Prop
-- | nop : forall ctxt local_ctxt,
--   step_stmt ctxt local_ctxt nop nop
-- |
