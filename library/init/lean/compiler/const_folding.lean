/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.expr init.platform
import init.lean.compiler.util

/- Constant folding for primitives that have special runtime support. -/

namespace lean
namespace compiler

def bin_fold_fn := bool → expr → expr → option expr

def mk_uint_type_name (nbytes : nat) : name :=
mk_simple_name ("uint" ++ to_string nbytes)

structure num_scalar_type_info :=
(nbits : nat)
(id : name        := mk_uint_type_name nbits)
(of_nat_fn : name := name.mk_string id "of_nat")
(size : nat       := 2^nbits)

def num_scalar_types : list num_scalar_type_info :=
[{nbits := 8}, {nbits := 16}, {nbits := 32}, {nbits := 64},
 {id := `usize, nbits := system.platform.nbits}]

def is_of_nat (fn : name) : bool :=
num_scalar_types.any (λ info, info.of_nat_fn = fn)

def get_info_from_fn (fn : name) : list num_scalar_type_info → option num_scalar_type_info
| []            := none
| (info::infos) :=
  if info.of_nat_fn = fn then some info
  else get_info_from_fn infos

def get_info_from_val : expr → option num_scalar_type_info
| (expr.app (expr.const fn _) _) := get_info_from_fn fn num_scalar_types
| _ := none

@[export lean.get_num_lit_core]
def get_num_lit : expr → option nat
| (expr.lit (literal.nat_val n)) := some n
| (expr.app (expr.const fn _) a) := if is_of_nat fn then get_num_lit a else none
| _                              := none

def mk_uint_lit (info : num_scalar_type_info) (n : nat) : expr :=
expr.app (expr.const info.of_nat_fn []) (expr.lit (literal.nat_val (n%info.size)))

def fold_bin_uint (fn : num_scalar_type_info → bool → nat → nat → nat) (before_erasure : bool) (a₁ a₂ : expr) : option expr :=
do n₁   ← get_num_lit a₁,
   n₂   ← get_num_lit a₂,
   info ← get_info_from_val a₁,
   pure $ mk_uint_lit info (fn info before_erasure n₁ n₂)

def fold_uint_add := fold_bin_uint $ λ _ _, (+)
def fold_uint_mul := fold_bin_uint $ λ _ _, (*)
def fold_uint_div := fold_bin_uint $ λ _ _, (/)
def fold_uint_mod := fold_bin_uint $ λ _ _, (%)
def fold_uint_sub := fold_bin_uint $ λ info _ a b, (a + (info.size - b))

def pre_uint_bin_fold_fns : list (name × bin_fold_fn) :=
[(`add, fold_uint_add), (`mul, fold_uint_mul), (`div, fold_uint_div),
 (`mod, fold_uint_mod), (`sub, fold_uint_sub)]

def uint_bin_fold_fns : list (name × bin_fold_fn) :=
num_scalar_types.foldl (λ r info, r ++ (pre_uint_bin_fold_fns.map (λ ⟨suffix, fn⟩, (info.id ++ suffix, fn)))) []

def fold_nat_bin_op (fn : nat → nat → nat) (a₁ a₂ : expr) : option expr :=
do n₁   ← get_num_lit a₁,
   n₂   ← get_num_lit a₂,
   pure $ expr.lit (literal.nat_val (fn n₁ n₂))

def fold_nat_add (_ : bool) := fold_nat_bin_op (+)
def fold_nat_mul (_ : bool) := fold_nat_bin_op (*)
def fold_nat_div (_ : bool) := fold_nat_bin_op (/)
def fold_nat_mod (_ : bool) := fold_nat_bin_op (%)

def mk_nat_eq (a b : expr) : expr :=
mk_bin_app (expr.app (expr.const `eq [level.one]) (expr.const `nat [])) a b

def mk_nat_lt (a b : expr) : expr :=
mk_bin_app (mk_bin_app (expr.const `has_lt.lt [level.zero]) (expr.const `nat []) (expr.const `nat.has_lt [])) a b

def mk_nat_le (a b : expr) : expr :=
mk_bin_app (mk_bin_app (expr.const `has_lt.le [level.zero]) (expr.const `nat []) (expr.const `nat.has_le [])) a b

def to_decidable_expr (before_erasure : bool) (pred : expr) (r : bool) : expr :=
match before_erasure, r with
| ff, tt := mk_dec_is_true  neutral_expr neutral_expr
| ff, ff := mk_dec_is_false neutral_expr neutral_expr
| tt, tt := mk_dec_is_true pred (mk_lc_proof pred)
| tt, ff := mk_dec_is_false pred (mk_lc_proof pred)

def fold_nat_bin_pred (mk_pred : expr → expr → expr) (fn : nat → nat → bool)
                      (before_erasure : bool) (a₁ a₂ : expr) : option expr :=
do n₁   ← get_num_lit a₁,
   n₂   ← get_num_lit a₂,
   pure $ to_decidable_expr before_erasure (mk_pred a₁ a₂) (fn n₁ n₂)

def fold_nat_dec_eq := fold_nat_bin_pred mk_nat_eq (λ a b, a = b)
def fold_nat_dec_lt := fold_nat_bin_pred mk_nat_lt (λ a b, a < b)
def fold_nat_dec_le := fold_nat_bin_pred mk_nat_le (λ a b, a ≤ b)

def nat_fold_fns : list (name × bin_fold_fn) :=
[(`nat.add, fold_nat_add),
 (`nat.mul, fold_nat_mul),
 (`nat.div, fold_nat_div),
 (`nat.mod, fold_nat_mod),
 (`nat.dec_eq, fold_nat_dec_eq),
 (`nat.dec_lt, fold_nat_dec_lt),
 (`nat.dec_le, fold_nat_dec_le)]

def bin_fold_fns : list (name × bin_fold_fn) :=
uint_bin_fold_fns ++ nat_fold_fns

def find_bin_fold_fn_aux (fn : name) : list (name × bin_fold_fn) → option bin_fold_fn
| []             := none
| ((n, f)::rest) :=
  if fn = n then some f else find_bin_fold_fn_aux rest

def find_bin_fold_fn (fn : name) : option bin_fold_fn :=
find_bin_fold_fn_aux fn bin_fold_fns

@[export lean.fold_bin_op_core]
def fold_bin_op (before_erasure : bool) (f : expr) (a : expr) (b : expr) : option expr :=
match f with
| expr.const fn _ := do
   fold_fn ← find_bin_fold_fn fn,
   fold_fn before_erasure a b
| _ := none

end compiler
end lean
