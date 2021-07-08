/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Dany Fabian, Sebastian Ullrich
*/

#pragma once
#include "library/compiler/ir.h"
#include "util/array_ref.h"

namespace lean {
namespace ir {
// C++ wrappers of Lean data types

typedef object_ref lit_val;
typedef object_ref ctor_info;

type to_type(object *obj);
type cnstr_get_type(object_ref const &o, unsigned i);

bool arg_is_irrelevant(arg const &a);
var_id const &arg_var_id(arg const &a);

enum class lit_val_kind { Num, Str };
lit_val_kind lit_val_tag(lit_val const &l);
nat const &lit_val_num(lit_val const &l);
string_ref const &lit_val_str(lit_val const &l);

name const &ctor_info_name(ctor_info const &c);
nat const &ctor_info_tag(ctor_info const &c);
nat const &ctor_info_size(ctor_info const &c);
nat const &ctor_info_usize(ctor_info const &c);
nat const &ctor_info_ssize(ctor_info const &c);

/* Return the only Bool scalar field in an object that has `num_obj_fields` object/usize fields */
static inline bool get_bool_field(object *o, unsigned num_obj_fields);

enum class expr_kind { Ctor, Reset, Reuse, Proj, UProj, SProj, FAp, PAp, Ap, Box, Unbox, Lit, IsShared, IsTaggedPtr };
expr_kind expr_tag(expr const &e);
ctor_info const &expr_ctor_info(expr const &e);
array_ref<arg> const &expr_ctor_args(expr const &e);
nat const &expr_reset_num_objs(expr const &e);
var_id const &expr_reset_obj(expr const &e);
var_id const &expr_reuse_obj(expr const &e);
ctor_info const &expr_reuse_ctor(expr const &e);
bool expr_reuse_update_header(expr const &e);
array_ref<arg> const &expr_reuse_args(expr const &e);
nat const &expr_proj_idx(expr const &e);
var_id const &expr_proj_obj(expr const &e);
nat const &expr_uproj_idx(expr const &e);
var_id const &expr_uproj_obj(expr const &e);
nat const &expr_sproj_idx(expr const &e);
nat const &expr_sproj_offset(expr const &e);
var_id const &expr_sproj_obj(expr const &e);
fun_id const &expr_fap_fun(expr const &e);
array_ref<arg> const &expr_fap_args(expr const &e);
fun_id const &expr_pap_fun(expr const &e);
array_ref<arg> const &expr_pap_args(expr const &e);
var_id const &expr_ap_fun(expr const &e);
array_ref<arg> const &expr_ap_args(expr const &e);
type expr_box_type(expr const &e);
var_id const &expr_box_obj(expr const &e);
var_id const &expr_unbox_obj(expr const &e);
lit_val const &expr_lit_val(expr const &e);
var_id const &expr_is_shared_obj(expr const &e);
var_id const &expr_is_tagged_ptr_obj(expr const &e);

typedef object_ref param;
var_id const &param_var(param const &p);
bool param_borrow(param const &p);
type param_type(param const &p);

typedef object_ref alt_core;
enum class alt_core_kind { Ctor, Default };
alt_core_kind alt_core_tag(alt_core const &a);
ctor_info const &alt_core_ctor_info(alt_core const &a);
fn_body const &alt_core_ctor_cont(alt_core const &a);
fn_body const &alt_core_default_cont(alt_core const &a);

enum class fn_body_kind { VDecl, JDecl, Set, SetTag, USet, SSet, Inc, Dec, Del, MData, Case, Ret, Jmp, Unreachable };
fn_body_kind fn_body_tag(fn_body const &a);
var_id const &fn_body_vdecl_var(fn_body const &b);
type fn_body_vdecl_type(fn_body const &b);
expr const &fn_body_vdecl_expr(fn_body const &b);
fn_body const &fn_body_vdecl_cont(fn_body const &b);
jp_id const &fn_body_jdecl_id(fn_body const &b);
array_ref<param> const &fn_body_jdecl_params(fn_body const &b);
fn_body const &fn_body_jdecl_body(fn_body const &b);
fn_body const &fn_body_jdecl_cont(fn_body const &b);
var_id const &fn_body_set_var(fn_body const &b);
nat const &fn_body_set_idx(fn_body const &b);
arg const &fn_body_set_arg(fn_body const &b);
fn_body const &fn_body_set_cont(fn_body const &b);
var_id const &fn_body_set_tag_var(fn_body const &b);
nat const &fn_body_set_tag_cidx(fn_body const &b);
fn_body const &fn_body_set_tag_cont(fn_body const &b);
var_id const &fn_body_uset_target(fn_body const &b);
nat const &fn_body_uset_idx(fn_body const &b);
var_id const &fn_body_uset_source(fn_body const &b);
fn_body const &fn_body_uset_cont(fn_body const &b);
var_id const &fn_body_sset_target(fn_body const &b);
nat const &fn_body_sset_idx(fn_body const &b);
nat const &fn_body_sset_offset(fn_body const &b);
var_id const &fn_body_sset_source(fn_body const &b);
type fn_body_sset_type(fn_body const &b);
fn_body const &fn_body_sset_cont(fn_body const &b);
var_id const &fn_body_inc_var(fn_body const &b);
nat const &fn_body_inc_val(fn_body const &b);
bool fn_body_inc_maybe_scalar(fn_body const &b);
fn_body const &fn_body_inc_cont(fn_body const &b);
var_id const &fn_body_dec_var(fn_body const &b);
nat const &fn_body_dec_val(fn_body const &b);
bool fn_body_dec_maybe_scalar(fn_body const &b);
fn_body const &fn_body_dec_cont(fn_body const &b);
var_id const &fn_body_del_var(fn_body const &b);
fn_body const &fn_body_del_cont(fn_body const &b);
object_ref const &fn_body_mdata_data(fn_body const &b);
fn_body const &fn_body_mdata_cont(fn_body const &b);
name const &fn_body_case_tid(fn_body const &b);
var_id const &fn_body_case_var(fn_body const &b);
type fn_body_case_var_type(fn_body const &b);
array_ref<alt_core> const &fn_body_case_alts(fn_body const &b);
arg const &fn_body_ret_arg(fn_body const &b);
jp_id const &fn_body_jmp_jp(fn_body const &b);
array_ref<arg> const &fn_body_jmp_args(fn_body const &b);

typedef object_ref decl;
enum class decl_kind { Fun, Extern };
decl_kind decl_tag(decl const &a);
fun_id const &decl_fun_id(decl const &b);
array_ref<param> const &decl_params(decl const &b);
type decl_type(decl const &b);
fn_body const &decl_fun_body(decl const &b);
}
}