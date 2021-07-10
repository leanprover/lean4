/*
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Dany Fabian, Sebastian Ullrich
*/

#include "ir_decode_helpers.h"

namespace lean {
namespace ir {

type to_type(object * obj) {
    if (!is_scalar(obj)) throw exception("unsupported IRType");
    else return static_cast<type>(unbox(obj));
}
type cnstr_get_type(object_ref const & o, unsigned i) { return to_type(cnstr_get(o.raw(), i)); }

bool arg_is_irrelevant(arg const & a) { return is_scalar(a.raw()); }
var_id const & arg_var_id(arg const & a) { lean_assert(!arg_is_irrelevant(a)); return cnstr_get_ref_t<var_id>(a, 0); }

lit_val_kind lit_val_tag(lit_val const & l) { return static_cast<lit_val_kind>(cnstr_tag(l.raw())); }
nat const & lit_val_num(lit_val const & l) { lean_assert(lit_val_tag(l) == lit_val_kind::Num); return cnstr_get_ref_t<nat>(l, 0); }
string_ref const & lit_val_str(lit_val const & l) { lean_assert(lit_val_tag(l) == lit_val_kind::Str); return cnstr_get_ref_t<string_ref>(l, 0); }

name const & ctor_info_name(ctor_info const & c) { return cnstr_get_ref_t<name>(c, 0); }
nat const & ctor_info_tag(ctor_info const & c) { return cnstr_get_ref_t<nat>(c, 1); }
nat const & ctor_info_size(ctor_info const & c) { return cnstr_get_ref_t<nat>(c, 2); }
nat const & ctor_info_usize(ctor_info const & c) { return cnstr_get_ref_t<nat>(c, 3); }
nat const & ctor_info_ssize(ctor_info const & c) { return cnstr_get_ref_t<nat>(c, 4); }

/* Return the only Bool scalar field in an object that has `num_obj_fields` object/usize fields */
static inline bool get_bool_field(object * o, unsigned num_obj_fields) {
    return cnstr_get_uint8(o, sizeof(void*)*num_obj_fields);
}

expr_kind expr_tag(expr const & e) { return static_cast<expr_kind>(cnstr_tag(e.raw())); }
ctor_info const & expr_ctor_info(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Ctor); return cnstr_get_ref_t<ctor_info>(e, 0); }
array_ref<arg> const & expr_ctor_args(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Ctor); return cnstr_get_ref_t<array_ref<arg>>(e, 1); }
nat const & expr_reset_num_objs(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Reset); return cnstr_get_ref_t<nat>(e, 0); }
var_id const & expr_reset_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Reset); return cnstr_get_ref_t<var_id>(e, 1); }
var_id const & expr_reuse_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Reuse); return cnstr_get_ref_t<var_id>(e, 0); }
ctor_info const & expr_reuse_ctor(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Reuse); return cnstr_get_ref_t<ctor_info>(e, 1); }
bool expr_reuse_update_header(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Reuse); return get_bool_field(e.raw(), 3); }
array_ref<arg> const & expr_reuse_args(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Reuse); return cnstr_get_ref_t<array_ref<arg>>(e, 2); }
nat const & expr_proj_idx(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Proj); return cnstr_get_ref_t<nat>(e, 0); }
var_id const & expr_proj_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Proj); return cnstr_get_ref_t<var_id>(e, 1); }
nat const & expr_uproj_idx(expr const & e) { lean_assert(expr_tag(e) == expr_kind::UProj); return cnstr_get_ref_t<nat>(e, 0); }
var_id const & expr_uproj_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::UProj); return cnstr_get_ref_t<var_id>(e, 1); }
nat const & expr_sproj_idx(expr const & e) { lean_assert(expr_tag(e) == expr_kind::SProj); return cnstr_get_ref_t<nat>(e, 0); }
nat const & expr_sproj_offset(expr const & e) { lean_assert(expr_tag(e) == expr_kind::SProj); return cnstr_get_ref_t<nat>(e, 1); }
var_id const & expr_sproj_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::SProj); return cnstr_get_ref_t<var_id>(e, 2); }
fun_id const & expr_fap_fun(expr const & e) { lean_assert(expr_tag(e) == expr_kind::FAp); return cnstr_get_ref_t<fun_id>(e, 0); }
array_ref<arg> const & expr_fap_args(expr const & e) { lean_assert(expr_tag(e) == expr_kind::FAp); return cnstr_get_ref_t<array_ref<arg>>(e, 1); }
fun_id const & expr_pap_fun(expr const & e) { lean_assert(expr_tag(e) == expr_kind::PAp); return cnstr_get_ref_t<name>(e, 0); }
array_ref<arg> const & expr_pap_args(expr const & e) { lean_assert(expr_tag(e) == expr_kind::PAp); return cnstr_get_ref_t<array_ref<arg>>(e, 1); }
var_id const & expr_ap_fun(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Ap); return cnstr_get_ref_t<var_id>(e, 0); }
array_ref<arg> const & expr_ap_args(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Ap); return cnstr_get_ref_t<array_ref<arg>>(e, 1); }
type expr_box_type(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Box); return cnstr_get_type(e, 0); }
var_id const & expr_box_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Box); return cnstr_get_ref_t<var_id>(e, 1); }
var_id const & expr_unbox_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Unbox); return cnstr_get_ref_t<var_id>(e, 0); }
lit_val const & expr_lit_val(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Lit); return cnstr_get_ref_t<lit_val>(e, 0); }
var_id const & expr_is_shared_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::IsShared); return cnstr_get_ref_t<var_id>(e, 0); }
var_id const & expr_is_tagged_ptr_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::IsTaggedPtr); return cnstr_get_ref_t<var_id>(e, 0); }

typedef object_ref param;
var_id const & param_var(param const & p) { return cnstr_get_ref_t<var_id>(p, 0); }
bool param_borrow(param const & p) { return get_bool_field(p.raw(), 2); }
type param_type(param const & p) { return cnstr_get_type(p, 1); }

typedef object_ref alt_core;
alt_core_kind alt_core_tag(alt_core const & a) { return static_cast<alt_core_kind>(cnstr_tag(a.raw())); }
ctor_info const & alt_core_ctor_info(alt_core const & a) { lean_assert(alt_core_tag(a) == alt_core_kind::Ctor); return cnstr_get_ref_t<ctor_info>(a, 0); }
fn_body const & alt_core_ctor_cont(alt_core const & a) { lean_assert(alt_core_tag(a) == alt_core_kind::Ctor); return cnstr_get_ref_t<fn_body>(a, 1); }
fn_body const & alt_core_default_cont(alt_core const & a) { lean_assert(alt_core_tag(a) == alt_core_kind::Default); return cnstr_get_ref_t<fn_body>(a, 0); }

fn_body_kind fn_body_tag(fn_body const & a) { return is_scalar(a.raw()) ? static_cast<fn_body_kind>(unbox(a.raw())) : static_cast<fn_body_kind>(cnstr_tag(a.raw())); }
var_id const & fn_body_vdecl_var(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::VDecl); return cnstr_get_ref_t<var_id>(b, 0); }
type fn_body_vdecl_type(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::VDecl); return cnstr_get_type(b, 1); }
expr const & fn_body_vdecl_expr(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::VDecl); return cnstr_get_ref_t<expr>(b, 2); }
fn_body const & fn_body_vdecl_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::VDecl); return cnstr_get_ref_t<fn_body>(b, 3); }
jp_id const & fn_body_jdecl_id(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::JDecl); return cnstr_get_ref_t<jp_id>(b, 0); }
array_ref<param> const & fn_body_jdecl_params(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::JDecl); return cnstr_get_ref_t<array_ref<param>>(b, 1); }
fn_body const & fn_body_jdecl_body(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::JDecl); return cnstr_get_ref_t<fn_body>(b, 2); }
fn_body const & fn_body_jdecl_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::JDecl); return cnstr_get_ref_t<fn_body>(b, 3); }
var_id const & fn_body_set_var(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Set); return cnstr_get_ref_t<var_id>(b, 0); }
nat const & fn_body_set_idx(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Set); return cnstr_get_ref_t<nat>(b, 1); }
arg const & fn_body_set_arg(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Set); return cnstr_get_ref_t<arg>(b, 2); }
fn_body const & fn_body_set_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Set); return cnstr_get_ref_t<fn_body>(b, 3); }
var_id const & fn_body_set_tag_var(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SetTag); return cnstr_get_ref_t<var_id>(b, 0); }
nat const & fn_body_set_tag_cidx(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SetTag); return cnstr_get_ref_t<nat>(b, 1); }
fn_body const & fn_body_set_tag_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SetTag); return cnstr_get_ref_t<fn_body>(b, 2); }
var_id const & fn_body_uset_target(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::USet); return cnstr_get_ref_t<var_id>(b, 0); }
nat const & fn_body_uset_idx(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::USet); return cnstr_get_ref_t<nat>(b, 1); }
var_id const & fn_body_uset_source(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::USet); return cnstr_get_ref_t<var_id>(b, 2); }
fn_body const & fn_body_uset_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::USet); return cnstr_get_ref_t<fn_body>(b, 3); }
var_id const & fn_body_sset_target(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SSet); return cnstr_get_ref_t<var_id>(b, 0); }
nat const & fn_body_sset_idx(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SSet); return cnstr_get_ref_t<nat>(b, 1); }
nat const & fn_body_sset_offset(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SSet); return cnstr_get_ref_t<nat>(b, 2); }
var_id const & fn_body_sset_source(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SSet); return cnstr_get_ref_t<var_id>(b, 3); }
type fn_body_sset_type(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SSet); return cnstr_get_type(b, 4); }
fn_body const & fn_body_sset_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SSet); return cnstr_get_ref_t<fn_body>(b, 5); }
var_id const & fn_body_inc_var(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Inc); return cnstr_get_ref_t<var_id>(b, 0); }
nat const & fn_body_inc_val(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Inc); return cnstr_get_ref_t<nat>(b, 1); }
bool fn_body_inc_maybe_scalar(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Inc); return get_bool_field(b.raw(), 3); }
fn_body const & fn_body_inc_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Inc); return cnstr_get_ref_t<fn_body>(b, 2); }
var_id const & fn_body_dec_var(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Dec); return cnstr_get_ref_t<var_id>(b, 0); }
nat const & fn_body_dec_val(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Dec); return cnstr_get_ref_t<nat>(b, 1); }
bool fn_body_dec_maybe_scalar(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Dec); return get_bool_field(b.raw(), 3); }
fn_body const & fn_body_dec_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Dec); return cnstr_get_ref_t<fn_body>(b, 2); }
var_id const & fn_body_del_var(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Del); return cnstr_get_ref_t<var_id>(b, 0); }
fn_body const & fn_body_del_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Del); return cnstr_get_ref_t<fn_body>(b, 1); }
object_ref const & fn_body_mdata_data(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::MData); return cnstr_get_ref_t<object_ref>(b, 0); }
fn_body const & fn_body_mdata_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::MData); return cnstr_get_ref_t<fn_body>(b, 1); }
name const & fn_body_case_tid(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Case); return cnstr_get_ref_t<name>(b, 0); }
var_id const & fn_body_case_var(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Case); return cnstr_get_ref_t<var_id>(b, 1); }
type fn_body_case_var_type(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Case); return cnstr_get_type(b, 2); }
array_ref<alt_core> const & fn_body_case_alts(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Case); return cnstr_get_ref_t<array_ref<alt_core>>(b, 3); }
arg const & fn_body_ret_arg(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Ret); return cnstr_get_ref_t<arg>(b, 0); }
jp_id const & fn_body_jmp_jp(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Jmp); return cnstr_get_ref_t<jp_id>(b, 0); }
array_ref<arg> const & fn_body_jmp_args(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Jmp); return cnstr_get_ref_t<array_ref<arg>>(b, 1); }

typedef object_ref decl;
decl_kind decl_tag(decl const & a) { return is_scalar(a.raw()) ? static_cast<decl_kind>(unbox(a.raw())) : static_cast<decl_kind>(cnstr_tag(a.raw())); }
fun_id const & decl_fun_id(decl const & b) { return cnstr_get_ref_t<fun_id>(b, 0); }
array_ref<param> const & decl_params(decl const & b) { return cnstr_get_ref_t<array_ref<param>>(b, 1); }
type decl_type(decl const & b) { return cnstr_get_type(b, 2); }
fn_body const & decl_fun_body(decl const & b) { lean_assert(decl_tag(b) == decl_kind::Fun); return cnstr_get_ref_t<fn_body>(b, 3); }

} // namespace ir
}
