/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include <string>
#include <vector>
#include <dlfcn.h>
#include "runtime/flet.h"
#include "runtime/apply.h"
#include "library/trace.h"
#include "library/compiler/ir.h"
#include "util/option_ref.h"
#include "util/array_ref.h"
#include "util/nat.h"

namespace lean {
namespace ir {
typedef object_ref lit_val;
typedef object_ref ctor_info;

template<class T>
inline T const & cnstr_get_ref_t(object_ref const & o, unsigned i) {
    static_assert(sizeof(T) == sizeof(object_ref), "unexpected object wrapper size");
    return *reinterpret_cast<T const *>(&cnstr_get_ref(o.raw(), i));
}

bool arg_is_irrelevant(arg const & a) { return is_scalar(a.raw()); }
var_id const & arg_var_id(arg const & a) { lean_assert(!arg_is_irrelevant(a)); return cnstr_get_ref_t<var_id>(a, 0); }

enum class lit_val_kind { Num, Str };
lit_val_kind lit_val_tag(lit_val const & l) { return static_cast<lit_val_kind>(cnstr_tag(l.raw())); }
nat const & lit_val_num(lit_val const & l) { lean_assert(lit_val_tag(l) == lit_val_kind::Num); return cnstr_get_ref_t<nat>(l, 0); }
string_ref const & lit_val_str(lit_val const & l) { lean_assert(lit_val_tag(l) == lit_val_kind::Str); return cnstr_get_ref_t<string_ref>(l, 0); }

name const & ctor_info_name(ctor_info const & c) { return cnstr_get_ref_t<name>(c, 0); }
nat const & ctor_info_idx(ctor_info const & c) { return cnstr_get_ref_t<nat>(c, 1); }
nat const & ctor_info_size(ctor_info const & c) { return cnstr_get_ref_t<nat>(c, 2); }
nat const & ctor_info_usize(ctor_info const & c) { return cnstr_get_ref_t<nat>(c, 3); }
nat const & ctor_info_ssize(ctor_info const & c) { return cnstr_get_ref_t<nat>(c, 4); }

enum class expr_kind { Ctor, Reset, Reuse, Proj, UProj, SProj, FAp, PAp, Ap, Box, Unbox, Lit, IsShared, IsTaggedPtr };
expr_kind expr_tag(expr const & e) { return static_cast<expr_kind>(cnstr_tag(e.raw())); }
ctor_info const & expr_ctor_info(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Ctor); return cnstr_get_ref_t<ctor_info>(e, 0); }
array_ref<arg> const & expr_ctor_args(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Ctor); return cnstr_get_ref_t<array_ref<arg>>(e, 1); }
nat const & expr_reset_num_objs(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Reset); return cnstr_get_ref_t<nat>(e, 0); }
var_id const & expr_reset_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Reset); return cnstr_get_ref_t<var_id>(e, 1); }
var_id const & expr_reuse_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Reuse); return cnstr_get_ref_t<var_id>(e, 0); }
ctor_info const & expr_reuse_ctor(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Reuse); return cnstr_get_ref_t<ctor_info>(e, 1); }
bool expr_reuse_update_header(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Reuse); return cnstr_get_uint8(e.raw(), sizeof(void *) * 3); }
array_ref<arg> const & expr_reuse_args(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Reuse); return cnstr_get_ref_t<array_ref<arg>>(e, 2); }
nat const & expr_proj_idx(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Proj); return cnstr_get_ref_t<nat>(e, 0); }
var_id const & expr_proj_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Proj); return cnstr_get_ref_t<var_id>(e, 1); }
nat const & expr_uproj_idx(expr const & e) { lean_assert(expr_tag(e) == expr_kind::UProj); return cnstr_get_ref_t<nat>(e, 0); }
var_id const & expr_uproj_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::UProj); return cnstr_get_ref_t<var_id>(e, 1); }
nat const & expr_sproj_num_objs(expr const & e) { lean_assert(expr_tag(e) == expr_kind::SProj); return cnstr_get_ref_t<nat>(e, 0); }
nat const & expr_sproj_offset(expr const & e) { lean_assert(expr_tag(e) == expr_kind::SProj); return cnstr_get_ref_t<nat>(e, 1); }
var_id const & expr_sproj_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::SProj); return cnstr_get_ref_t<var_id>(e, 2); }
fun_id const & expr_fap_fun(expr const & e) { lean_assert(expr_tag(e) == expr_kind::FAp); return cnstr_get_ref_t<fun_id>(e, 0); }
array_ref<arg> const & expr_fap_args(expr const & e) { lean_assert(expr_tag(e) == expr_kind::FAp); return cnstr_get_ref_t<array_ref<arg>>(e, 1); }
fun_id const & expr_pap_fun(expr const & e) { lean_assert(expr_tag(e) == expr_kind::PAp); return cnstr_get_ref_t<name>(e, 0); }
array_ref<arg> const & expr_pap_args(expr const & e) { lean_assert(expr_tag(e) == expr_kind::PAp); return cnstr_get_ref_t<array_ref<arg>>(e, 1); }
var_id const & expr_ap_fun(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Ap); return cnstr_get_ref_t<var_id>(e, 0); }
array_ref<arg> const & expr_ap_args(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Ap); return cnstr_get_ref_t<array_ref<arg>>(e, 1); }
type expr_box_type(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Box); return static_cast<type>(cnstr_get_uint8(e.raw(), sizeof(void *))); }
var_id const & expr_box_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Box); return cnstr_get_ref_t<var_id>(e, 0); }
var_id const & expr_unbox_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Unbox); return cnstr_get_ref_t<var_id>(e, 0); }
lit_val const & expr_lit_val(expr const & e) { lean_assert(expr_tag(e) == expr_kind::Lit); return cnstr_get_ref_t<lit_val>(e, 0); }
var_id const & expr_is_shared_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::IsShared); return cnstr_get_ref_t<var_id>(e, 0); }
var_id const & expr_is_tagged_ptr_obj(expr const & e) { lean_assert(expr_tag(e) == expr_kind::IsTaggedPtr); return cnstr_get_ref_t<var_id>(e, 0); }

typedef object_ref param;
var_id const & param_var(param const & p) { return cnstr_get_ref_t<var_id>(p, 0); }
bool param_borrow(param const & p) { return cnstr_get_uint8(p.raw(), sizeof(void *)); }

typedef object_ref alt_core;
enum class alt_core_kind { Ctor, Default };
alt_core_kind alt_core_tag(alt_core const & a) { return static_cast<alt_core_kind>(cnstr_tag(a.raw())); }
ctor_info const & alt_core_ctor_info(alt_core const & a) { lean_assert(alt_core_tag(a) == alt_core_kind::Ctor); return cnstr_get_ref_t<ctor_info>(a, 0); }
fn_body const & alt_core_ctor_cont(alt_core const & a) { lean_assert(alt_core_tag(a) == alt_core_kind::Ctor); return cnstr_get_ref_t<fn_body>(a, 1); }
fn_body const & alt_core_default_cont(alt_core const & a) { lean_assert(alt_core_tag(a) == alt_core_kind::Default); return cnstr_get_ref_t<fn_body>(a, 0); }

enum class fn_body_kind { VDecl, JDecl, Set, SetTag, USet, SSet, Inc, Dec, Del, MData, Case, Ret, Jmp, Unreachable };
fn_body_kind fn_body_tag(fn_body const & a) { return is_scalar(a.raw()) ? static_cast<fn_body_kind>(unbox(a.raw())) : static_cast<fn_body_kind>(cnstr_tag(a.raw())); }
var_id const & fn_body_vdecl_var(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::VDecl); return cnstr_get_ref_t<var_id>(b, 0); }
type fn_body_vdecl_type(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::VDecl); return static_cast<type>(cnstr_get_uint8(b.raw(), sizeof(void *) * 3)); }
expr const & fn_body_vdecl_expr(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::VDecl); return cnstr_get_ref_t<expr>(b, 1); }
fn_body const & fn_body_vdecl_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::VDecl); return cnstr_get_ref_t<fn_body>(b, 2); }
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
var_id const & fn_body_uset_var(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::USet); return cnstr_get_ref_t<var_id>(b, 0); }
nat const & fn_body_uset_idx(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::USet); return cnstr_get_ref_t<nat>(b, 1); }
var_id const & fn_body_uset_arg(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::USet); return cnstr_get_ref_t<var_id>(b, 2); }
fn_body const & fn_body_uset_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::USet); return cnstr_get_ref_t<fn_body>(b, 3); }
var_id const & fn_body_sset_target(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SSet); return cnstr_get_ref_t<var_id>(b, 0); }
nat const & fn_body_sset_num_objs(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SSet); return cnstr_get_ref_t<nat>(b, 1); }
nat const & fn_body_sset_offset(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SSet); return cnstr_get_ref_t<nat>(b, 2); }
var_id const & fn_body_sset_source(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SSet); return cnstr_get_ref_t<var_id>(b, 3); }
type fn_body_sset_type(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SSet); return static_cast<type>(cnstr_get_uint8(b.raw(), sizeof(void *) * 5)); }
fn_body const & fn_body_sset_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SSet); return cnstr_get_ref_t<fn_body>(b, 4); }
var_id const & fn_body_inc_var(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Inc); return cnstr_get_ref_t<var_id>(b, 0); }
nat const & fn_body_inc_val(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Inc); return cnstr_get_ref_t<nat>(b, 1); }
bool fn_body_inc_maybe_scalar(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Inc); return static_cast<bool>(cnstr_get_uint8(b.raw(), sizeof(void *) * 3)); }
fn_body const & fn_body_inc_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Inc); return cnstr_get_ref_t<fn_body>(b, 2); }
var_id const & fn_body_dec_var(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Dec); return cnstr_get_ref_t<var_id>(b, 0); }
nat const & fn_body_dec_val(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Dec); return cnstr_get_ref_t<nat>(b, 1); }
bool fn_body_dec_maybe_scalar(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Dec); return static_cast<bool>(cnstr_get_uint8(b.raw(), sizeof(void *) * 3)); }
fn_body const & fn_body_dec_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Dec); return cnstr_get_ref_t<fn_body>(b, 2); }
var_id const & fn_body_del_var(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Del); return cnstr_get_ref_t<var_id>(b, 0); }
fn_body const & fn_body_del_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Del); return cnstr_get_ref_t<fn_body>(b, 1); }
object_ref const & fn_body_mdata_data(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::MData); return cnstr_get_ref_t<object_ref>(b, 0); }
fn_body const & fn_body_mdata_cont(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::MData); return cnstr_get_ref_t<fn_body>(b, 1); }
name const & fn_body_case_tid(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Case); return cnstr_get_ref_t<name>(b, 0); }
var_id const & fn_body_case_var(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Case); return cnstr_get_ref_t<var_id>(b, 1); }
array_ref<alt_core> const & fn_body_case_alts(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Case); return cnstr_get_ref_t<array_ref<alt_core>>(b, 2); }
arg const & fn_body_ret_arg(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Ret); return cnstr_get_ref_t<arg>(b, 0); }
jp_id const & fn_body_jmp_jp(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Jmp); return cnstr_get_ref_t<jp_id>(b, 0); }
array_ref<arg> const & fn_body_jmp_args(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::Jmp); return cnstr_get_ref_t<array_ref<arg>>(b, 1); }

typedef object_ref decl;
enum class decl_kind { Fun, Extern };
decl_kind decl_tag(decl const & a) { return is_scalar(a.raw()) ? static_cast<decl_kind>(unbox(a.raw())) : static_cast<decl_kind>(cnstr_tag(a.raw())); }
fun_id const & decl_fun_id(decl const & b) { return cnstr_get_ref_t<fun_id>(b, 0); }
array_ref<param> const & decl_params(decl const & b) { return cnstr_get_ref_t<array_ref<param>>(b, 1); }
type decl_type(decl const & b) { return static_cast<type>(cnstr_get_uint8(b.raw(), sizeof(void *) * 3)); }
fn_body const & decl_fun_body(decl const & b) { lean_assert(decl_tag(b) == decl_kind::Fun); return cnstr_get_ref_t<fn_body>(b, 2); }

extern "C" object * lean_ir_find_env_decl(object * env, object * n);
option_ref<decl> find_env_decl(environment const & env, name const & n) {
    return option_ref<decl>(lean_ir_find_env_decl(env.to_obj_arg(), n.to_obj_arg()));
}

static string_ref * g_mangle_prefix = nullptr;
static string_ref * g_boxed_mangled_suffix = nullptr;

extern "C" object * lean_name_mangle(object * n, object * pre);
string_ref name_mangle(name const & n, string_ref const & pre) {
    return string_ref(lean_name_mangle(n.to_obj_arg(), pre.to_obj_arg()));
}

extern "C" object * lean_ir_format_fn_body_head(object * b);
format format_fn_body_head(fn_body const & b) {
    return format(lean_ir_format_fn_body_head(b.to_obj_arg()));
}

void print_object(io_state_stream const & ios, object * o) {
    if (is_scalar(o)) {
        ios << unbox(o);
    } else if (o == nullptr) {
        ios << "0x0"; // confusingly printed as "0" by the default operator<<
    } else {
        ios.get_stream() << o;
    }
}

class interpreter {
    std::vector<object *> m_arg_stack;
    std::vector<fn_body const *> m_jp_stack;
    struct frame {
        name m_fn;
        size_t m_arg_bp;
        size_t m_jp_bp;
    };
    std::vector<frame> m_call_stack;
    environment const & m_env;
    name_map<object *> m_constant_cache;

    inline frame & get_frame() {
        return m_call_stack.back();
    }

    inline object * & var(var_id const & v) {
        // variables are 1-indexed
        size_t i = get_frame().m_arg_bp + v.get_small_value() - 1;
        if (i >= m_arg_stack.size()) {
            m_arg_stack.resize(i + 1);
        }
        return m_arg_stack[i];
    }

    object * eval_arg(arg const & a) {
        return arg_is_irrelevant(a) ? box(0) : var(arg_var_id(a));
    }

    object * alloc_ctor(ctor_info const & i, array_ref<arg> const & args) {
        size_t idx = ctor_info_idx(i).get_small_value();
        size_t size = ctor_info_size(i).get_small_value();
        size_t usize = ctor_info_usize(i).get_small_value();
        size_t ssize = ctor_info_ssize(i).get_small_value();
        if (size == 0 && usize == 0 && ssize == 0) {
            return box(idx);
        } else {
            object *o = alloc_cnstr(idx, size, usize * sizeof(void *) + ssize);
            for (size_t i = 0; i < args.size(); i++) {
                cnstr_set(o, i, eval_arg(args[i]));
            }
            return o;
        }
    }

    object * eval_expr(expr const & e, type t) {
        switch (expr_tag(e)) {
            case expr_kind::Ctor:
                return alloc_ctor(expr_ctor_info(e), expr_ctor_args(e));
            case expr_kind::Reset: {
                object * o = var(expr_reset_obj(e));
                if (is_exclusive(o)) {
                    for (size_t i = 0; i < expr_reset_num_objs(e).get_small_value(); i++) {
                        cnstr_release(o, i);
                    }
                    return o;
                } else {
                    dec_ref(o);
                    return box(0);
                }
            }
            case expr_kind::Reuse: {
                object * o = var(expr_reuse_obj(e));
                if (is_scalar(o)) {
                    return alloc_ctor(expr_reuse_ctor(e), expr_reuse_args(e));
                } else {
                    if (expr_reuse_update_header(e)) {
                        cnstr_set_tag(o, ctor_info_idx(expr_reuse_ctor(e)).get_small_value());
                    }
                    for (size_t i = 0; i < expr_reuse_args(e).size(); i++) {
                        cnstr_set(o, i, eval_arg(expr_reuse_args(e)[i]));
                    }
                    return o;
                }
            }
            case expr_kind::Proj:
                return cnstr_get(var(expr_proj_obj(e)), expr_proj_idx(e).get_small_value());
            case expr_kind::UProj:
                return box_size_t(cnstr_get_usize(var(expr_uproj_obj(e)), expr_uproj_idx(e).get_small_value()));
            case expr_kind::SProj: {
                size_t offset = expr_sproj_num_objs(e).get_small_value() * sizeof(void *) +
                                expr_sproj_offset(e).get_small_value();
                object *o = var(expr_sproj_obj(e));
                switch (t) {
                    case type::Float: throw exception("floats are not supported yet");
                    case type::UInt8: return box(cnstr_get_uint8(o, offset));
                    case type::UInt16: return box(cnstr_get_uint16(o, offset));
                    case type::UInt32: return box_uint32(cnstr_get_uint32(o, offset));
                    case type::UInt64: return box_uint64(cnstr_get_uint64(o, offset));
                    default: throw exception("invalid instruction");
                }
            }
            case expr_kind::FAp: {
                if (expr_fap_args(e).size()) {
                    return call(expr_fap_fun(e), expr_fap_args(e));
                } else {
                    object * const * cached = m_constant_cache.find(expr_fap_fun(e));
                    if (cached) {
                        return *cached;
                    } else {
                        object * r = load(expr_fap_fun(e), t);
                        mark_persistent(r);
                        m_constant_cache.insert(expr_fap_fun(e), r);
                        return r;
                    }
                }
            }
            case expr_kind::PAp: {
                decl d = get_fdecl(expr_pap_fun(e));
                unsigned i = 0;
                object * cls;
                if (void * p = get_symbol_pointer(expr_pap_fun(e))) {
                    cls = alloc_closure(p, decl_params(d).size(), expr_pap_args(e).size());
                } else {
                    cls = alloc_closure(reinterpret_cast<void *>(stub_m_aux), 16 + decl_params(d).size(), 16 + expr_pap_args(e).size());
                    closure_set(cls, i++, box(reinterpret_cast<size_t>(this)));
                    closure_set(cls, i++, d.to_obj_arg());
                    for (; i < 16; i++) {
                        closure_set(cls, i, box(0));
                    }
                }
                for (arg const & a : expr_pap_args(e)) {
                    closure_set(cls, i++, eval_arg(a));
                }
                return cls;
            }
            case expr_kind::Ap: {
                size_t old_size = m_arg_stack.size();
                for (const auto & arg : expr_ap_args(e)) {
                    m_arg_stack.push_back(eval_arg(arg));
                }
                object * r = apply_n(var(expr_ap_fun(e)), expr_ap_args(e).size(), &m_arg_stack[old_size]);
                m_arg_stack.resize(old_size);
                return r;
            }
            case expr_kind::Box:
                return var(expr_box_obj(e));
            case expr_kind::Unbox:
                return var(expr_unbox_obj(e));
            case expr_kind::Lit:
                switch (lit_val_tag(expr_lit_val(e))) {
                    case lit_val_kind::Num: {
                        nat const & n = lit_val_num(expr_lit_val(e));
                        switch (t) {
                            case type::Float: throw exception("floats are not supported yet");
                            case type::UInt8: return n.raw();
                            case type::UInt16: return n.raw();
                            case type::UInt32: return box_uint32(n.get_small_value());
                            case type::UInt64: return box_uint64(n.get_small_value());
                            case type::USize: return box_size_t(n.get_small_value());
                            case type::Object:
                            case type::TObject:
                                return n.to_obj_arg();
                            default:
                                throw exception("invalid instruction");
                        }
                    }
                    case lit_val_kind::Str:
                        return lit_val_str(expr_lit_val(e)).to_obj_arg();
                }
            case expr_kind::IsShared:
                return box(!is_exclusive(var(expr_is_shared_obj(e))));
            case expr_kind::IsTaggedPtr:
                return box(!is_scalar(var(expr_is_tagged_ptr_obj(e))));
            default:
                throw exception(sstream() << "unexpected instruction kind " << static_cast<unsigned>(expr_tag(e)));
        }
    }

    object * eval_body(fn_body const & b0) {
        // make reference reassignable...
        std::reference_wrapper<fn_body const> b(b0);
        while (true) {
            DEBUG_CODE(lean_trace(name({"interpreter", "step"}),
                    tout() << std::string(m_call_stack.size(), ' ') << format_fn_body_head(b) << "\n";);)
            switch (fn_body_tag(b)) {
                case fn_body_kind::VDecl: {
                    expr const & e = fn_body_vdecl_expr(b);
                    fn_body const & cont = fn_body_vdecl_cont(b);
                    if (expr_tag(e) == expr_kind::FAp && expr_fap_fun(e) == get_frame().m_fn &&
                        fn_body_tag(cont) == fn_body_kind::Ret && !arg_is_irrelevant(fn_body_ret_arg(cont)) &&
                        arg_var_id(fn_body_ret_arg(cont)) == fn_body_vdecl_var(b)) {
                        // tail recursion
                        fun_id const & fn = expr_fap_fun(e);
                        decl d = get_decl(fn);
                        if (!get_symbol_pointer(fn)) {
                            if (decl_tag(d) == decl_kind::Extern) {
                                throw exception(sstream() << "unexpected external declaration '" << fn << "'");
                            }
                            array_ref<arg> const & args = expr_fap_args(e);
                            // copy bla bla
                            size_t old_size = m_arg_stack.size();
                            for (const auto & arg : args) {
                                m_arg_stack.push_back(eval_arg(arg));
                            }
                            for (size_t i = 0; i < args.size(); i++) {
                                m_arg_stack[get_frame().m_arg_bp + i] = m_arg_stack[old_size + i];
                            }
                            m_arg_stack.resize(get_frame().m_arg_bp + args.size());
                            b = decl_fun_body(d);
                            break;
                        }
                    }
                    var(fn_body_vdecl_var(b)) = eval_expr(fn_body_vdecl_expr(b), fn_body_vdecl_type(b));
                    DEBUG_CODE(lean_trace(name({"interpreter", "step"}),
                                          tout() << std::string(m_call_stack.size(), ' ') << "=> x_";
                                          tout() << fn_body_vdecl_var(b).get_small_value() << " = ";
                                          print_object(tout(), var(fn_body_vdecl_var(b)));
                                          tout() << "\n";);)
                    b = fn_body_vdecl_cont(b);
                    break;
                }
                case fn_body_kind::JDecl: {
                    size_t i = get_frame().m_jp_bp + fn_body_jdecl_id(b).get_small_value();
                    if (i >= m_jp_stack.size()) {
                        m_jp_stack.resize(i + 1);
                    }
                    m_jp_stack[i] = &b.get();
                    b = fn_body_jdecl_cont(b);
                    break;
                }
                case fn_body_kind::Set: {
                    object * o = var(fn_body_set_var(b));
                    lean_assert(is_exclusive(o));
                    cnstr_set(o, fn_body_set_idx(b).get_small_value(), eval_arg(fn_body_set_arg(b)));
                    b = fn_body_set_cont(b);
                    break;
                }
                case fn_body_kind::SetTag: {
                    object * o = var(fn_body_set_tag_var(b));
                    lean_assert(is_exclusive(o));
                    cnstr_set_tag(o, fn_body_set_tag_cidx(b).get_small_value());
                    b = fn_body_set_tag_cont(b);
                    break;
                }
                case fn_body_kind::USet: {
                    object * o = var(fn_body_uset_var(b));
                    lean_assert(is_exclusive(o));
                    cnstr_set_usize(o, fn_body_uset_idx(b).get_small_value(), unbox_size_t(eval_arg(fn_body_uset_arg(b))));
                    b = fn_body_uset_cont(b);
                    break;
                }
                case fn_body_kind::SSet: {
                    object * o = var(fn_body_sset_target(b));
                    size_t offset = fn_body_sset_num_objs(b).get_small_value() * sizeof(void *) +
                                    fn_body_sset_offset(b).get_small_value();
                    object * v = var(fn_body_sset_source(b));
                    lean_assert(is_exclusive(o));
                    switch (fn_body_sset_type(b)) {
                        case type::Float: throw exception("floats are not supported yet");
                        case type::UInt8: cnstr_set_uint8(o, offset, unbox(v)); break;
                        case type::UInt16: cnstr_set_uint16(o, offset, unbox(v)); break;
                        case type::UInt32: cnstr_set_uint32(o, offset, unbox_uint32(v)); break;
                        case type::UInt64: cnstr_set_uint64(o, offset, unbox_uint64(v)); break;
                        default: throw exception(sstream() << "invalid instruction");
                    }
                    b = fn_body_sset_cont(b);
                    break;
                }
                case fn_body_kind::Inc:
                    inc(var(fn_body_inc_var(b)), fn_body_inc_val(b).get_small_value());
                    b = fn_body_inc_cont(b);
                    break;
                case fn_body_kind::Dec: {
                    size_t n = fn_body_dec_val(b).get_small_value();
                    for (size_t i = 0; i < n; i++) {
                        dec(var(fn_body_dec_var(b)));
                    }
                    b = fn_body_dec_cont(b);
                    break;
                }
                case fn_body_kind::Del:
                    lean_free_object(var(fn_body_del_var(b)));
                    b = fn_body_del_cont(b);
                    break;
                case fn_body_kind::MData:
                    b = fn_body_mdata_cont(b);
                    break;
                case fn_body_kind::Case: {
                    object * o = var(fn_body_case_var(b));
                    size_t tag = is_scalar(o) ? unbox(o) : cnstr_tag(o);
                    for (alt_core const & a : fn_body_case_alts(b)) {
                        switch (alt_core_tag(a)) {
                            case alt_core_kind::Ctor:
                                if (tag == ctor_info_idx(alt_core_ctor_info(a)).get_small_value()) {
                                    b = alt_core_ctor_cont(a);
                                    goto done;
                                }
                                break;
                            case alt_core_kind::Default:
                                b = alt_core_default_cont(a);
                                goto done;
                        }
                    }
                    throw exception("incomplete case");
                    done: break;
                }
                case fn_body_kind::Ret:
                    return eval_arg(fn_body_ret_arg(b));
                case fn_body_kind::Jmp: {
                    fn_body const & jp = *m_jp_stack[get_frame().m_jp_bp + fn_body_jmp_jp(b).get_small_value()];
                    lean_assert(fn_body_jdecl_params(jp).size() == fn_body_jmp_args(b).size());
                    for (size_t i = 0; i < fn_body_jdecl_params(jp).size(); i++) {
                        var(param_var(fn_body_jdecl_params(jp)[i])) = eval_arg(fn_body_jmp_args(b)[i]);
                    }
                    b = fn_body_jdecl_body(jp);
                    break;
                }
                case fn_body_kind::Unreachable:
                    throw exception("unreachable code");
            }
        }
    }

    void push_frame(name const & fn, size_t arg_bp) {
        DEBUG_CODE({
            lean_trace(name({"interpreter", "call"}),
                       tout() << std::string(m_call_stack.size(), ' ')
                              << fn;
                       for (size_t i = arg_bp; i < m_arg_stack.size(); i++) {
                           tout() << " "; print_object(tout(), m_arg_stack[i]);
                       }
                       tout() << "\n";);
        });
        m_call_stack.push_back(frame { fn, arg_bp, m_jp_stack.size() });
    }

    void pop_frame(object * DEBUG_CODE(r)) {
        m_arg_stack.resize(get_frame().m_arg_bp);
        m_jp_stack.resize(get_frame().m_jp_bp);
        m_call_stack.pop_back();
        DEBUG_CODE({
            lean_trace(name({"interpreter", "call"}),
                       tout() << std::string(m_call_stack.size(), ' ')
                              << "=> ";
                       print_object(tout(), r);
                       tout() << "\n";);
       });
    }

    void * get_symbol_pointer(name const & fn, bool & boxed) {
        string_ref mangled = name_mangle(fn, *g_mangle_prefix);
        string_ref boxed_mangled(string_append(mangled.to_obj_arg(), g_boxed_mangled_suffix->raw()));
        if (void * p_boxed = dlsym(RTLD_DEFAULT, boxed_mangled.data())) {
            boxed = true;
            return p_boxed;
        } else if (void * p = dlsym(RTLD_DEFAULT, mangled.data())) {
            boxed = false;
            return p;
        } else {
            return nullptr;
        }
    }

    void * get_symbol_pointer(name const & fn) {
        bool boxed;
        return get_symbol_pointer(fn, boxed);
    }

    decl get_decl(name const & fn) {
        option_ref<decl> d = find_env_decl(m_env, fn);
        if (!d) {
            throw exception(sstream() << "unknown declaration '" << fn << "'");
        }
        return d.get().value();
    }

    decl get_fdecl(name const & fn) {
        decl d = get_decl(fn);
        if (decl_tag(d) == decl_kind::Extern) {
            throw exception(sstream() << "unexpected external declaration '" << fn << "'");
        }
        return d;
    }

    // evaluate 0-ary function
    object * load(name const & fn, type t) {
        if (void * p = get_symbol_pointer(fn)) {
            switch (t) {
                case type::Float: throw exception("floats are not supported yet");
                case type::UInt8: return box(*static_cast<uint8 *>(p));
                case type::UInt16: return box(*static_cast<uint16 *>(p));
                case type::UInt32: return box_uint32(*static_cast<uint32 *>(p));
                case type::UInt64: return box_uint64(*static_cast<uint64 *>(p));
                case type::USize: return box_size_t(*static_cast<size_t *>(p));
                case type::Object:
                case type::TObject:
                    return *static_cast<object **>(p);
                default:
                    throw exception("invalid type");
            }
        } else {
            push_frame(fn, m_arg_stack.size());
            decl d = get_fdecl(fn);
            object * r = eval_body(decl_fun_body(d));
            pop_frame(r);
            return r;
        }
    }

    object * call(name const & fn, array_ref<arg> const & args) {
        size_t old_size = m_arg_stack.size();

        // evaluate args in old stack frame
        for (const auto & arg : args) {
            m_arg_stack.push_back(eval_arg(arg));
        }

        decl d = get_decl(fn);
        push_frame(fn, old_size);
        object * r;
        bool boxed;
        if (void * p = get_symbol_pointer(fn, boxed)) {
            for (size_t i = 0; i < args.size(); i++) {
                if (param_borrow(decl_params(d)[i])) {
                    inc(m_arg_stack[old_size + i]);
                }
            }
            object * cls = alloc_closure(p, 2, 1);
            r = curry(cls, args.size(), &m_arg_stack[old_size]);
            free_heap_obj(cls);
        } else {
            if (decl_tag(d) == decl_kind::Extern) {
                throw exception(sstream() << "unexpected external declaration '" << fn << "'");
            }
            r = eval_body(decl_fun_body(d));
        }
        pop_frame(r);
        return r;
    }
public:
    explicit interpreter(environment const & env) : m_env(env) {}

    uint32 run_main(int argc, char * argv[]) {
        decl d = get_fdecl("main");
        array_ref<param> const & params = decl_params(d);
        if (params.size() == 2) {
            lean_object * in = lean_box(0);
            int i = argc;
            while (i > 1) {
                i--;
                lean_object * n = lean_alloc_ctor(1, 2, 0);
                lean_ctor_set(n, 0, lean_mk_string(argv[i]));
                lean_ctor_set(n, 1, in);
                in = n;
            }
            m_arg_stack.push_back(in);
        } else {
            lean_assert(params.size() == 1);
        }
        object * w = io_mk_world();
        m_arg_stack.push_back(w);
        push_frame("main", 0);
        w = eval_body(decl_fun_body(d));
        pop_frame(w);
        if (io_result_is_ok(w)) {
            int ret = unbox(io_result_get_value(w));
            dec_ref(w);
            return ret;
        } else {
            io_result_show_error(w);
            dec_ref(w);
            return 1;
        }
    }

    object * stub_m(object ** args) {
        decl d(args[1]);
        size_t old_size = m_arg_stack.size();
        for (size_t i = 0; i < decl_params(d).size(); i++) {
            m_arg_stack.push_back(args[16 + i]);
        }
        push_frame(decl_fun_id(d), old_size);
        object * r = eval_body(decl_fun_body(d));
        pop_frame(r);
        return r;
    }

    static object * stub_m_aux(object ** args) {
        interpreter * self = reinterpret_cast<interpreter *>(unbox(args[0]));
        return self->stub_m(args);
    }
};

uint32 run_main(environment const & env, int argv, char * argc[]) {
    return interpreter(env).run_main(argv, argc);
}
}

void initialize_ir_interpreter() {
    ir::g_mangle_prefix = new string_ref("l_");
    ir::g_boxed_mangled_suffix = new string_ref("___boxed");
    DEBUG_CODE({
        register_trace_class({"interpreter"});
        register_trace_class({"interpreter", "call"});
        register_trace_class({"interpreter", "step"});
    });
}

void finalize_ir_interpreter() {
    delete ir::g_boxed_mangled_suffix;
    delete ir::g_mangle_prefix;
}
}
