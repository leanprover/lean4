/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich

A simple interpreter for evaluating λRC IR code.

Motivation
==========

Even with a JIT compiler, we still have a need for a simpler interpreter on platforms LLVM JIT does not support (i.e.
WebAssembly). Because this is mostly an edge case, we strive for simplicity instead of performance and thus reuse the
existing compiler IR instead of inventing something like a new bytecode format.

Implementation
==============

The interpreter mainly consists of a homogeneous stack of `value`s, which are either unboxed values or pointers to boxed
objects. The IR type system tells us which union member is active at any time. IR variables are mapped to stack
slots by adding the current base pointer to the variable index. Further stacks are used for storing join points and call
stack metadata. The interpreted IR is taken directly from the environment. Whenever possible, we try to switch to native
code by checking for the mangled symbol via dlsym/GetProcAddress, which is also how we can call external functions
(which only works if the file declaring them has already been compiled). We always call the "boxed" versions of native
functions, which have a (relatively) homogeneous ABI that we can use without runtime code generation; see also
`call/lookup_symbol` below.

*/
#include <string>
#include <vector>
#ifdef LEAN_WINDOWS
#include <windows.h>
#include <psapi.h>
#else
#include <dlfcn.h>
#endif
#include "runtime/flet.h"
#include "runtime/apply.h"
#include "runtime/interrupt.h"
#include "runtime/io.h"
#include "runtime/option_ref.h"
#include "runtime/array_ref.h"
#include "library/time_task.h"
#include "library/trace.h"
#include "library/compiler/ir.h"
#include "library/compiler/init_attribute.h"
#include "util/nat.h"
#include "util/option_declarations.h"

#ifndef LEAN_DEFAULT_INTERPRETER_PREFER_NATIVE
#define LEAN_DEFAULT_INTERPRETER_PREFER_NATIVE true
#endif

namespace lean {
namespace ir {
// C++ wrappers of Lean data types

typedef object_ref lit_val;
typedef object_ref ctor_info;

type to_type(object * obj) {
    if (!is_scalar(obj)) throw exception("unsupported IRType");
    else return static_cast<type>(unbox(obj));
}
type cnstr_get_type(object_ref const & o, unsigned i) { return to_type(cnstr_get(o.raw(), i)); }

bool arg_is_irrelevant(arg const & a) { return is_scalar(a.raw()); }
var_id const & arg_var_id(arg const & a) { lean_assert(!arg_is_irrelevant(a)); return cnstr_get_ref_t<var_id>(a, 0); }

enum class lit_val_kind { Num, Str };
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

enum class expr_kind { Ctor, Reset, Reuse, Proj, UProj, SProj, FAp, PAp, Ap, Box, Unbox, Lit, IsShared, IsTaggedPtr };
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
enum class alt_core_kind { Ctor, Default };
alt_core_kind alt_core_tag(alt_core const & a) { return static_cast<alt_core_kind>(cnstr_tag(a.raw())); }
ctor_info const & alt_core_ctor_info(alt_core const & a) { lean_assert(alt_core_tag(a) == alt_core_kind::Ctor); return cnstr_get_ref_t<ctor_info>(a, 0); }
fn_body const & alt_core_ctor_cont(alt_core const & a) { lean_assert(alt_core_tag(a) == alt_core_kind::Ctor); return cnstr_get_ref_t<fn_body>(a, 1); }
fn_body const & alt_core_default_cont(alt_core const & a) { lean_assert(alt_core_tag(a) == alt_core_kind::Default); return cnstr_get_ref_t<fn_body>(a, 0); }

enum class fn_body_kind { VDecl, JDecl, Set, SetTag, USet, SSet, Inc, Dec, Del, MData, Case, Ret, Jmp, Unreachable };
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
enum class decl_kind { Fun, Extern };
decl_kind decl_tag(decl const & a) { return is_scalar(a.raw()) ? static_cast<decl_kind>(unbox(a.raw())) : static_cast<decl_kind>(cnstr_tag(a.raw())); }
fun_id const & decl_fun_id(decl const & b) { return cnstr_get_ref_t<fun_id>(b, 0); }
array_ref<param> const & decl_params(decl const & b) { return cnstr_get_ref_t<array_ref<param>>(b, 1); }
type decl_type(decl const & b) { return cnstr_get_type(b, 2); }
fn_body const & decl_fun_body(decl const & b) { lean_assert(decl_tag(b) == decl_kind::Fun); return cnstr_get_ref_t<fn_body>(b, 3); }

extern "C" object * lean_ir_find_env_decl(object * env, object * n);
option_ref<decl> find_ir_decl(environment const & env, name const & n) {
    return option_ref<decl>(lean_ir_find_env_decl(env.to_obj_arg(), n.to_obj_arg()));
}

extern "C" double lean_float_of_nat(lean_obj_arg a);

static string_ref * g_mangle_prefix = nullptr;
static string_ref * g_boxed_suffix = nullptr;
static string_ref * g_boxed_mangled_suffix = nullptr;
static name * g_interpreter_prefer_native = nullptr;

// constants (lacking native declarations) initialized by `lean_run_init`
static name_map<object *> * g_init_globals;

// reuse the compiler's name mangling to compute native symbol names
extern "C" object * lean_name_mangle(object * n, object * pre);
string_ref name_mangle(name const & n, string_ref const & pre) {
    return string_ref(lean_name_mangle(n.to_obj_arg(), pre.to_obj_arg()));
}

extern "C" object * lean_ir_format_fn_body_head(object * b);
std::string format_fn_body_head(fn_body const & b) {
    return string_to_std(lean_ir_format_fn_body_head(b.to_obj_arg()));
}

static bool type_is_scalar(type t) {
    return t != type::Object && t != type::TObject && t != type::Irrelevant;
}

extern "C" object* lean_get_regular_init_fn_name_for(object* env, object* fn);
optional<name> get_regular_init_fn_name_for(environment const & env, name const & n) {
    return to_optional<name>(lean_get_regular_init_fn_name_for(env.to_obj_arg(), n.to_obj_arg()));
}

extern "C" object* lean_get_builtin_init_fn_name_for(object* env, object* fn);
optional<name> get_builtin_init_fn_name_for(environment const & env, name const & n) {
    return to_optional<name>(lean_get_builtin_init_fn_name_for(env.to_obj_arg(), n.to_obj_arg()));
}

/** \brief Value stored in an interpreter variable slot */
union value {
    // NOTE: the IR type system guarantees that we always access the active union member
    uint64   m_num; // big enough for any unboxed integral type
    static_assert(sizeof(size_t) <= sizeof(uint64), "uint64 should be the largest unboxed type"); // NOLINT
    double   m_float;
    object * m_obj;

    value() {}
    // too convenient to make explicit
    value(uint64 num): m_num(num) {}
    value(object * o): m_obj(o) {}

    // would overlap with `value(uint64)` as a constructor
    static value from_float(double f) {
        value v;
        v.m_float = f;
        return v;
    }
};

object * box_t(value v, type t) {
    switch (t) {
        case type::Float: return box_float(v.m_float);
        case type::UInt8: return box(v.m_num);
        case type::UInt16: return box(v.m_num);
        case type::UInt32: return box_uint32(v.m_num);
        case type::UInt64: return box_uint64(v.m_num);
        case type::USize: return box_size_t(v.m_num);
        case type::Object:
        case type::TObject:
        case type::Irrelevant:
            return v.m_obj;
    }
    lean_unreachable();
}

value unbox_t(object * o, type t) {
    switch (t) {
        case type::Float: return value::from_float(unbox_float(o));
        case type::UInt8: return unbox(o);
        case type::UInt16: return unbox(o);
        case type::UInt32: return unbox_uint32(o);
        case type::UInt64: return unbox_uint64(o);
        case type::USize: return unbox_size_t(o);
        case type::Irrelevant:
        case type::Object:
        case type::TObject:
            break;
    }
    lean_unreachable();
}

/** \pre Very simple debug output of arbitrary values, should be extended. */
void print_value(tout & ios, value const & v, type t) {
    if (t == type::Float) {
        ios << v.m_float;
    } else if (type_is_scalar(t)) {
        ios << v.m_num;
    } else {
        if (is_scalar(v.m_obj)) {
            ios << unbox(v.m_obj);
        } else if (v.m_obj == nullptr) {
            ios << "0x0"; // confusingly printed as "0" by the default operator<<
        } else {
            // merely following the trace of object addresses is surprisingly helpful for debugging
            ios << v.m_obj;
        }
    }
}

void print_value(tout const & ios, value const & v, type t) {
  return print_value(const_cast<tout &>(ios), v, t);
}

void * lookup_symbol_in_cur_exe(char const * sym) {
#ifdef LEAN_WINDOWS
    std::vector<HMODULE> hmods(128);
    DWORD bytes_needed;
    lean_always_assert(EnumProcessModules(GetCurrentProcess(), &hmods[0], hmods.size() * sizeof(HMODULE), &bytes_needed));
    unsigned num_mods = bytes_needed / sizeof(HMODULE);
    if (num_mods > hmods.size()) {
        hmods.resize(num_mods);
        lean_always_assert(EnumProcessModules(GetCurrentProcess(), &hmods[0], hmods.size() * sizeof(HMODULE), &bytes_needed));
    } else {
        hmods.resize(num_mods);
    }
    for (HMODULE hmod : hmods) {
        void * addr = reinterpret_cast<void *>(GetProcAddress(hmod, sym));
        if (addr) {
            return addr;
        }
    }
    return nullptr;
#else
    return dlsym(RTLD_DEFAULT, sym);
#endif
}

class interpreter;
LEAN_THREAD_PTR(interpreter, g_interpreter);

class interpreter {
    // stack of IR variable slots
    std::vector<value> m_arg_stack;
    // stack of join points
    std::vector<fn_body const *> m_jp_stack;
    struct frame {
        name m_fn;
        // base pointers into the stack above
        size_t m_arg_bp;
        size_t m_jp_bp;

        frame(name const & mFn, size_t mArgBp, size_t mJpBp) : m_fn(mFn), m_arg_bp(mArgBp), m_jp_bp(mJpBp) {}
    };
    std::vector<frame> m_call_stack;
    environment const & m_env;
    options const & m_opts;
    // if `false`, use IR code where possible
    bool m_prefer_native;
    struct constant_cache_entry {
      bool m_is_scalar;
      value m_val;
    };
    // caches values of nullary functions ("constants")
    name_map<constant_cache_entry> m_constant_cache;
    struct symbol_cache_entry {
        decl m_decl;
        // symbol address; `nullptr` if function does not have native code
        void * m_addr;
        // true iff we chose the boxed version of a function where the IR uses the unboxed version
        bool m_boxed;
    };
    // caches symbol lookup successes _and_ failures
    name_map<symbol_cache_entry> m_symbol_cache;

    /** \brief Get current stack frame */
    inline frame & get_frame() {
        return m_call_stack.back();
    }

    /** \brief Get reference to stack slot of IR variable */
    inline value & var(var_id const & v) {
        // variables are 1-indexed
        size_t i = get_frame().m_arg_bp + v.get_small_value() - 1;
        // we don't know the frame size (unless we do an additional IR pass), so we extend it dynamically
        if (i >= m_arg_stack.size()) {
            m_arg_stack.resize(i + 1);
        }
        return m_arg_stack[i];
    }

public:
    template<class T>
    static inline T with_interpreter(environment const & env, options const & opts, name const & fn, std::function<T(interpreter &)> const & f) {
        if (g_interpreter && is_eqp(g_interpreter->m_env, env) && is_eqp(g_interpreter->m_opts, opts)) {
            return f(*g_interpreter);
        } else {
            // We changed threads or the closure was stored and called in a different context.
            time_task t("interpretation", opts, fn);
            scope_trace_env scope_trace(env, opts);
            // the caches contain data from the Environment, so we cannot reuse them when changing it
            interpreter interp(env, opts);
            flet<interpreter *> fl(g_interpreter, &interp);
            return f(interp);
        }
    }

private:
    value eval_arg(arg const & a) {
        // an "irrelevant" argument is type- or proof-erased; we can use an arbitrary value for it
        return arg_is_irrelevant(a) ? box(0) : var(arg_var_id(a));
    }

    /** \brief Allocate constructor object with given tag and arguments */
    object * alloc_ctor(ctor_info const & i, array_ref<arg> const & args) {
        size_t tag = ctor_info_tag(i).get_small_value();
        // number of boxed object fields
        size_t size = ctor_info_size(i).get_small_value();
        // number of unboxed USize fields (whose byte size the IR is ignorant of)
        size_t usize = ctor_info_usize(i).get_small_value();
        // byte size of all other unboxed fields
        size_t ssize = ctor_info_ssize(i).get_small_value();
        if (size == 0 && usize == 0 && ssize == 0) {
            // a constructor without data is optimized to a tagged pointer
            return box(tag);
        } else {
            object *o = alloc_cnstr(tag, size, usize * sizeof(void *) + ssize);
            for (size_t i = 0; i < args.size(); i++) {
                cnstr_set(o, i, eval_arg(args[i]).m_obj);
            }
            return o;
        }
    }

    /** \brief Return closure pointing to interpreter stub taking interpreter data, declaration to be called, and partially
        applied arguments. */
    object * mk_stub_closure(decl const & d, unsigned n, object ** args) {
        unsigned cls_size = 3 + decl_params(d).size();
        object * cls = alloc_closure(get_stub(cls_size), cls_size, 3 + n);
        closure_set(cls, 0, m_env.to_obj_arg());
        closure_set(cls, 1, m_opts.to_obj_arg());
        closure_set(cls, 2, d.to_obj_arg());
        for (unsigned i = 0; i < n ; i++)
            closure_set(cls, 3 + i, args[i]);
        return cls;
    }

    value eval_expr(expr const & e, type t) {
        switch (expr_tag(e)) {
            case expr_kind::Ctor:
                return value { alloc_ctor(expr_ctor_info(e), expr_ctor_args(e)) };
            case expr_kind::Reset: { // release fields if unique reference in preparation for `Reuse` below
                object * o = var(expr_reset_obj(e)).m_obj;
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
            case expr_kind::Reuse: { // reuse dead allocation if possible
                object * o = var(expr_reuse_obj(e)).m_obj;
                // check if `Reset` above had a unique reference it consumed
                if (is_scalar(o)) {
                    // fall back to regular allocation
                    return alloc_ctor(expr_reuse_ctor(e), expr_reuse_args(e));
                } else {
                    // create new constructor object in-place
                    if (expr_reuse_update_header(e)) {
                        cnstr_set_tag(o, ctor_info_tag(expr_reuse_ctor(e)).get_small_value());
                    }
                    for (size_t i = 0; i < expr_reuse_args(e).size(); i++) {
                        cnstr_set(o, i, eval_arg(expr_reuse_args(e)[i]).m_obj);
                    }
                    return o;
                }
            }
            case expr_kind::Proj: // object field access
                return cnstr_get(var(expr_proj_obj(e)).m_obj, expr_proj_idx(e).get_small_value());
            case expr_kind::UProj: // USize field access
                return cnstr_get_usize(var(expr_uproj_obj(e)).m_obj, expr_uproj_idx(e).get_small_value());
            case expr_kind::SProj: { // other unboxed field access
                size_t offset = expr_sproj_idx(e).get_small_value() * sizeof(void *) +
                                expr_sproj_offset(e).get_small_value();
                object * o = var(expr_sproj_obj(e)).m_obj;
                switch (t) {
                    case type::Float: return value::from_float(cnstr_get_float(o, offset));
                    case type::UInt8: return cnstr_get_uint8(o, offset);
                    case type::UInt16: return cnstr_get_uint16(o, offset);
                    case type::UInt32: return cnstr_get_uint32(o, offset);
                    case type::UInt64: return cnstr_get_uint64(o, offset);
                    case type::USize:
                    case type::Irrelevant:
                    case type::Object:
                    case type::TObject:
                        break;
                }
                throw exception("invalid instruction");
            }
            case expr_kind::FAp: { // satured ("full") application of top-level function
                if (expr_fap_args(e).size()) {
                    return call(expr_fap_fun(e), expr_fap_args(e));
                } else {
                    // nullary function ("constant")
                    return load(expr_fap_fun(e), t);
                }
            }
            case expr_kind::PAp: { // unsatured (partial) application of top-level function
                symbol_cache_entry sym = lookup_symbol(expr_pap_fun(e));
                if (sym.m_addr) {
                    // point closure directly at native symbol
                    object * cls = alloc_closure(sym.m_addr, decl_params(sym.m_decl).size(), expr_pap_args(e).size());
                    for (unsigned i = 0; i < expr_pap_args(e).size(); i++) {
                        closure_set(cls, i, eval_arg(expr_pap_args(e)[i]).m_obj);
                    }
                    return cls;
                } else {
                    // point closure at interpreter stub
                    object ** args = static_cast<object **>(LEAN_ALLOCA(expr_pap_args(e).size() * sizeof(object *))); // NOLINT
                    for (size_t i = 0; i < expr_pap_args(e).size(); i++) {
                        args[i] = eval_arg(expr_pap_args(e)[i]).m_obj;
                    }
                    return mk_stub_closure(sym.m_decl, expr_pap_args(e).size(), args);
                }
            }
            case expr_kind::Ap: { // (saturated or unsatured) application of closure; mostly handled by runtime
                object ** args = static_cast<object **>(LEAN_ALLOCA(expr_ap_args(e).size() * sizeof(object *))); // NOLINT
                for (size_t i = 0; i < expr_ap_args(e).size(); i++) {
                    args[i] = eval_arg(expr_ap_args(e)[i]).m_obj;
                }
                object * r = apply_n(var(expr_ap_fun(e)).m_obj, expr_ap_args(e).size(), args);
                return r;
            }
            case expr_kind::Box: // box unboxed value
                return box_t(var(expr_box_obj(e)).m_num, expr_box_type(e));
            case expr_kind::Unbox: // unbox boxed value
                return unbox_t(var(expr_unbox_obj(e)).m_obj, t);
            case expr_kind::Lit: // load numeric or string literal
                switch (lit_val_tag(expr_lit_val(e))) {
                    case lit_val_kind::Num: {
                        nat const & n = lit_val_num(expr_lit_val(e));
                        switch (t) {
                            case type::Float:
                                lean_inc(n.raw());
                                return value::from_float(lean_float_of_nat(n.raw()));
                            case type::UInt8:
                            case type::UInt16:
                            case type::UInt32:
                            case type::USize:
                                return lean_usize_of_nat(n.raw());
                            case type::UInt64:
                                return lean_uint64_of_nat(n.raw());
                            // `nat` literal
                            case type::Object:
                            case type::TObject:
                                return n.to_obj_arg();
                            case type::Irrelevant:
                                break;
                        }
                        throw exception("invalid instruction");
                    }
                    case lit_val_kind::Str:
                        return lit_val_str(expr_lit_val(e)).to_obj_arg();
                }
                break;
            case expr_kind::IsShared:
                return !is_exclusive(var(expr_is_shared_obj(e)).m_obj);
            case expr_kind::IsTaggedPtr:
                return !is_scalar(var(expr_is_tagged_ptr_obj(e)).m_obj);
        }
        throw exception(sstream() << "unexpected instruction kind " << static_cast<unsigned>(expr_tag(e)));
    }

    void check_system() {
        try {
            lean::check_system("interpreter");
        } catch (stack_space_exception & ex) {
            sstream ss;
            ss << ex.what() << "\n";
            ss << "interpreter stacktrace:\n";
            for (unsigned i = 0; i < m_call_stack.size(); i++) {
                ss << "#" << (i + 1) << " " << m_call_stack[m_call_stack.size() - i - 1].m_fn << "\n";
            }
            throw throwable(ss);
        }
    }

    value eval_body(fn_body const & b0) {
        check_system();

        // make reference reassignable...
        std::reference_wrapper<fn_body const> b(b0);
        while (true) {
            DEBUG_CODE(lean_trace(name({"interpreter", "step"}),
                                  tout() << std::string(m_call_stack.size(), ' ') << format_fn_body_head(b) << "\n";);)
            switch (fn_body_tag(b)) {
                case fn_body_kind::VDecl: { // variable declaration
                    expr const & e = fn_body_vdecl_expr(b);
                    fn_body const & cont = fn_body_vdecl_cont(b);
                    // tail recursion?
                    if (expr_tag(e) == expr_kind::FAp && expr_fap_fun(e) == get_frame().m_fn &&
                        fn_body_tag(cont) == fn_body_kind::Ret && !arg_is_irrelevant(fn_body_ret_arg(cont)) &&
                        arg_var_id(fn_body_ret_arg(cont)) == fn_body_vdecl_var(b)) {
                        // tail recursion! copy argument values to parameter slots and reset `b`
                        array_ref<arg> const & args = expr_fap_args(e);
                        // argument and parameter slots may overlap, so first copy arguments to end of stack
                        size_t old_size = m_arg_stack.size();
                        for (const auto & arg : args) {
                            m_arg_stack.push_back(eval_arg(arg));
                        }
                        // now copy to parameter slots
                        for (size_t i = 0; i < args.size(); i++) {
                            m_arg_stack[get_frame().m_arg_bp + i] = m_arg_stack[old_size + i];
                        }
                        m_arg_stack.resize(get_frame().m_arg_bp + args.size());
                        b = b0;
                        check_system();
                        break;
                    }
                    value v = eval_expr(fn_body_vdecl_expr(b), fn_body_vdecl_type(b));
                    // NOTE: `var` must be called *after* `eval_expr` because the stack may get resized and invalidate
                    // the pointer
                    var(fn_body_vdecl_var(b)) = v;
                    DEBUG_CODE(lean_trace(name({"interpreter", "step"}),
                                          tout() << std::string(m_call_stack.size(), ' ') << "=> x_";
                                          tout() << fn_body_vdecl_var(b).get_small_value() << " = ";
                                          print_value(tout(), var(fn_body_vdecl_var(b)), fn_body_vdecl_type(b));
                                          tout() << "\n";);)
                    b = fn_body_vdecl_cont(b);
                    break;
                }
                case fn_body_kind::JDecl: { // join-point declaration; store in stack slot just like variables
                    size_t i = get_frame().m_jp_bp + fn_body_jdecl_id(b).get_small_value();
                    if (i >= m_jp_stack.size()) {
                        m_jp_stack.resize(i + 1);
                    }
                    m_jp_stack[i] = &b.get();
                    b = fn_body_jdecl_cont(b);
                    break;
                }
                case fn_body_kind::Set: { // set boxed field of unique reference
                    object * o = var(fn_body_set_var(b)).m_obj;
                    lean_assert(is_exclusive(o));
                    cnstr_set(o, fn_body_set_idx(b).get_small_value(), eval_arg(fn_body_set_arg(b)).m_obj);
                    b = fn_body_set_cont(b);
                    break;
                }
                case fn_body_kind::SetTag: { // set constructor tag of unique reference
                    object * o = var(fn_body_set_tag_var(b)).m_obj;
                    lean_assert(is_exclusive(o));
                    cnstr_set_tag(o, fn_body_set_tag_cidx(b).get_small_value());
                    b = fn_body_set_tag_cont(b);
                    break;
                }
                case fn_body_kind::USet: { // set USize field of unique reference
                    object * o = var(fn_body_uset_target(b)).m_obj;
                    lean_assert(is_exclusive(o));
                    cnstr_set_usize(o, fn_body_uset_idx(b).get_small_value(), var(fn_body_uset_source(b)).m_num);
                    b = fn_body_uset_cont(b);
                    break;
                }
                case fn_body_kind::SSet: { // set other unboxed field of unique reference
                    object * o = var(fn_body_sset_target(b)).m_obj;
                    size_t offset = fn_body_sset_idx(b).get_small_value() * sizeof(void *) +
                                    fn_body_sset_offset(b).get_small_value();
                    value v = var(fn_body_sset_source(b));
                    lean_assert(is_exclusive(o));
                    switch (fn_body_sset_type(b)) {
                        case type::Float: cnstr_set_float(o, offset, v.m_float); break;
                        case type::UInt8: cnstr_set_uint8(o, offset, v.m_num); break;
                        case type::UInt16: cnstr_set_uint16(o, offset, v.m_num); break;
                        case type::UInt32: cnstr_set_uint32(o, offset, v.m_num); break;
                        case type::UInt64: cnstr_set_uint64(o, offset, v.m_num); break;
                        case type::USize:
                        case type::Irrelevant:
                        case type::Object:
                        case type::TObject:
                            throw exception(sstream() << "invalid instruction");
                    }
                    b = fn_body_sset_cont(b);
                    break;
                }
                case fn_body_kind::Inc: // increment reference counter
                    inc(var(fn_body_inc_var(b)).m_obj, fn_body_inc_val(b).get_small_value());
                    b = fn_body_inc_cont(b);
                    break;
                case fn_body_kind::Dec: { // decrement reference counter
                    size_t n = fn_body_dec_val(b).get_small_value();
                    for (size_t i = 0; i < n; i++) {
                        dec(var(fn_body_dec_var(b)).m_obj);
                    }
                    b = fn_body_dec_cont(b);
                    break;
                }
                case fn_body_kind::Del: // delete object of unique reference
                    lean_free_object(var(fn_body_del_var(b)).m_obj);
                    b = fn_body_del_cont(b);
                    break;
                case fn_body_kind::MData: // metadata; no-op
                    b = fn_body_mdata_cont(b);
                    break;
                case fn_body_kind::Case: { // branch according to constructor tag
                    array_ref<alt_core> const & alts = fn_body_case_alts(b);
                    unsigned tag;
                    value v = var(fn_body_case_var(b));
                    if (type_is_scalar(fn_body_case_var_type(b))) {
                        tag = v.m_num;
                    } else {
                        tag = lean_obj_tag(v.m_obj);
                    }
                    for (alt_core const & a : alts) {
                        switch (alt_core_tag(a)) {
                            case alt_core_kind::Ctor:
                                if (tag == ctor_info_tag(alt_core_ctor_info(a)).get_small_value()) {
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
                case fn_body_kind::Jmp: { // jump to join-point
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

    // specify argument base pointer explicitly because we've usually already pushed some function arguments
    void push_frame(decl const & d, size_t arg_bp) {
        DEBUG_CODE({
            lean_trace(name({"interpreter", "call"}),
                       tout() << std::string(m_call_stack.size(), ' ')
                              << decl_fun_id(d);
                       for (size_t i = arg_bp; i < m_arg_stack.size(); i++) {
                           tout() << " "; print_value(tout(), m_arg_stack[i], param_type(decl_params(d)[i - arg_bp]));
                       }
                       tout() << "\n";);
        });
        m_call_stack.emplace_back(decl_fun_id(d), arg_bp, m_jp_stack.size());
    }

    void pop_frame(value DEBUG_CODE(r), type DEBUG_CODE(t)) {
        m_arg_stack.resize(get_frame().m_arg_bp);
        m_jp_stack.resize(get_frame().m_jp_bp);
        m_call_stack.pop_back();
        DEBUG_CODE({
            lean_trace(name({"interpreter", "call"}),
                       tout() << std::string(m_call_stack.size(), ' ')
                              << "=> ";
                       print_value(tout(), r, t);
                       tout() << "\n";);
       });
    }

    /** \brief Return cached lookup result for given unmangled function name in the current binary. */
    symbol_cache_entry lookup_symbol(name const & fn) {
        if (symbol_cache_entry const * e = m_symbol_cache.find(fn)) {
            return *e;
        } else {
            symbol_cache_entry e_new { get_decl(fn), nullptr, false };
            if (m_prefer_native || decl_tag(e_new.m_decl) == decl_kind::Extern || has_init_attribute(m_env, fn)) {
                string_ref mangled = name_mangle(fn, *g_mangle_prefix);
                string_ref boxed_mangled(string_append(mangled.to_obj_arg(), g_boxed_mangled_suffix->raw()));
                // check for boxed version first
                if (void *p_boxed = lookup_symbol_in_cur_exe(boxed_mangled.data())) {
                    e_new.m_addr = p_boxed;
                    e_new.m_boxed = true;
                } else if (void *p = lookup_symbol_in_cur_exe(mangled.data())) {
                    // if there is no boxed version, there are no unboxed parameters, so use default version
                    e_new.m_addr = p;
                }
            }
            m_symbol_cache.insert(fn, e_new);
            return e_new;
        }
    }

    /** \brief Retrieve Lean declaration from environment. */
    decl get_decl(name const & fn) {
        option_ref<decl> d = find_ir_decl(m_env, fn);
        if (!d) {
            throw exception(sstream() << "unknown declaration '" << fn << "'");
        }
        return d.get().value();
    }

    /** \brief Evaluate nullary function ("constant"). */
    value load(name const & fn, type t) {
        if (constant_cache_entry const * cached = m_constant_cache.find(fn)) {
            if (!cached->m_is_scalar) {
                inc(cached->m_val.m_obj);
            }
            return cached->m_val;
        }
        if (object * const * o = g_init_globals->find(fn)) {
            // persistent, so no `inc` needed
            return *o;
        }

        symbol_cache_entry e = lookup_symbol(fn);
        if (e.m_addr) {
            // we can assume that all native code has been initialized (see e.g. `evalConst`)

            // constants do not have boxed wrappers, but we'll survive
            switch (t) {
                case type::Float: return value::from_float(*static_cast<double *>(e.m_addr));
                case type::UInt8: return *static_cast<uint8 *>(e.m_addr);
                case type::UInt16: return *static_cast<uint16 *>(e.m_addr);
                case type::UInt32: return *static_cast<uint32 *>(e.m_addr);
                case type::UInt64: return *static_cast<uint64 *>(e.m_addr);
                case type::USize: return *static_cast<size_t *>(e.m_addr);
                case type::Object:
                case type::TObject:
                case type::Irrelevant:
                    return *static_cast<object **>(e.m_addr);
            }
        }

        // no native code, so might be part of the current module
        if (get_regular_init_fn_name_for(m_env, fn)) {
            // We don't know whether `[init]` decls can be re-executed, so let's not.
            throw exception(sstream() << "cannot evaluate `[init]` declaration '" << fn << "' in the same module");
        }
        push_frame(e.m_decl, m_arg_stack.size());
        value r = eval_body(decl_fun_body(e.m_decl));
        pop_frame(r, decl_type(e.m_decl));
        if (!type_is_scalar(t)) {
            inc(r.m_obj);
        }
        m_constant_cache.insert(fn, constant_cache_entry { type_is_scalar(t), r });
        return r;
    }

    value call(name const & fn, array_ref<arg> const & args) {
        size_t old_size = m_arg_stack.size();
        value r;
        symbol_cache_entry e = lookup_symbol(fn);
        if (e.m_addr) {
            object ** args2 = static_cast<object **>(LEAN_ALLOCA(args.size() * sizeof(object *))); // NOLINT
            for (size_t i = 0; i < args.size(); i++) {
                type t = param_type(decl_params(e.m_decl)[i]);
                args2[i] = box_t(eval_arg(args[i]), t);
                if (e.m_boxed && param_borrow(decl_params(e.m_decl)[i])) {
                    // NOTE: If we chose the boxed version where the IR chose the unboxed one, we need to manually increment
                    // originally borrowed parameters because the wrapper will decrement these after the call.
                    // Basically the wrapper is more homogeneous (removing both unboxed and borrowed parameters) than we
                    // would need in this instance.
                    inc(args2[i]);
                }
            }
            push_frame(e.m_decl, old_size);
            object * o = curry(e.m_addr, args.size(), args2);
            type t = decl_type(e.m_decl);
            if (type_is_scalar(t)) {
                lean_assert(e.m_boxed);
                // NOTE: this unboxing does not exist in the IR, so we should manually consume `o`
                r = unbox_t(o, t);
                lean_dec(o);
            } else {
                r = o;
            }
        } else {
            if (decl_tag(e.m_decl) == decl_kind::Extern) {
                string_ref mangled = name_mangle(fn, *g_mangle_prefix);
                string_ref boxed_mangled(string_append(mangled.to_obj_arg(), g_boxed_mangled_suffix->raw()));
                throw exception(sstream() << "Could not find native implementation of external declaration '" << fn
                                          << "' (symbols '" << boxed_mangled.data() << "' or '" << mangled.data() << "').\n"
                                          << "For declarations from `Init` or `Lean`, you need to set `supportInterpreter := true` "
                                          << "in the relevant `lean_exe` statement in your `lakefile.lean`.");
            }
            // evaluate args in old stack frame
            for (const auto & arg : args) {
                m_arg_stack.push_back(eval_arg(arg));
            }
            push_frame(e.m_decl, old_size);
            r = eval_body(decl_fun_body(e.m_decl));
        }
        pop_frame(r, decl_type(e.m_decl));
        return r;
    }

    // closure stub
    object * stub_m(object ** args) {
        decl d(args[2]);
        size_t old_size = m_arg_stack.size();
        for (size_t i = 0; i < decl_params(d).size(); i++) {
            m_arg_stack.push_back(args[3 + i]);
        }
        push_frame(d, old_size);
        object * r = eval_body(decl_fun_body(d)).m_obj;
        pop_frame(r, type::TObject);
        return r;
    }

    // static closure stub
    static object * stub_m_aux(object ** args) {
        environment env(args[0]);
        options opts(args[1]);
        return with_interpreter<object *>(env, opts, decl_fun_id(TO_REF(decl, args[2])), [&](interpreter & interp) {
            return interp.stub_m(args);
        });
    }

    // python3 -c 'for i in range(1,17): print(f"    static object * stub_{i}_aux(" + ", ".join([f"object * x_{j}" for j in range(1,i+1)]) + ") { object * args[] = { " + ", ".join([f"x_{j}" for j in range(1,i+1)]) + " }; return interpreter::stub_m_aux(args); }")'
    static object * stub_1_aux(object * x_1) { object * args[] = { x_1 }; return interpreter::stub_m_aux(args); }
    static object * stub_2_aux(object * x_1, object * x_2) { object * args[] = { x_1, x_2 }; return interpreter::stub_m_aux(args); }
    static object * stub_3_aux(object * x_1, object * x_2, object * x_3) { object * args[] = { x_1, x_2, x_3 }; return interpreter::stub_m_aux(args); }
    static object * stub_4_aux(object * x_1, object * x_2, object * x_3, object * x_4) { object * args[] = { x_1, x_2, x_3, x_4 }; return interpreter::stub_m_aux(args); }
    static object * stub_5_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5) { object * args[] = { x_1, x_2, x_3, x_4, x_5 }; return interpreter::stub_m_aux(args); }
    static object * stub_6_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6 }; return interpreter::stub_m_aux(args); }
    static object * stub_7_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7 }; return interpreter::stub_m_aux(args); }
    static object * stub_8_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8 }; return interpreter::stub_m_aux(args); }
    static object * stub_9_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9 }; return interpreter::stub_m_aux(args); }
    static object * stub_10_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9, object * x_10) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10 }; return interpreter::stub_m_aux(args); }
    static object * stub_11_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9, object * x_10, object * x_11) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11 }; return interpreter::stub_m_aux(args); }
    static object * stub_12_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9, object * x_10, object * x_11, object * x_12) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12 }; return interpreter::stub_m_aux(args); }
    static object * stub_13_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9, object * x_10, object * x_11, object * x_12, object * x_13) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13 }; return interpreter::stub_m_aux(args); }
    static object * stub_14_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9, object * x_10, object * x_11, object * x_12, object * x_13, object * x_14) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14 }; return interpreter::stub_m_aux(args); }
    static object * stub_15_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9, object * x_10, object * x_11, object * x_12, object * x_13, object * x_14, object * x_15) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15 }; return interpreter::stub_m_aux(args); }
    static object * stub_16_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9, object * x_10, object * x_11, object * x_12, object * x_13, object * x_14, object * x_15, object * x_16) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16 }; return interpreter::stub_m_aux(args); }

    void * get_stub(unsigned params) {
        switch (params) {
            case 0: lean_unreachable();
            case 1: return reinterpret_cast<void *>(stub_1_aux);
            case 2: return reinterpret_cast<void *>(stub_2_aux);
            case 3: return reinterpret_cast<void *>(stub_3_aux);
            case 4: return reinterpret_cast<void *>(stub_4_aux);
            case 5: return reinterpret_cast<void *>(stub_5_aux);
            case 6: return reinterpret_cast<void *>(stub_6_aux);
            case 7: return reinterpret_cast<void *>(stub_7_aux);
            case 8: return reinterpret_cast<void *>(stub_8_aux);
            case 9: return reinterpret_cast<void *>(stub_9_aux);
            case 10: return reinterpret_cast<void *>(stub_10_aux);
            case 11: return reinterpret_cast<void *>(stub_11_aux);
            case 12: return reinterpret_cast<void *>(stub_12_aux);
            case 13: return reinterpret_cast<void *>(stub_13_aux);
            case 14: return reinterpret_cast<void *>(stub_14_aux);
            case 15: return reinterpret_cast<void *>(stub_15_aux);
            case 16: return reinterpret_cast<void *>(stub_16_aux);
            default: return reinterpret_cast<void *>(stub_m_aux);
        }
    }
public:
    explicit interpreter(environment const & env, options const & opts) : m_env(env), m_opts(opts) {
        m_prefer_native = opts.get_bool(*g_interpreter_prefer_native, LEAN_DEFAULT_INTERPRETER_PREFER_NATIVE);
    }

    ~interpreter() {
        for_each(m_constant_cache, [](name const &, constant_cache_entry const & e) {
            if (!e.m_is_scalar) {
                dec(e.m_val.m_obj);
            }
        });
    }

    /** A variant of `call` designed for external uses.
     *  * takes (owned) `object *`s instead of `arg`s.
     *  * supports under- and over-application.
     *  * supports "calling" (evaluating) nullary constants. */
    object * call_boxed(name const & fn, unsigned n, object ** args) {
        symbol_cache_entry e = lookup_symbol(fn);
        unsigned arity = decl_params(e.m_decl).size();
        object * r;
        if (arity == 0) {
            r = box_t(load(fn, decl_type(e.m_decl)), decl_type(e.m_decl));
        } else {
            // First allocate a closure with zero fixed parameters. This is slightly wasteful in the under-application
            // case, but simpler to handle.
            if (e.m_addr) {
                // `lookup_symbol` always prefers the boxed version for compiled functions, so nothing to do here
                r = alloc_closure(e.m_addr, arity, 0);
            } else {
                // `lookup_symbol` does not prefer the boxed version for interpreted functions, so check manually.
                decl d = e.m_decl;
                if (option_ref<decl> d_boxed = find_ir_decl(m_env, fn + *g_boxed_suffix)) {
                    d = *d_boxed.get();
                }
                r = mk_stub_closure(d, 0, nullptr);
            }
        }
        if (n > 0) {
            r = apply_n(r, n, args);
        }
        return r;
    }

    uint32 run_main(int argc, char * argv[]) {
        decl d = get_decl("main");
        array_ref<param> const & params = decl_params(d);
        buffer<object *> args;
        if (params.size() == 2) { // List String -> IO _
            lean_object * in = lean_box(0);
            int i = argc;
            while (i > 0) {
                i--;
                lean_object * n = lean_alloc_ctor(1, 2, 0);
                lean_ctor_set(n, 0, lean_mk_string(argv[i]));
                lean_ctor_set(n, 1, in);
                in = n;
            }
            args.push_back(in);
        } else { // IO _
            lean_assert(params.size() == 1);
        }
        object * w = io_mk_world();
        args.push_back(w);
        w = call_boxed("main", args.size(), &args[0]);
        if (io_result_is_ok(w)) {
            int ret = 0;
            lean::expr ret_ty = m_env.get("main").get_type();
            if (is_arrow(ret_ty)) {
                ret_ty = binding_body(ret_ty);
            }
            // `IO UInt32` or `IO (P)Unit`
            if (is_const(app_arg(ret_ty), get_uint32_name())) {
                ret = unbox_uint32(io_result_get_value(w));
            }
            dec_ref(w);
            return ret;
        } else {
            io_result_show_error(w);
            dec_ref(w);
            return 1;
        }
    }

    object * run_init(name const & decl, name const & init_decl) {
        try {
            object * args[] = { io_mk_world() };
            object * r = call_boxed(init_decl, 1, args);
            if (io_result_is_ok(r)) {
                object * o = io_result_get_value(r);
                mark_persistent(o);
                dec_ref(r);
                symbol_cache_entry e = lookup_symbol(decl);
                if (e.m_addr) {
                    *((object **)e.m_addr) = o;
                } else {
                    g_init_globals->insert(decl, o);
                }
                return lean_io_result_mk_ok(box(0));
            } else {
                return r;
            }
        } catch (exception & ex) {
            return io_result_mk_error(ex.what());
        }
    }
};

extern "C" object * lean_decl_get_sorry_dep(object * env, object * n);

optional<name> get_sorry_dep(environment const & env, name const & n) {
    return option_ref<name>(lean_decl_get_sorry_dep(env.to_obj_arg(), n.to_obj_arg())).get();
}

object * run_boxed(environment const & env, options const & opts, name const & fn, unsigned n, object **args) {
    if (optional<name> decl_with_sorry = get_sorry_dep(env, fn)) {
        throw exception(sstream() << "cannot evaluate code because '" << *decl_with_sorry
            << "' uses 'sorry' and/or contains errors");
    }
    return interpreter::with_interpreter<object *>(env, opts, fn, [&](interpreter & interp) { return interp.call_boxed(fn, n, args); });
}
uint32 run_main(environment const & env, options const & opts, int argv, char * argc[]) {
    return interpreter::with_interpreter<uint32>(env, opts, "main", [&](interpreter & interp) { return interp.run_main(argv, argc); });
}

extern "C" LEAN_EXPORT object * lean_eval_const(object * env, object * opts, object * c) {
    try {
        return mk_cnstr(1, run_boxed(TO_REF(environment, env), TO_REF(options, opts), TO_REF(name, c), 0, 0)).steal();
    } catch (exception & ex) {
        return mk_cnstr(0, string_ref(ex.what())).steal();
    }
}

/* mkModuleInitializationFunctionName (moduleName : Name) : String */
extern "C" obj_res lean_mk_module_initialization_function_name(obj_arg);

extern "C" LEAN_EXPORT object * lean_run_mod_init(object * mod, object *) {
    string_ref mangled = string_ref(lean_mk_module_initialization_function_name(mod));
    if (void * init = lookup_symbol_in_cur_exe(mangled.data())) {
        auto init_fn = reinterpret_cast<object *(*)(uint8_t, object *)>(init);
        uint8_t builtin = 0;
        object * r = init_fn(builtin, io_mk_world());
        if (io_result_is_ok(r)) {
            dec_ref(r);
            return lean_io_result_mk_ok(box(true));
        } else {
            return r;
        }
    } else {
        return lean_io_result_mk_ok(box(false));
    }
}

extern "C" LEAN_EXPORT object * lean_run_init(object * env, object * opts, object * decl, object * init_decl, object *) {
    return interpreter::with_interpreter<object *>(TO_REF(environment, env), TO_REF(options, opts), TO_REF(name, decl), [&](interpreter & interp) {
        return interp.run_init(TO_REF(name, decl), TO_REF(name, init_decl));
    });
}
}

void initialize_ir_interpreter() {
    ir::g_mangle_prefix = new string_ref("l_");
    mark_persistent(ir::g_mangle_prefix->raw());
    ir::g_boxed_suffix = new string_ref("_boxed");
    mark_persistent(ir::g_boxed_suffix->raw());
    ir::g_boxed_mangled_suffix = new string_ref("___boxed");
    mark_persistent(ir::g_boxed_mangled_suffix->raw());
    ir::g_interpreter_prefer_native = new name({"interpreter", "prefer_native"});
    ir::g_init_globals = new name_map<object *>();
    register_bool_option(*ir::g_interpreter_prefer_native, LEAN_DEFAULT_INTERPRETER_PREFER_NATIVE, "(interpreter) whether to use precompiled code where available");
    DEBUG_CODE({
        register_trace_class({"interpreter"});
        register_trace_class({"interpreter", "call"});
        register_trace_class({"interpreter", "step"});
    });
}

void finalize_ir_interpreter() {
    delete ir::g_init_globals;
    delete ir::g_interpreter_prefer_native;
    delete ir::g_boxed_mangled_suffix;
    delete ir::g_boxed_suffix;
    delete ir::g_mangle_prefix;
}
}
