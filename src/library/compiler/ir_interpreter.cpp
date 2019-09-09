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

The interpreter mainly consists of a homogeneous stack of boxed `object *` values. IR variables are mapped to stack
slots by adding the current base pointer to the variable index. Further stacks are used for storing join points and call
stack metadata. The interpreted IR is taken directly from the environment. Whenever possible, we try to switch to native
code by checking for the mangled symbol via dlsym/GetProcAddress, which is also how we can call external functions (but
only if the file declaring them has already been compiled). We always call the "boxed" versions of native functions,
which have a (relatively) homogeneous ABI that we can use without runtime code generation; see also `call/lookup_symbol`
below.

*/
#include <string>
#include <vector>
#ifdef LEAN_WINDOWS
#include <windows.h>
#else
#include <dlfcn.h>
#endif
#include "runtime/flet.h"
#include "runtime/apply.h"
#include "library/trace.h"
#include "library/compiler/ir.h"
#include "util/option_ref.h"
#include "util/array_ref.h"
#include "util/nat.h"

namespace lean {
namespace ir {
// C++ wrappers of Lean data types

typedef object_ref lit_val;
typedef object_ref ctor_info;

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
nat const & expr_sproj_idx(expr const & e) { lean_assert(expr_tag(e) == expr_kind::SProj); return cnstr_get_ref_t<nat>(e, 0); }
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
nat const & fn_body_sset_idx(fn_body const & b) { lean_assert(fn_body_tag(b) == fn_body_kind::SSet); return cnstr_get_ref_t<nat>(b, 1); }
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

// reuse the compiler's name mangling to compute native symbol names
extern "C" object * lean_name_mangle(object * n, object * pre);
string_ref name_mangle(name const & n, string_ref const & pre) {
    return string_ref(lean_name_mangle(n.to_obj_arg(), pre.to_obj_arg()));
}

extern "C" object * lean_ir_format_fn_body_head(object * b);
format format_fn_body_head(fn_body const & b) {
    return format(lean_ir_format_fn_body_head(b.to_obj_arg()));
}

/** \pre Very simple debug output of arbitrary objects, should be extended. */
void print_object(io_state_stream const & ios, object * o) {
    if (is_scalar(o)) {
        ios << unbox(o);
    } else if (o == nullptr) {
        ios << "0x0"; // confusingly printed as "0" by the default operator<<
    } else {
        // merely following the trace of object addresses is surprisingly helpful for debugging
        ios.get_stream() << o;
    }
}

void * lookup_symbol_in_cur_exe(char const * sym) {
#ifdef LEAN_WINDOWS
    return reinterpret_cast<void *>(GetProcAddress(GetModuleHandle(nullptr), sym));
#else
    return dlsym(RTLD_DEFAULT, sym);
#endif
}

class interpreter;
LEAN_THREAD_PTR(interpreter, g_interpreter);

class interpreter {
    // stack of IR variable slots
    std::vector<object *> m_arg_stack;
    // stack of join points
    std::vector<fn_body const *> m_jp_stack;
    struct frame {
        name m_fn;
        // base pointers into the stack above
        size_t m_arg_bp;
        size_t m_jp_bp;
    };
    std::vector<frame> m_call_stack;
    environment const & m_env;
    // caches values of nullary functions ("constants")
    name_map<object_ref> m_constant_cache;
    struct symbol_cache_entry {
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
    inline object * & var(var_id const & v) {
        // variables are 1-indexed
        size_t i = get_frame().m_arg_bp + v.get_small_value() - 1;
        // we don't know the frame size (unless we do an additional IR pass), so we extend it dynamically
        if (i >= m_arg_stack.size()) {
            m_arg_stack.resize(i + 1);
        }
        return m_arg_stack[i];
    }

    object * eval_arg(arg const & a) {
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
                cnstr_set(o, i, eval_arg(args[i]));
            }
            return o;
        }
    }

    object * eval_expr(expr const & e, type t) {
        switch (expr_tag(e)) {
            case expr_kind::Ctor:
                return alloc_ctor(expr_ctor_info(e), expr_ctor_args(e));
            case expr_kind::Reset: { // release fields if unique reference in preparation for `Reuse` below
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
            case expr_kind::Reuse: { // reuse dead allocation if possible
                object * o = var(expr_reuse_obj(e));
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
                        cnstr_set(o, i, eval_arg(expr_reuse_args(e)[i]));
                    }
                    return o;
                }
            }
            case expr_kind::Proj: // object field access
                return cnstr_get(var(expr_proj_obj(e)), expr_proj_idx(e).get_small_value());
            case expr_kind::UProj: // USize field access
                return box_size_t(cnstr_get_usize(var(expr_uproj_obj(e)), expr_uproj_idx(e).get_small_value()));
            case expr_kind::SProj: { // other unboxed field access
                size_t offset = expr_sproj_idx(e).get_small_value() * sizeof(void *) +
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
            case expr_kind::FAp: { // satured ("full") application of top-level function
                if (expr_fap_args(e).size()) {
                    return call(expr_fap_fun(e), expr_fap_args(e));
                } else {
                    // nullary function ("constant")
                    return load(expr_fap_fun(e), t);
                }
            }
            case expr_kind::PAp: { // unsatured (partial) application of top-level function
                decl d = get_fdecl(expr_pap_fun(e));
                unsigned i = 0;
                object * cls;
                if (void * p = lookup_symbol(expr_pap_fun(e)).m_addr) {
                    // point closure directly to native symbol
                    cls = alloc_closure(p, decl_params(d).size(), expr_pap_args(e).size());
                } else {
                    // point closure to interpreter stub taking interpreter data, declaration to be called, and partially
                    // applied arguments
                    // HACK: filling up closure to at least 16 arguments
                    // Boxed functions of arity >= 16 use a single common signature, so we only need a single stub.
                    cls = alloc_closure(reinterpret_cast<void *>(stub_m_aux), 16 + decl_params(d).size(), 16 + expr_pap_args(e).size());
                    closure_set(cls, i++, m_env.to_obj_arg());
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
            case expr_kind::Ap: { // (saturated or unsatured) application of closure; mostly handled by runtime
                size_t old_size = m_arg_stack.size();
                // optimization: use unused part of stack for temporarily storing evaluated arguments
                for (const auto & arg : expr_ap_args(e)) {
                    m_arg_stack.push_back(eval_arg(arg));
                }
                object * r = apply_n(var(expr_ap_fun(e)), expr_ap_args(e).size(), &m_arg_stack[old_size]);
                m_arg_stack.resize(old_size);
                return r;
            }
            case expr_kind::Box: // box unboxed value; no-op in interpreter
                return var(expr_box_obj(e));
            case expr_kind::Unbox: // unbox boxed value; no-op in interpreter
                return var(expr_unbox_obj(e));
            case expr_kind::Lit: // load numeric or string literal
                switch (lit_val_tag(expr_lit_val(e))) {
                    case lit_val_kind::Num: {
                        nat const & n = lit_val_num(expr_lit_val(e));
                        switch (t) {
                            case type::Float: throw exception("floats are not supported yet");
                            case type::UInt8: return n.raw();
                            case type::UInt16: return n.raw();
                            // the following types might *not* use the same boxed representation as `nat`, so unbox and
                            // re-box
                            case type::UInt32: return box_uint32(n.get_small_value());
                            case type::UInt64: return box_uint64(n.get_small_value());
                            case type::USize: return box_size_t(n.get_small_value());
                            // `nat` literal
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
                        b = decl_fun_body(get_decl(expr_fap_fun(e)));
                        break;
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
                    object * o = var(fn_body_set_var(b));
                    lean_assert(is_exclusive(o));
                    cnstr_set(o, fn_body_set_idx(b).get_small_value(), eval_arg(fn_body_set_arg(b)));
                    b = fn_body_set_cont(b);
                    break;
                }
                case fn_body_kind::SetTag: { // set constructor tag of unique reference
                    object * o = var(fn_body_set_tag_var(b));
                    lean_assert(is_exclusive(o));
                    cnstr_set_tag(o, fn_body_set_tag_cidx(b).get_small_value());
                    b = fn_body_set_tag_cont(b);
                    break;
                }
                case fn_body_kind::USet: { // set USize field of unique reference
                    object * o = var(fn_body_uset_var(b));
                    lean_assert(is_exclusive(o));
                    cnstr_set_usize(o, fn_body_uset_idx(b).get_small_value(), unbox_size_t(eval_arg(fn_body_uset_arg(b))));
                    b = fn_body_uset_cont(b);
                    break;
                }
                case fn_body_kind::SSet: { // set other unboxed field of unique reference
                    object * o = var(fn_body_sset_target(b));
                    size_t offset = fn_body_sset_idx(b).get_small_value() * sizeof(void *) +
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
                case fn_body_kind::Inc: // increment reference counter
                    inc(var(fn_body_inc_var(b)), fn_body_inc_val(b).get_small_value());
                    b = fn_body_inc_cont(b);
                    break;
                case fn_body_kind::Dec: { // decrement reference counter
                    size_t n = fn_body_dec_val(b).get_small_value();
                    for (size_t i = 0; i < n; i++) {
                        dec(var(fn_body_dec_var(b)));
                    }
                    b = fn_body_dec_cont(b);
                    break;
                }
                case fn_body_kind::Del: // delete object of unique reference
                    lean_free_object(var(fn_body_del_var(b)));
                    b = fn_body_del_cont(b);
                    break;
                case fn_body_kind::MData: // metadata; no-op
                    b = fn_body_mdata_cont(b);
                    break;
                case fn_body_kind::Case: { // branch according to constructor tag
                    object * o = var(fn_body_case_var(b));
                    size_t tag = is_scalar(o) ? unbox(o) : cnstr_tag(o);
                    for (alt_core const & a : fn_body_case_alts(b)) {
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

    /** \brief Return cached lookup result for given unmangled function name in the current binary. */
    symbol_cache_entry lookup_symbol(name const & fn) {
        if (symbol_cache_entry const * e = m_symbol_cache.find(fn)) {
            return *e;
        } else {
            string_ref mangled = name_mangle(fn, *g_mangle_prefix);
            string_ref boxed_mangled(string_append(mangled.to_obj_arg(), g_boxed_mangled_suffix->raw()));
            symbol_cache_entry e_new;
            // check for boxed version first
            if (void *p_boxed = lookup_symbol_in_cur_exe(boxed_mangled.data())) {
                e_new = symbol_cache_entry { p_boxed, true };
            } else if (void *p = lookup_symbol_in_cur_exe(mangled.data())) {
                // if there is no boxed version, there are no unboxed parameters, so use default version
                e_new = symbol_cache_entry { p, false };
            } else {
                e_new = symbol_cache_entry { nullptr, false };
            }
            m_symbol_cache.insert(fn, e_new);
            return e_new;
        }
    }

    /** \brief Retrieve Lean declaration from environment. */
    decl get_decl(name const & fn) {
        option_ref<decl> d = find_env_decl(m_env, fn);
        if (!d) {
            throw exception(sstream() << "unknown declaration '" << fn << "'");
        }
        return d.get().value();
    }

    /** \brief Retrieve Lean definition from environment. */
    decl get_fdecl(name const & fn) {
        decl d = get_decl(fn);
        if (decl_tag(d) == decl_kind::Extern) {
            throw exception(sstream() << "unexpected external declaration '" << fn << "'");
        }
        return d;
    }

    /** \brief Evaluate nullary function ("constant"). */
    object * load(name const & fn, type t) {
        object_ref const * cached = m_constant_cache.find(fn);
        if (cached) {
            return cached->to_obj_arg();
        }

        object * r;
        if (void * p = lookup_symbol(fn).m_addr) {
            // constants do not have boxed wrappers, but we'll survive
            switch (t) {
                case type::Float: throw exception("floats are not supported yet");
                case type::UInt8: r = box(*static_cast<uint8 *>(p)); break;
                case type::UInt16: r = box(*static_cast<uint16 *>(p)); break;
                case type::UInt32: r = box_uint32(*static_cast<uint32 *>(p)); break;
                case type::UInt64: r = box_uint64(*static_cast<uint64 *>(p)); break;
                case type::USize: r = box_size_t(*static_cast<size_t *>(p)); break;
                case type::Object:
                case type::TObject:
                    r = *static_cast<object **>(p);
                    break;
                default:
                    throw exception("invalid type");
            }
        } else {
            push_frame(fn, m_arg_stack.size());
            decl d = get_fdecl(fn);
            r = eval_body(decl_fun_body(d));
            pop_frame(r);
        }
        m_constant_cache.insert(fn, object_ref(r, true));
        return r;
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
        symbol_cache_entry e = lookup_symbol(fn);
        if (e.m_addr) {
            if (e.m_boxed) {
                // NOTE: If we chose the boxed version where the IR chose the unboxed one, we need to manually increment
                // originally borrowed parameters because the wrapper will decrement these after the call.
                // Basically the wrapper is more homogeneous (removing both boxed and borrowed parameters) than we
                // would need in this instance.
                for (size_t i = 0; i < args.size(); i++) {
                    if (param_borrow(decl_params(d)[i])) {
                        inc(m_arg_stack[old_size + i]);
                    }
                }
            }
            r = curry(e.m_addr, args.size(), &m_arg_stack[old_size]);
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
    explicit interpreter(environment const & env) : m_env(env) {
        lean_assert(g_interpreter == nullptr);
        g_interpreter = this;
    }
    ~interpreter() {
        lean_assert(g_interpreter == this);
        g_interpreter = nullptr;
    }

    uint32 run_main(int argc, char * argv[]) {
        decl d = get_fdecl("main");
        array_ref<param> const & params = decl_params(d);
        if (params.size() == 2) { // List String -> IO UInt32
            lean_object * in = lean_box(0);
            int i = argc;
            while (i > 0) {
                i--;
                lean_object * n = lean_alloc_ctor(1, 2, 0);
                lean_ctor_set(n, 0, lean_mk_string(argv[i]));
                lean_ctor_set(n, 1, in);
                in = n;
            }
            m_arg_stack.push_back(in);
        } else { // IO UInt32
            lean_assert(params.size() == 1);
        }
        object * w = io_mk_world();
        m_arg_stack.push_back(w);
        push_frame("main", 0);
        w = eval_body(decl_fun_body(d));
        pop_frame(w);
        if (io_result_is_ok(w)) {
            // NOTE: in an awesome hack, `IO Unit` works just as well because `pure 0` and `pure ()` use the same
            // representation
            int ret = unbox(io_result_get_value(w));
            dec_ref(w);
            return ret;
        } else {
            io_result_show_error(w);
            dec_ref(w);
            return 1;
        }
    }

    // closure stub
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

    // closure stub stub
    static object * stub_m_aux(object ** args) {
        environment env(args[0]);
        if (g_interpreter) {
            return g_interpreter->stub_m(args);
        } else {
            // We changed threads or the closure was stored and called after the original interpreter exited.
            // Create new interpreter with new stacks.
            return interpreter(env).stub_m(args);
        }
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
