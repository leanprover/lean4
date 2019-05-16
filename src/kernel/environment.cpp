/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include <limits>
#include "runtime/sstream.h"
#include "runtime/thread.h"
#include "util/map_foreach.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "kernel/type_checker.h"
#include "kernel/quot.h"

namespace lean {
object* environment_add_core(object*, object*);
object* mk_empty_environment_core(uint32, object*);
object* environment_find_core(object*, object*);
uint32 environment_trust_level_core(object*);
object* environment_mark_quot_init_core(object*);
uint8 environment_quot_init_core(object*);
object* register_extension_core(object*);
object* get_extension_core(object*, object*);
object* set_extension_core(object*, object*, object*);
object* environment_switch_core(object*);

object* mk_empty_environment(uint32 trust_lvl) {
    object* r = mk_empty_environment_core(trust_lvl, io_mk_world());
    if (io_result_is_error(r)) { dec(r); throw exception("error creating empty environment"); }
    object* env = io_result_get_value(r);
    inc(env);
    dec(r);
    return env;
}

environment::environment(unsigned trust_lvl):
    // TODO(Leo): do not eagerly switch
    object_ref(environment_switch_core(mk_empty_environment(trust_lvl))) {
}

unsigned environment::trust_lvl() const {
    return environment_trust_level_core(to_obj_arg());
}

bool environment::is_quot_initialized() const {
    return environment_quot_init_core(to_obj_arg()) != 0;
}

void environment::mark_quot_initialized() {
    m_obj = environment_mark_quot_init_core(m_obj);
}

optional<constant_info> environment::find(name const & n) const {
    return to_optional<constant_info>(environment_find_core(to_obj_arg(), n.to_obj_arg()));
}

constant_info environment::get(name const & n) const {
    object * o = environment_find_core(to_obj_arg(), n.to_obj_arg());
    if (is_scalar(o))
        throw unknown_constant_exception(*this, n);
    constant_info r(cnstr_get(o, 0), true);
    dec(o);
    return r;
}

static void check_no_metavar(environment const & env, name const & n, expr const & e) {
    if (has_metavar(e))
        throw declaration_has_metavars_exception(env, n, e);
}

static void check_no_fvar(environment const & env, name const & n, expr const & e) {
    if (has_fvar(e))
        throw declaration_has_free_vars_exception(env, n, e);
}

void check_no_metavar_no_fvar(environment const & env, name const & n, expr const & e) {
    check_no_metavar(env, n, e);
    check_no_fvar(env, n, e);
}

static void check_name(environment const & env, name const & n) {
    if (env.find(n))
        throw already_declared_exception(env, n);
}

void environment::check_name(name const & n) const {
    ::lean::check_name(*this, n);
}

static void check_duplicated_univ_params(environment const & env, names ls) {
    while (!is_nil(ls)) {
        auto const & p = head(ls);
        ls = tail(ls);
        if (std::find(ls.begin(), ls.end(), p) != ls.end()) {
            throw kernel_exception(env, sstream() << "failed to add declaration to environment, "
                                   << "duplicate universe level parameter: '"
                                   << p << "'");
        }
    }
}

void environment::check_duplicated_univ_params(names ls) const {
    ::lean::check_duplicated_univ_params(*this, ls);
}

static void check_constant_val(environment const & env, constant_val const & v, type_checker & checker) {
    check_name(env, v.get_name());
    check_duplicated_univ_params(env, v.get_lparams());
    check_no_metavar_no_fvar(env, v.get_name(), v.get_type());
    expr sort = checker.check(v.get_type(), v.get_lparams());
    checker.ensure_sort(sort, v.get_type());
}

static void check_constant_val(environment const & env, constant_val const & v, bool safe_only) {
    type_checker checker(env, safe_only);
    check_constant_val(env, v, checker);
}

void environment::add_core(constant_info const & info) {
    m_obj = environment_add_core(m_obj, info.to_obj_arg());
}

environment environment::add(constant_info const & info) const {
    return environment(environment_add_core(to_obj_arg(), info.to_obj_arg()));
}

environment environment::add_axiom(declaration const & d, bool check) const {
    axiom_val const & v = d.to_axiom_val();
    if (check)
        check_constant_val(*this, v.to_constant_val(), !d.is_unsafe());
    return add(constant_info(d));
}

environment environment::add_definition(declaration const & d, bool check) const {
    definition_val const & v = d.to_definition_val();
    if (v.is_unsafe()) {
        /* Meta definition can be recursive.
           So, we check the header, add, and then type check the body. */
        if (check) {
            bool safe_only = false;
            type_checker checker(*this, safe_only);
            check_constant_val(*this, v.to_constant_val(), checker);
        }
        environment new_env = add(constant_info(d));
        if (check) {
            bool safe_only = false;
            type_checker checker(new_env, safe_only);
            expr val_type = checker.check(v.get_value(), v.get_lparams());
            if (!checker.is_def_eq(val_type, v.get_type()))
                throw definition_type_mismatch_exception(new_env, d, val_type);
        }
        return new_env;
    } else {
        if (check) {
            type_checker checker(*this);
            check_constant_val(*this, v.to_constant_val(), checker);
            expr val_type = checker.check(v.get_value(), v.get_lparams());
            if (!checker.is_def_eq(val_type, v.get_type()))
                throw definition_type_mismatch_exception(*this, d, val_type);
        }
        return add(constant_info(d));
    }
}

environment environment::add_theorem(declaration const & d, bool check) const {
    theorem_val const & v = d.to_theorem_val();
    if (check) {
        // TODO(Leo): we must add support for handling tasks here
        type_checker checker(*this);
        check_constant_val(*this, v.to_constant_val(), checker);
        expr val_type = checker.check(v.get_value(), v.get_lparams());
        if (!checker.is_def_eq(val_type, v.get_type()))
            throw definition_type_mismatch_exception(*this, d, val_type);
    }
    return add(constant_info(d));
}

environment environment::add_opaque(declaration const & d, bool check) const {
    opaque_val const & v = d.to_opaque_val();
    if (check) {
        type_checker checker(*this);
        check_constant_val(*this, v.to_constant_val(), checker);
        expr val_type = checker.check(v.get_value(), v.get_lparams());
        if (!checker.is_def_eq(val_type, v.get_type()))
            throw definition_type_mismatch_exception(*this, d, val_type);
    }
    return add(constant_info(d));
}

environment environment::add_mutual(declaration const & d, bool check) const {
    definition_vals const & vs = d.to_definition_vals();
    /* Check declarations header */
    if (check) {
        bool safe_only = false;
        type_checker checker(*this, safe_only);
        for (definition_val const & v : vs) {
            if (!v.is_unsafe())
                throw kernel_exception(*this, "invalid mutual definition, declaration is not tagged as meta");
            check_constant_val(*this, v.to_constant_val(), checker);
        }
    }
    /* Add declarations */
    environment new_env = *this;
    for (definition_val const & v : vs) {
        new_env.add_core(constant_info(v));
    }
    /* Check actual definitions */
    if (check) {
        bool safe_only = false;
        type_checker checker(new_env, safe_only);
        for (definition_val const & v : vs) {
            expr val_type = checker.check(v.get_value(), v.get_lparams());
            if (!checker.is_def_eq(val_type, v.get_type()))
                throw definition_type_mismatch_exception(new_env, d, val_type);
        }
    }
    return new_env;
}

environment environment::add(declaration const & d, bool check) const {
    switch (d.kind()) {
    case declaration_kind::Axiom:            return add_axiom(d, check);
    case declaration_kind::Definition:       return add_definition(d, check);
    case declaration_kind::Theorem:          return add_theorem(d, check);
    case declaration_kind::Opaque:           return add_opaque(d, check);
    case declaration_kind::MutualDefinition: return add_mutual(d, check);
    case declaration_kind::Quot:             return add_quot();
    case declaration_kind::Inductive:        return add_inductive(d);
    }
    lean_unreachable();
}

static void env_ext_finalizer(void * ext) {
    delete static_cast<environment_extension*>(ext);
}

static void env_ext_foreach(void * /* ext */, b_obj_arg /* fn */) {
    /* The foreach combinator is used by `mark_mt` when marking values as "multi-threaded".
       Moreover, it is invoked even when we don't use threads because of global
       IO.Ref is considered to be "multi-threaded".

       So, we just ignore this issue for now.
       This is not critical since eventually all environment extensions will be implemented in Lean,
       and we will be able to delete this code.
    */
}

static external_object_class * g_env_ext_class = nullptr;

static environment_extension const & to_env_ext(b_obj_arg o) {
    lean_assert(external_class(o) == g_env_ext_class);
    return *static_cast<environment_extension *>(external_data(o));
}

static obj_res to_object(environment_extension * ext) {
    return alloc_external(g_env_ext_class, ext);
}

unsigned environment::register_extension(environment_extension * initial) {
    object * r = register_extension_core(to_object(initial));
    if (is_scalar(r)) { throw exception("error creating empty environment"); }
    unsigned idx = unbox(cnstr_get(r, 0));
    dec(r);
    return idx;
}

environment_extension const & environment::get_extension(unsigned id) const {
    object * r = get_extension_core(to_obj_arg(), box(id));
    if (is_scalar(r)) { throw exception("invalid extension id"); }
    object * ext = cnstr_get(r, 0);
    dec(r);
    return to_env_ext(ext);
}

environment environment::update(unsigned id, environment_extension * ext) const {
    object * r = set_extension_core(to_obj_arg(), box(id), to_object(ext));
    if (is_scalar(r)) { throw exception("invalid extension id"); }
    environment env(cnstr_get(r, 0), true);
    dec(r);
    return env;
}

void environment::for_each_constant(std::function<void(constant_info const & d)> const & f) const {
    smap_foreach(cnstr_get(raw(), 1), [&](object *, object * v) {
            constant_info cinfo(v, true);
            f(cinfo);
        });
}

obj_res display_stats_core(obj_arg env, obj_arg w);

void environment::display_stats() const {
    dec_ref(display_stats_core(to_obj_arg(), io_mk_world()));
}

void initialize_environment() {
    g_env_ext_class = register_external_object_class(env_ext_finalizer, env_ext_foreach);
}

void finalize_environment() {
}
}
