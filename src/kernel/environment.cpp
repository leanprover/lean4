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
#include "runtime/sharecommon.h"
#include "util/map_foreach.h"
#include "util/io.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "kernel/type_checker.h"
#include "kernel/quot.h"

namespace lean {
extern "C" object* lean_environment_add(object*, object*);
extern "C" object* lean_environment_find(object*, object*);
extern "C" object* lean_environment_mark_quot_init(object*);
extern "C" uint8 lean_environment_quot_init(object*);
extern "C" object* lean_kernel_record_unfold (object*, object*);
extern "C" object* lean_kernel_get_diag(object*);
extern "C" object* lean_kernel_set_diag(object*, object*);
extern "C" uint8* lean_kernel_diag_is_enabled(object*);

void diagnostics::record_unfold(name const & decl_name) {
    m_obj = lean_kernel_record_unfold(to_obj_arg(), decl_name.to_obj_arg());
}

scoped_diagnostics::scoped_diagnostics(environment const & env, bool collect) {
    if (collect) {
        diagnostics d(env.get_diag());
        if (lean_kernel_diag_is_enabled(d.to_obj_arg())) {
            m_diag = new diagnostics(d);
        } else
            m_diag = nullptr;
    } else {
        m_diag = nullptr;
    }
}

scoped_diagnostics::~scoped_diagnostics() {
    if (m_diag)
        delete m_diag;
}

environment scoped_diagnostics::update(environment const & env) const {
    if (m_diag)
        return env.set_diag(*m_diag);
    else
        return env;
}

diagnostics environment::get_diag() const {
    return diagnostics(lean_kernel_get_diag(to_obj_arg()));
}

environment environment::set_diag(diagnostics const & diag) const {
    return environment(lean_kernel_set_diag(to_obj_arg(), diag.to_obj_arg()));
}

bool environment::is_quot_initialized() const {
    return lean_environment_quot_init(to_obj_arg()) != 0;
}

void environment::mark_quot_initialized() {
    m_obj = lean_environment_mark_quot_init(m_obj);
}

optional<constant_info> environment::find(name const & n) const {
    return to_optional<constant_info>(lean_environment_find(to_obj_arg(), n.to_obj_arg()));
}

constant_info environment::get(name const & n) const {
    object * o = lean_environment_find(to_obj_arg(), n.to_obj_arg());
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

static void check_constant_val(environment const & env, constant_val const & v, diagnostics * diag, definition_safety ds) {
    type_checker checker(env, diag, ds);
    check_constant_val(env, v, checker);
}

static void check_constant_val(environment const & env, constant_val const & v, diagnostics * diag, bool safe_only) {
    check_constant_val(env, v, diag, safe_only ? definition_safety::safe : definition_safety::unsafe);
}

void environment::add_core(constant_info const & info) {
    m_obj = lean_environment_add(m_obj, info.to_obj_arg());
}

environment environment::add(constant_info const & info) const {
    return environment(lean_environment_add(to_obj_arg(), info.to_obj_arg()));
}

environment environment::add_axiom(declaration const & d, bool check) const {
    scoped_diagnostics diag(*this, check);
    axiom_val const & v = d.to_axiom_val();
    if (check)
        check_constant_val(*this, v.to_constant_val(), diag.get(), !d.is_unsafe());
    return diag.update(add(constant_info(d)));
}

environment environment::add_definition(declaration const & d, bool check) const {
    scoped_diagnostics diag(*this, check);
    definition_val const & v = d.to_definition_val();
    if (v.is_unsafe()) {
        /* Meta definition can be recursive.
           So, we check the header, add, and then type check the body. */
        if (check) {
            type_checker checker(*this, diag.get(), definition_safety::unsafe);
            check_constant_val(*this, v.to_constant_val(), checker);
        }
        environment new_env = add(constant_info(d));
        if (check) {
            type_checker checker(new_env, diag.get(), definition_safety::unsafe);
            check_no_metavar_no_fvar(new_env, v.get_name(), v.get_value());
            expr val_type = checker.check(v.get_value(), v.get_lparams());
            if (!checker.is_def_eq(val_type, v.get_type()))
                throw definition_type_mismatch_exception(new_env, d, val_type);
        }
        return diag.update(new_env);
    } else {
        if (check) {
            type_checker checker(*this, diag.get());
            check_constant_val(*this, v.to_constant_val(), checker);
            check_no_metavar_no_fvar(*this, v.get_name(), v.get_value());
            expr val_type = checker.check(v.get_value(), v.get_lparams());
            if (!checker.is_def_eq(val_type, v.get_type()))
                throw definition_type_mismatch_exception(*this, d, val_type);
        }
        return diag.update(add(constant_info(d)));
    }
}

environment environment::add_theorem(declaration const & d, bool check) const {
    scoped_diagnostics diag(*this, check);
    theorem_val const & v = d.to_theorem_val();
    if (check) {
        type_checker checker(*this, diag.get());
        sharecommon_persistent_fn share;
        expr val(share(v.get_value().raw()));
        expr type(share(v.get_type().raw()));
        if (!checker.is_prop(type))
            throw theorem_type_is_not_prop(*this, v.get_name(), type);
        check_constant_val(*this, v.to_constant_val(), checker);
        check_no_metavar_no_fvar(*this, v.get_name(), val);
        expr val_type = checker.check(val, v.get_lparams());
        if (!checker.is_def_eq(val_type, type))
            throw definition_type_mismatch_exception(*this, d, val_type);
    }
    return diag.update(add(constant_info(d)));
}

environment environment::add_opaque(declaration const & d, bool check) const {
    scoped_diagnostics diag(*this, check);
    opaque_val const & v = d.to_opaque_val();
    if (check) {
        type_checker checker(*this, diag.get());
        check_constant_val(*this, v.to_constant_val(), checker);
        expr val_type = checker.check(v.get_value(), v.get_lparams());
        if (!checker.is_def_eq(val_type, v.get_type()))
            throw definition_type_mismatch_exception(*this, d, val_type);
    }
    return diag.update(add(constant_info(d)));
}

environment environment::add_mutual(declaration const & d, bool check) const {
    scoped_diagnostics diag(*this, check);
    definition_vals const & vs = d.to_definition_vals();
    if (empty(vs))
        throw kernel_exception(*this, "invalid empty mutual definition");
    definition_safety safety = head(vs).get_safety();
    if (safety == definition_safety::safe)
        throw kernel_exception(*this, "invalid mutual definition, declaration is not tagged as unsafe/partial");
    /* Check declarations header */
    if (check) {
        type_checker checker(*this, diag.get(), safety);
        for (definition_val const & v : vs) {
            if (v.get_safety() != safety)
                throw kernel_exception(*this, "invalid mutual definition, declarations must have the same safety annotation");
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
        type_checker checker(new_env, diag.get(), safety);
        for (definition_val const & v : vs) {
            check_no_metavar_no_fvar(new_env, v.get_name(), v.get_value());
            expr val_type = checker.check(v.get_value(), v.get_lparams());
            if (!checker.is_def_eq(val_type, v.get_type()))
                throw definition_type_mismatch_exception(new_env, d, val_type);
        }
    }
    return diag.update(new_env);
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
/*
addDeclCore (env : Environment) (maxHeartbeats : USize) (decl : @& Declaration)
  (cancelTk? : @& Option IO.CancelToken) : Except Kernel.Exception Environment
*/
extern "C" LEAN_EXPORT object * lean_add_decl(object * env, size_t max_heartbeat, object * decl,
    object * opt_cancel_tk) {
    scope_max_heartbeat s(max_heartbeat);
    scope_cancel_tk s2(is_scalar(opt_cancel_tk) ? nullptr : cnstr_get(opt_cancel_tk, 0));
    return catch_kernel_exceptions<environment>([&]() {
            return environment(env).add(declaration(decl, true));
        });
}

extern "C" LEAN_EXPORT object * lean_add_decl_without_checking(object * env, object * decl) {
    return catch_kernel_exceptions<environment>([&]() {
            return environment(env).add(declaration(decl, true), false);
        });
}

void environment::for_each_constant(std::function<void(constant_info const & d)> const & f) const {
    smap_foreach(cnstr_get(raw(), 1), [&](object *, object * v) {
            constant_info cinfo(v, true);
            f(cinfo);
        });
}

void initialize_environment() {
}

void finalize_environment() {
}
}
