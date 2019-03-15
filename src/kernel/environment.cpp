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
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "kernel/type_checker.h"
#include "kernel/quot.h"

namespace lean {
environment_extension::~environment_extension() {}

optional<constant_info> environment::find(name const & n) const {
    constant_info const * r = m_constants.find(n);
    return r ? some_constant_info(*r) : none_constant_info();
}

constant_info environment::get(name const & n) const {
    constant_info const * r = m_constants.find(n);
    if (!r)
        throw unknown_constant_exception(*this, n);
    return *r;
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
    case declaration_kind::MutualDefinition: return add_mutual(d, check);
    case declaration_kind::Quot:             return add_quot();
    case declaration_kind::Inductive:        return add_inductive(d);
    }
    lean_unreachable();
}

class extension_manager {
    std::vector<std::shared_ptr<environment_extension const>> m_exts;
    mutex                                                     m_mutex;
public:
    unsigned register_extension(std::shared_ptr<environment_extension const> const & ext) {
        lock_guard<mutex> lock(m_mutex);
        unsigned r = m_exts.size();
        m_exts.push_back(ext);
        return r;
    }

    bool has_ext(unsigned extid) const { return extid < m_exts.size(); }

    environment_extension const & get_initial(unsigned extid) {
        lock_guard<mutex> lock(m_mutex);
        return *(m_exts[extid].get());
    }
};

static extension_manager * g_extension_manager = nullptr;
static extension_manager & get_extension_manager() {
    return *g_extension_manager;
}

void initialize_environment() {
    g_extension_manager = new extension_manager();
}

void finalize_environment() {
    delete g_extension_manager;
}

unsigned environment::register_extension(std::shared_ptr<environment_extension const> const & initial) {
    return get_extension_manager().register_extension(initial);
}

[[ noreturn ]] void throw_invalid_extension(environment const & env) {
    throw kernel_exception(env, "invalid environment extension identifier");
}

environment_extension const & environment::get_extension(unsigned id) const {
    if (!get_extension_manager().has_ext(id))
        throw_invalid_extension(*this);
    if (id >= m_extensions->size() || !(*m_extensions)[id])
        return get_extension_manager().get_initial(id);
    return *((*m_extensions)[id].get());
}

environment environment::update(unsigned id, std::shared_ptr<environment_extension const> const & ext) const {
    if (!get_extension_manager().has_ext(id))
        throw_invalid_extension(*this);
    auto new_exts = std::make_shared<environment_extensions>(*m_extensions);
    if (id >= new_exts->size())
        new_exts->resize(id+1);
    (*new_exts)[id] = ext;
    return environment(*this, new_exts);
}

void environment::for_each_constant(std::function<void(constant_info const & d)> const & f) const {
    m_constants.for_each([&](name const &, constant_info const & c) { return f(c); });
}
}
