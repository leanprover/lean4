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
environment_header::environment_header(unsigned trust_lvl, std::unique_ptr<normalizer_extension const> ext):
    m_trust_lvl(trust_lvl), m_norm_ext(std::move(ext)) {}

environment_extension::~environment_extension() {}

environment::environment(unsigned trust_lvl):
    environment(trust_lvl, mk_id_normalizer_extension())
{}

environment::environment(unsigned trust_lvl, std::unique_ptr<normalizer_extension> ext):
    m_header(std::make_shared<environment_header>(trust_lvl, std::move(ext))),
    m_extensions(std::make_shared<environment_extensions const>())
{}

environment::~environment() {}

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

bool environment::is_recursor(name const & n) const {
    return m_header->is_recursor(*this, n) || (m_quot_initialized && quot_is_rec(n));
}

bool environment::is_builtin(name const & n) const {
    return m_header->is_builtin(*this, n) || (m_quot_initialized && quot_is_decl(n));
}

environment environment::add_quot() const {
    if (m_quot_initialized)
        return *this;
    environment new_env = quot_declare(*this);
    new_env.m_quot_initialized = true;
    return new_env;
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

static void check_duplicated_univ_params(environment const & env, declaration const & d) {
    level_param_names ls = d.get_univ_params();
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

static void check_definition_value(environment const & env, declaration const & d, type_checker & checker) {
    check_no_metavar_no_fvar(env, d.get_name(), d.get_value());
    expr val_type = checker.check(d.get_value(), d.get_univ_params());
    if (!checker.is_def_eq(val_type, d.get_type())) {
        throw definition_type_mismatch_exception(env, d, val_type);
    }
}

static void check_definition_value(environment const & env, declaration const & d) {
    bool memoize = true; bool non_meta_only = !d.is_meta();
    type_checker checker(env, memoize, non_meta_only);
    if (d.has_value()) {
        check_definition_value(env, d, checker);
    }
}

static void check_declaration_type(environment const & env, declaration const & d, type_checker & checker) {
    check_no_metavar_no_fvar(env, d.get_name(), d.get_type());
    check_duplicated_univ_params(env, d);
    expr sort = checker.check(d.get_type(), d.get_univ_params());
    checker.ensure_sort(sort, d.get_type());
}

static void check_declaration_type(environment const & env, declaration const & d) {
    bool memoize = true; bool non_meta_only = !d.is_meta();
    type_checker checker(env, memoize, non_meta_only);
    check_declaration_type(env, d, checker);
}

environment environment::add_defn_thm_axiom(declaration const & d, bool check) const {
    if (check) {
        bool memoize = true; bool non_meta_only = !d.is_meta();
        check_name(*this, d.get_name());
        type_checker checker(*this, memoize, non_meta_only);
        check_declaration_type(*this, d, checker);
        if (d.has_value()) {
            check_definition_value(*this, d, checker);
        }
    }
    return environment(*this, insert(m_constants, d.get_name(), constant_info(d)));
}

environment environment::add(declaration const & d, bool check) const {
    switch (d.kind()) {
    case declaration_kind::Axiom: case declaration_kind::Definition: case declaration_kind::Theorem:
        return add_defn_thm_axiom(d, check);
    default:
        // NOT IMPLEMENTED YET.
        lean_unreachable();
    }
}

environment environment::add_meta(buffer<declaration> const & ds, bool check) const {
    if (!check && trust_lvl() == 0)
        throw kernel_exception(*this, "invalid meta declarations, type checking cannot be skipped at trust level 0");
    environment new_env = *this;
    /* Check declarations header, and add them to new_env.m_constants */
    for (declaration const & d : ds) {
        check_name(new_env, d.get_name());
        if (check)
            check_declaration_type(new_env, d);
        new_env.m_constants.insert(d.get_name(), constant_info(d));
    }
    /* Check actual definitions */
    if (check) {
        for (declaration const & d : ds) {
            check_definition_value(new_env, d);
        }
    }
    return new_env;
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
