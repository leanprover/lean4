/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include <limits>
#include <util/task_builder.h>
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

optional<declaration> environment::find(name const & n) const {
    declaration const * r = m_declarations.find(n);
    return r ? some_declaration(*r) : none_declaration();
}

declaration environment::get(name const & n) const {
    declaration const * r = m_declarations.find(n);
    if (!r)
        throw unknown_declaration_exception(*this, n);
    return *r;
}

[[ noreturn ]] void throw_incompatible_environment(environment const & env) {
    throw kernel_exception(env, "invalid declaration, it was checked/certified in an incompatible environment");
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

environment environment::add(certified_declaration const & d) const {
    name const & n = d.get_declaration().get_name();
    if (find(n))
        throw already_declared_exception(*this, n);
    return environment(*this, insert(m_declarations, n, d.get_declaration()));
}

environment environment::add_meta(buffer<declaration> const & ds, bool check) const {
    if (!check && trust_lvl() == 0)
        throw kernel_exception(*this, "invalid meta declarations, type checking cannot be skipped at trust level 0");
    environment new_env = *this;
    /* Check declarations header, and add them to new_env.m_declarations */
    for (declaration const & d : ds) {
        if (check)
            check_decl_type(new_env, d);
        new_env.m_declarations.insert(d.get_name(), d);
    }
    /* Check actual definitions */
    if (check) {
        for (declaration const & d : ds) {
            check_decl_value(new_env, d);
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

void environment::for_each_declaration(std::function<void(declaration const & d)> const & f) const {
    m_declarations.for_each([&](name const &, declaration const & d) { return f(d); });
}
}
