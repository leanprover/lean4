/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include <limits>
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"

namespace lean {
/**
   \brief "Do nothing" normalizer extension.
*/
class noop_normalizer_extension : public normalizer_extension {
public:
    virtual optional<expr> operator()(expr const &, extension_context &) const {
        return none_expr();
    }
};

environment_header::environment_header(unsigned trust_lvl, bool prop_proof_irrel, bool eta, bool impredicative,
                                       list<name> const & cls_proof_irrel, std::unique_ptr<normalizer_extension const> ext):
    m_trust_lvl(trust_lvl), m_prop_proof_irrel(prop_proof_irrel), m_eta(eta), m_impredicative(impredicative),
    m_cls_proof_irrel(cls_proof_irrel), m_norm_ext(std::move(ext)) {}

environment_extension::~environment_extension() {}

environment_id::environment_id():m_trail(0, list<unsigned>()) {}

environment_id::environment_id(environment_id const & ancestor, bool):m_trail(car(ancestor.m_trail) + 1, ancestor.m_trail) {}

bool environment_id::is_descendant(environment_id const & id) const {
    list<unsigned> const * it = &m_trail;
    while (!is_nil(*it)) {
        if (is_eqp(*it, id.m_trail))
            return true;
        if (car(*it) < car(id.m_trail))
            return false;
        it = &cdr(*it);
    }
    return false;
}

environment::environment(header const & h, environment_id const & ancestor, definitions const & d, name_set const & g, extensions const & exts):
    m_header(h), m_id(environment_id::mk_descendant(ancestor)), m_definitions(d), m_global_levels(g), m_extensions(exts) {}

environment::environment(unsigned trust_lvl, bool prop_proof_irrel, bool eta, bool impredicative, list<name> const & cls_proof_irrel):
    environment(trust_lvl, prop_proof_irrel, eta, impredicative, cls_proof_irrel, std::unique_ptr<normalizer_extension>(new noop_normalizer_extension()))
{}

environment::environment(unsigned trust_lvl, bool prop_proof_irrel, bool eta, bool impredicative, list<name> const & cls_proof_irrel,
                         std::unique_ptr<normalizer_extension> ext):
    m_header(std::make_shared<environment_header>(trust_lvl, prop_proof_irrel, eta, impredicative, cls_proof_irrel, std::move(ext))),
    m_extensions(std::make_shared<environment_extensions const>())
{}

environment::~environment() {}

optional<definition> environment::find(name const & n) const {
    definition const * r = m_definitions.find(n);
    return r ? some_definition(*r) : none_definition();
}

definition environment::get(name const & n) const {
    definition const * r = m_definitions.find(n);
    if (!r)
        throw_unknown_declaration(*this, n);
    return *r;
}

[[ noreturn ]] void throw_incompatible_environment(environment const & env) {
    throw_kernel_exception(env, "invalid declaration, it was checked/certified in an incompatible environment");
}

environment environment::add(certified_definition const & d) const {
    if (!m_id.is_descendant(d.get_id()))
        throw_incompatible_environment(*this);
    name const & n = d.get_definition().get_name();
    if (find(n))
        throw_already_declared(*this, n);
    return environment(m_header, m_id, insert(m_definitions, n, d.get_definition()), m_global_levels, m_extensions);
}

environment environment::add_global_level(name const & n) const {
    if (m_global_levels.contains(n))
        throw_kernel_exception(*this,
                               "invalid global universe level declaration, environment already contains a universe level with the given name");
    return environment(m_header, m_id, m_definitions, insert(m_global_levels, n), m_extensions);
}

bool environment::is_global_level(name const & n) const {
    return m_global_levels.contains(n);
}

environment environment::replace(certified_definition const & t) const {
    if (!m_id.is_descendant(t.get_id()))
        throw_incompatible_environment(*this);
    name const & n = t.get_definition().get_name();
    auto ax = find(n);
    if (!ax)
        throw_kernel_exception(*this, "invalid replacement of axiom with theorem, the environment does not have an axiom with the given name");
    if (!ax->is_axiom())
        throw_kernel_exception(*this, "invalid replacement of axiom with theorem, the current declaration in the environment is not an axiom");
    if (!t.get_definition().is_theorem())
        throw_kernel_exception(*this, "invalid replacement of axiom with theorem, the new declaration is not a theorem");
    if (ax->get_type() != t.get_definition().get_type())
        throw_kernel_exception(*this, "invalid replacement of axiom with theorem, the 'replace' operation can only be used when the axiom and theorem have the same type");
    return environment(m_header, m_id, insert(m_definitions, n, t.get_definition()), m_global_levels, m_extensions);
}

environment environment::forget() const {
    return environment(m_header, environment_id(), m_definitions, m_global_levels, m_extensions);
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

static std::unique_ptr<extension_manager> g_extension_manager;

static extension_manager & get_extension_manager() {
    if (!g_extension_manager)
        g_extension_manager.reset(new extension_manager());
    return *g_extension_manager;
}

unsigned environment::register_extension(std::shared_ptr<environment_extension const> const & initial) {
    return get_extension_manager().register_extension(initial);
}

[[ noreturn ]] void throw_invalid_extension(environment const & env) {
    throw_kernel_exception(env, "invalid environment extension identifier");
}

environment_extension const & environment::get_extension(unsigned id) const {
    if (id >= get_extension_manager().has_ext(id))
        throw_invalid_extension(*this);
    if (id < m_extensions->size() || !(*m_extensions)[id])
        return get_extension_manager().get_initial(id);
    return *((*m_extensions)[id].get());
}

environment environment::update(unsigned id, std::shared_ptr<environment_extension const> const & ext) const {
    if (id >= get_extension_manager().has_ext(id))
        throw_invalid_extension(*this);
    auto new_exts = std::make_shared<environment_extensions>(*m_extensions);
    if (id >= new_exts->size())
        new_exts->resize(id+1);
    (*new_exts)[id] = ext;
    return environment(m_header, m_id, m_definitions, m_global_levels, new_exts);
}
}
