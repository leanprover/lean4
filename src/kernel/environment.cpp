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

namespace lean {
environment_header::environment_header(unsigned trust_lvl, std::unique_ptr<normalizer_extension const> ext):
    m_trust_lvl(trust_lvl), m_norm_ext(std::move(ext)) {}

environment_extension::~environment_extension() {}

struct environment_id::path {
    unsigned m_next_depth;
    unsigned m_start_depth;
    mutex    m_mutex;
    path *   m_prev;
    MK_LEAN_RC(); // Declare m_rc counter
    void dealloc() { delete this; }

    path():m_next_depth(1), m_start_depth(0), m_prev(nullptr), m_rc(1) {}
    path(unsigned start_depth, path * prev):m_next_depth(start_depth + 1), m_start_depth(start_depth), m_prev(prev), m_rc(1) {
        if (prev) prev->inc_ref();
    }
    ~path() { if (m_prev) m_prev->dec_ref(); }
};

environment_id::environment_id():m_ptr(new path()), m_depth(0) {}
environment_id::environment_id(environment_id const & ancestor, bool) {
    if (ancestor.m_depth == std::numeric_limits<unsigned>::max())
        throw exception("maximal depth in is_descendant tree has been reached, use 'forget' method to workaround this limitation");
    lock_guard<mutex> lock(ancestor.m_ptr->m_mutex);
    if (ancestor.m_ptr->m_next_depth == ancestor.m_depth + 1) {
        m_ptr   = ancestor.m_ptr;
        m_depth = ancestor.m_depth + 1;
        m_ptr->m_next_depth++;
        m_ptr->inc_ref();
    } else {
        m_ptr   = new path(ancestor.m_depth+1, ancestor.m_ptr);
        m_depth = ancestor.m_depth + 1;
    }
    lean_assert(m_depth == ancestor.m_depth+1);
    lean_assert(m_ptr->m_next_depth == m_depth+1);
}
environment_id::environment_id(environment_id const & id):m_ptr(id.m_ptr), m_depth(id.m_depth) { if (m_ptr) m_ptr->inc_ref(); }
environment_id::environment_id(environment_id && id):m_ptr(id.m_ptr), m_depth(id.m_depth) { id.m_ptr = nullptr; }
environment_id::~environment_id() { if (m_ptr) m_ptr->dec_ref(); }
environment_id & environment_id::operator=(environment_id const & s) { m_depth = s.m_depth; LEAN_COPY_REF(s); }
environment_id & environment_id::operator=(environment_id && s) { m_depth = s.m_depth; LEAN_MOVE_REF(s); }
bool environment_id::is_descendant(environment_id const & id) const {
    if (m_depth < id.m_depth)
        return false;
    path * p = m_ptr;
    while (p != nullptr) {
        if (p == id.m_ptr)
            return true;
        if (p->m_start_depth <= id.m_depth)
            return false;
        p = p->m_prev;
    }
    return false;
}

environment::environment(header const & h, environment_id const & ancestor, declarations const & d, extensions const & exts):
    m_header(h), m_id(environment_id::mk_descendant(ancestor)), m_declarations(d), m_extensions(exts) {}

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
        throw_unknown_declaration(*this, n);
    return *r;
}

[[ noreturn ]] void throw_incompatible_environment(environment const & env) {
    throw_kernel_exception(env, "invalid declaration, it was checked/certified in an incompatible environment");
}

environment environment::add(certified_declaration const & d) const {
    if (!m_id.is_descendant(d.get_id()))
        throw_incompatible_environment(*this);
    name const & n = d.get_declaration().get_name();
    if (find(n))
        throw_already_declared(*this, n);
    return environment(m_header, m_id, insert(m_declarations, n, d.get_declaration()), m_extensions);
}

environment environment::replace(certified_declaration const & t) const {
    if (!m_id.is_descendant(t.get_id()))
        throw_incompatible_environment(*this);
    name const & n = t.get_declaration().get_name();
    auto ax = find(n);
    if (!ax)
        throw_kernel_exception(*this, "invalid replacement of axiom with theorem, the environment does not have an axiom with the given name");
    if (!ax->is_axiom())
        throw_kernel_exception(*this, "invalid replacement of axiom with theorem, the current declaration in the environment is not an axiom");
    if (!t.get_declaration().is_theorem())
        throw_kernel_exception(*this, "invalid replacement of axiom with theorem, the new declaration is not a theorem");
    if (ax->get_type() != t.get_declaration().get_type())
        throw_kernel_exception(*this, "invalid replacement of axiom with theorem, the 'replace' operation can only be used when the axiom and theorem have the same type");
    if (ax->get_univ_params() != t.get_declaration().get_univ_params())
        throw_kernel_exception(*this, "invalid replacement of axiom with theorem, the 'replace' operation can only be used when the axiom and theorem have the same universe parameters");
    return environment(m_header, m_id, insert(m_declarations, n, t.get_declaration()), m_extensions);
}

environment environment::forget() const {
    return environment(m_header, environment_id(), m_declarations, m_extensions);
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
    throw_kernel_exception(env, "invalid environment extension identifier");
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
    return environment(m_header, m_id, m_declarations, new_exts);
}

void environment::for_each_declaration(std::function<void(declaration const & d)> const & f) const {
    m_declarations.for_each([&](name const &, declaration const & d) { return f(d); });
}
}
