/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <string>
#include <algorithm>
#include "util/sstream.h"
#include "library/attribute_manager.h"

namespace lean {
struct attribute_decl {
    std::string        m_id;
    std::string        m_descr;
    std::string        m_token;
    has_attribute_proc m_tester;
};

struct default_attribute_decl : public attribute_decl {
    set_attribute_proc m_setter;
};

struct prioritized_attribute_decl : public attribute_decl {
    set_prio_attribute_proc  m_setter;
    get_attribute_prio_proc  m_getter;
};

struct param_attribute_decl : public attribute_decl {
    set_param_attribute_proc m_setter;
    get_attribute_param_proc m_getter;
};

struct opt_param_attribute_decl : public attribute_decl {
    set_opt_param_attribute_proc m_setter;
    get_attribute_param_proc     m_getter;
};

struct params_attribute_decl : public attribute_decl {
    set_params_attribute_proc m_setter;
    get_attribute_params_proc m_getter;
};

static std::vector<default_attribute_decl> *         g_default_attrs = nullptr;
static std::vector<prioritized_attribute_decl> *     g_prio_attrs = nullptr;
static std::vector<param_attribute_decl> *           g_param_attrs = nullptr;
static std::vector<opt_param_attribute_decl> *       g_opt_param_attrs = nullptr;
static std::vector<params_attribute_decl> *          g_params_attrs = nullptr;
static std::vector<pair<std::string, std::string>> * g_incomp = nullptr;

template<typename Decls>
bool is_attribute(Decls const & decls, char const * attr) {
    for (auto const & d : decls) {
        if (d.m_id == attr)
            return true;
    }
    return false;
}

bool is_attribute(char const * attr) {
    return
        is_attribute(*g_default_attrs, attr) ||
        is_attribute(*g_prio_attrs, attr) ||
        is_attribute(*g_param_attrs, attr) ||
        is_attribute(*g_opt_param_attrs, attr) ||
        is_attribute(*g_params_attrs, attr);
}

template<typename Decl, typename Setter, typename Tester>
void set_core_fields(Decl & decl, char const * attr, char const * descr, Setter const & setter, Tester const & tester) {
    decl.m_id     = attr;
    decl.m_descr  = descr;
    decl.m_setter = setter;
    decl.m_tester = tester;
}

void register_attribute(char const * attr, char const * descr, set_attribute_proc const & setter,
                        has_attribute_proc const & tester) {
    lean_assert(!is_attribute(attr));
    default_attribute_decl decl;
    set_core_fields(decl, attr, descr, setter, tester);
    decl.m_token  = std::string("[") + attr + "]";
    g_default_attrs->push_back(decl);
}

void register_prio_attribute(char const * attr, char const * descr, set_prio_attribute_proc const & setter,
                             has_attribute_proc const & tester, get_attribute_prio_proc const & getter) {
    lean_assert(!is_attribute(attr));
    prioritized_attribute_decl decl;
    set_core_fields(decl, attr, descr, setter, tester);
    decl.m_token  = std::string("[") + attr + "]";
    decl.m_getter = getter;
    g_prio_attrs->push_back(decl);
}

void register_param_attribute(char const * attr, char const * descr, set_param_attribute_proc const & setter,
                              has_attribute_proc const & tester, get_attribute_param_proc const & getter) {
    lean_assert(!is_attribute(attr));
    param_attribute_decl decl;
    set_core_fields(decl, attr, descr, setter, tester);
    decl.m_token  = std::string("[") + attr;
    decl.m_getter = getter;
    g_param_attrs->push_back(decl);
}

void register_opt_param_attribute(char const * attr, char const * descr, set_opt_param_attribute_proc const & setter,
                                  has_attribute_proc const & tester, get_attribute_param_proc const & getter) {
    lean_assert(!is_attribute(attr));
    opt_param_attribute_decl decl;
    set_core_fields(decl, attr, descr, setter, tester);
    decl.m_token  = std::string("[") + attr;
    decl.m_getter = getter;
    g_opt_param_attrs->push_back(decl);
}

void register_params_attribute(char const * attr, char const * descr, set_params_attribute_proc const & setter,
                               has_attribute_proc const & tester, get_attribute_params_proc const & getter) {
    lean_assert(!is_attribute(attr));
    params_attribute_decl decl;
    set_core_fields(decl, attr, descr, setter, tester);
    decl.m_token  = std::string("[") + attr;
    decl.m_getter = getter;
    g_params_attrs->push_back(decl);
}

void register_incompatible(char const * attr1, char const * attr2) {
    lean_assert(is_attribute(attr1));
    lean_assert(is_attribute(attr2));
    std::string s1(attr1);
    std::string s2(attr2);
    if (s1 > s2)
        std::swap(s1, s2);
    g_incomp->emplace_back(s1, s2);
}

template<typename Decls>
void get_attributes(Decls const & decls, buffer<char const *> & r) {
    for (auto const & d : decls)
        r.push_back(d.m_id.c_str());
}

void get_attributes(buffer<char const *> & r) {
    get_attributes(*g_default_attrs, r);
    get_attributes(*g_prio_attrs, r);
    get_attributes(*g_param_attrs, r);
    get_attributes(*g_opt_param_attrs, r);
    get_attributes(*g_params_attrs, r);
}

template<typename Decls>
void get_attribute_tokens(Decls const & decls, buffer<char const *> & r) {
    for (auto const & d : decls)
        r.push_back(d.m_token.c_str());
}

void get_attribute_tokens(buffer<char const *> & r) {
    get_attribute_tokens(*g_default_attrs, r);
    get_attribute_tokens(*g_prio_attrs, r);
    get_attribute_tokens(*g_param_attrs, r);
    get_attribute_tokens(*g_opt_param_attrs, r);
    get_attribute_tokens(*g_params_attrs, r);
}

template<typename Decls>
char const * get_attribute_from_token(Decls const & decls, char const * tk) {
    for (auto const & d : decls) {
        if (d.m_token == tk)
            return d.m_id.c_str();
    }
    return nullptr;
}

char const * get_attribute_from_token(char const * tk) {
    if (auto r = get_attribute_from_token(*g_default_attrs, tk)) return r;
    if (auto r = get_attribute_from_token(*g_prio_attrs, tk)) return r;
    if (auto r = get_attribute_from_token(*g_param_attrs, tk)) return r;
    if (auto r = get_attribute_from_token(*g_opt_param_attrs, tk)) return r;
    if (auto r = get_attribute_from_token(*g_params_attrs, tk)) return r;
    return nullptr;
}

template<typename Decls>
char const * get_attribute_token(Decls const & decls, char const * attr) {
    for (auto const & d : decls) {
        if (d.m_id == attr)
            return d.m_token.c_str();
    }
    return nullptr;
}

char const * get_attribute_token(char const * attr) {
    if (auto r = get_attribute_token(*g_default_attrs, attr)) return r;
    if (auto r = get_attribute_token(*g_prio_attrs, attr)) return r;
    if (auto r = get_attribute_token(*g_param_attrs, attr)) return r;
    if (auto r = get_attribute_token(*g_opt_param_attrs, attr)) return r;
    if (auto r = get_attribute_token(*g_params_attrs, attr)) return r;
    return nullptr;
}

attribute_kind get_attribute_kind (char const * attr) {
    lean_assert(is_attribute(attr));
    if (is_attribute(*g_default_attrs, attr)) return attribute_kind::Default;
    if (is_attribute(*g_prio_attrs, attr)) return attribute_kind::Prioritized;
    if (is_attribute(*g_param_attrs, attr)) return attribute_kind::Parametric;
    if (is_attribute(*g_opt_param_attrs, attr)) return attribute_kind::OptParametric;
    if (is_attribute(*g_params_attrs, attr)) return attribute_kind::MultiParametric;
    lean_unreachable();
}

template<typename Decls>
bool has_attribute(Decls const & decls, environment const & env, char const * attr, name const & d) {
    for (auto const & decl : decls) {
        if (decl.m_id == attr)
            return decl.m_tester(env, d);
    }
    return false;
}

bool has_attribute(environment const & env, char const * attr, name const & d) {
    return
        has_attribute(*g_default_attrs, env, attr, d) ||
        has_attribute(*g_prio_attrs, env, attr, d) ||
        has_attribute(*g_param_attrs, env, attr, d) ||
        has_attribute(*g_opt_param_attrs, env, attr, d) ||
        has_attribute(*g_params_attrs, env, attr, d);
}

[[ noreturn ]] void throw_unknown_attribute(char const * attr) {
    throw exception(sstream() << "unknown attribute '" << attr << "'");
}

environment set_attribute(environment const & env, io_state const & ios, char const * attr,
                          name const & d, name const & ns, bool persistent) {
    for (auto const & decl : *g_default_attrs) {
        if (decl.m_id == attr)
            return decl.m_setter(env, ios, d, ns, persistent);
    }
    throw_unknown_attribute(attr);
}

environment set_prio_attribute(environment const & env, io_state const & ios, char const * attr,
                               name const & d, unsigned prio, name const & ns, bool persistent) {
    for (auto const & decl : *g_prio_attrs) {
        if (decl.m_id == attr)
            return decl.m_setter(env, ios, d, prio, ns, persistent);
    }
    throw_unknown_attribute(attr);
}

environment set_param_attribute(environment const & env, io_state const & ios, char const * attr,
                                name const & d, unsigned param, name const & ns, bool persistent) {
    for (auto const & decl : *g_param_attrs) {
        if (decl.m_id == attr)
            return decl.m_setter(env, ios, d, param, ns, persistent);
    }
    throw_unknown_attribute(attr);
}

environment set_opt_param_attribute(environment const & env, io_state const & ios, char const * attr,
                                    name const & d, optional<unsigned> const & param, name const & ns, bool persistent) {
    for (auto const & decl : *g_opt_param_attrs) {
        if (decl.m_id == attr)
            return decl.m_setter(env, ios, d, param, ns, persistent);
    }
    throw_unknown_attribute(attr);
}

environment set_params_attribute(environment const & env, io_state const & ios, char const * attr,
                                 name const & d, list<unsigned> const & params, name const & ns, bool persistent) {
    for (auto const & decl : *g_params_attrs) {
        if (decl.m_id == attr)
            return decl.m_setter(env, ios, d, params, ns, persistent);
    }
    throw_unknown_attribute(attr);
}

unsigned get_attribute_prio(environment const & env, char const * attr, name const & d) {
    for (auto const & decl : *g_prio_attrs) {
        if (decl.m_id == attr)
            return decl.m_getter(env, d);
    }
    throw_unknown_attribute(attr);
}

unsigned get_attribute_param(environment const & env, char const * attr, name const & d) {
    for (auto const & decl : *g_param_attrs) {
        if (decl.m_id == attr)
            return decl.m_getter(env, d);
    }
    for (auto const & decl : *g_opt_param_attrs) {
        if (decl.m_id == attr)
            return decl.m_getter(env, d);
    }
    throw_unknown_attribute(attr);
}

list<unsigned> get_attribute_params(environment const & env, char const * attr, name const & d) {
    for (auto const & decl : *g_params_attrs) {
        if (decl.m_id == attr)
            return decl.m_getter(env, d);
    }
    throw_unknown_attribute(attr);
}

bool are_incompatible(char const * attr1, char const * attr2) {
    std::string s1(attr1);
    std::string s2(attr2);
    if (s1 > s2)
        std::swap(s1, s2);
    return std::find(g_incomp->begin(), g_incomp->end(), mk_pair(s1, s2)) != g_incomp->end();
}

void initialize_attribute_manager() {
    g_default_attrs   = new std::vector<default_attribute_decl>();
    g_prio_attrs      = new std::vector<prioritized_attribute_decl>();
    g_param_attrs     = new std::vector<param_attribute_decl>();
    g_opt_param_attrs = new std::vector<opt_param_attribute_decl>();
    g_params_attrs    = new std::vector<params_attribute_decl>();
    g_incomp          = new std::vector<pair<std::string, std::string>>();
}

void finalize_attribute_manager() {
    delete g_default_attrs;
    delete g_prio_attrs;
    delete g_param_attrs;
    delete g_opt_param_attrs;
    delete g_params_attrs;
}
}
