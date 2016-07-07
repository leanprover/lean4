/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <string>
#include <algorithm>
#include "util/priority_queue.h"
#include "util/sstream.h"
#include "library/attribute_manager.h"
#include "library/scoped_ext.h"

namespace lean {
struct attribute_decl {
    std::string        m_id;
    std::string        m_descr;
    std::string        m_token;
    set_attribute_proc m_on_set;
};

static std::vector<attribute_decl> * g_attr_decls;
static std::vector<pair<std::string, std::string>> * g_incomp = nullptr;

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct attr_record {
    name      m_decl;
    list<unsigned> m_params;

    attr_record() {}
    attr_record(name decl, list<unsigned> params):
            m_decl(decl), m_params(params) {}

    unsigned hash() const {
        unsigned h = m_decl.hash();
        for (unsigned p : m_params)
            h = ::lean::hash(h, p);
        return h;
    }
};

struct attr_record_cmp {
    int operator()(attr_record const & r1, attr_record const & r2) const {
        // Adding a new record with different arguments should override the old one
        return quick_cmp(r1.m_decl, r2.m_decl);
    }
};

struct attr_entry {
    name     m_attr;
    unsigned m_prio;
    attr_record m_record;

    attr_entry() {}
    attr_entry(name attr, unsigned prio, attr_record record):
            m_attr(attr), m_prio(prio), m_record(record) {}
};

typedef priority_queue<attr_record, attr_record_cmp> attr_records;
typedef name_map<attr_records> attr_state;

struct attr_config {
    typedef attr_state state;
    typedef attr_entry entry;
    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        attr_records m;
        if (auto q = s.find(e.m_attr))
            m = *q;
        m.insert(e.m_record, e.m_prio);
        s.insert(e.m_attr, m);
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void write_entry(serializer & s, entry const & e) {
        s << e.m_attr << e.m_prio << e.m_record.m_decl;
        write_list(s, e.m_record.m_params);
    }
    static entry read_entry(deserializer & d) {
        entry e;
        d >> e.m_attr >> e.m_prio >> e.m_record.m_decl;
        e.m_record.m_params = read_list<unsigned>(d);
        return e;
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return optional<unsigned>(hash(hash(e.m_attr.hash(), e.m_record.hash()), e.m_prio));
    }
};

template class scoped_ext<attr_config>;
typedef scoped_ext<attr_config> attribute_ext;

bool is_attribute(char const * attr) {
    for (auto const & d : *g_attr_decls) {
        if (d.m_id == attr)
            return true;
    }
    return false;
}

void register_attribute(char const * attr, char const * descr, set_attribute_proc const & on_set) {
    lean_assert(!is_attribute(attr));
    g_attr_decls->push_back(attribute_decl {attr, descr, std::string("[") + attr, on_set});
}

void register_no_params_attribute(char const * attr, char const * descr, set_no_params_attribute_proc const & on_set) {
    register_attribute(attr, descr,
                       [=](environment const & env, io_state const & ios, name const & d, unsigned prio,
                           list<unsigned> const & idxs, name const & ns, bool persistent) {
                           if (prio != LEAN_DEFAULT_PRIORITY)
                               throw exception(sstream() << "invalid [" << attr <<
                                               "] declaration, unexpected priority declaration");
                           if (idxs)
                               throw exception(sstream() << "invalid [" << attr <<
                                               "] declaration, unexpected parameter");
                           return on_set(env, ios, d, ns, persistent);
                       });
}
void register_no_params_attribute(char const * attr, char const * descr) {
    register_no_params_attribute(attr, descr,
                                 [](environment const & env, io_state const &, name const &, name const &, bool) {
                                     return env;
                                 });
}

void register_prio_attribute(char const * attr, char const * descr, set_prio_attribute_proc const & on_set) {
    register_attribute(attr, descr,
                       [=](environment const & env, io_state const & ios, name const & d, unsigned prio,
                          list<unsigned> const & idxs, name const & ns, bool persistent) {
                           if (idxs)
                               throw exception(sstream() << "invalid [" << attr <<
                                               "] declaration, unexpected parameter");
                           return on_set(env, ios, d, prio, ns, persistent);
                       });
}

void register_opt_param_attribute(char const * attr, char const * descr, set_opt_param_attribute_proc const & on_set) {
    register_attribute(attr, descr,
                       [=](environment const & env, io_state const & ios, name const & d, unsigned prio,
                          list<unsigned> const & idxs, name const & ns, bool persistent) {
                           if (prio != LEAN_DEFAULT_PRIORITY)
                               throw exception(sstream() << "invalid [" << attr <<
                                               "] declaration, unexpected priority declaration");
                           if (idxs && tail(idxs))
                               throw exception(sstream() << "invalid [" << attr <<
                                               "] declaration, expected at most one parameter");
                           return on_set(env, ios, d, head_opt(idxs), ns, persistent);
                       });
}

void register_params_attribute(char const * attr, char const * descr, set_params_attribute_proc const & on_set) {
    register_attribute(attr, descr,
                       [=](environment const & env, io_state const & ios, name const & d, unsigned prio,
                          list<unsigned> const & idxs, name const & ns, bool persistent) {
                           if (prio != LEAN_DEFAULT_PRIORITY)
                               throw exception(sstream() << "invalid [" << attr <<
                                               "] declaration, unexpected priority declaration");
                           return on_set(env, ios, d, idxs, ns, persistent);
                       });
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

void get_attributes(buffer<char const *> & r) {
    for (auto const & d : *g_attr_decls)
        r.push_back(d.m_id.c_str());
}

void get_attribute_tokens(buffer<char const *> & r) {
    for (auto const & d : *g_attr_decls)
        r.push_back(d.m_token.c_str());
}

char const * get_attribute_from_token(char const * tk) {
    for (auto const & d : *g_attr_decls) {
        if (d.m_token == tk)
            return d.m_id.c_str();
    }
    return nullptr;
}

char const * get_attribute_token(char const * attr) {
    for (auto const & d : *g_attr_decls) {
        if (d.m_id == attr)
            return d.m_token.c_str();
    }
    return nullptr;
}

bool has_attribute(environment const & env, char const * attr, name const & d) {
    if (auto it = attribute_ext::get_state(env).find(attr))
        return it->contains(attr_record(d, list<unsigned>()));
    return false;
}

void get_attribute_instances(environment const & env, name const & attr, buffer<name> & r) {
    attribute_ext::get_state(env).for_each([&](name const & n, attr_records const & recs){
        if (n == attr)
            recs.for_each([&](attr_record const & rec) { r.push_back(rec.m_decl); });
    });
}

void get_attribute_instances(environment const & env, name const & attr, name const & ns, buffer<name> & r) {
    if (auto entries = attribute_ext::get_entries(env, ns)) {
        for (auto const & e : *entries) {
            if (e.m_attr == attr)
                r.push_back(e.m_record.m_decl);
        }
    }
}

[[ noreturn ]] void throw_unknown_attribute(name const & attr) {
    throw exception(sstream() << "unknown attribute '" << attr << "'");
}

environment set_attribute(environment const & env, io_state const & ios, char const * attr,
                          name const & d, unsigned prio, list<unsigned> const & params, name const & ns, bool persistent) {
    for (auto const & decl : *g_attr_decls) {
        if (decl.m_id == attr) {
            auto env2 = attribute_ext::add_entry(env, ios, attr_entry(attr, prio, attr_record(d, params)), ns, persistent);
            return decl.m_on_set(env2, ios, d, prio, params, ns, persistent);
        }
    }
    throw_unknown_attribute(attr);
}

environment set_attribute(environment const & env, io_state const & ios, char const * attr,
                          name const & d, name const & ns, bool persistent) {
    return set_attribute(env, ios, attr, d, LEAN_DEFAULT_PRIORITY, list<unsigned>(), ns, persistent);
}

unsigned get_attribute_prio(environment const & env, name const & attr, name const & d) {
    if (auto it = attribute_ext::get_state(env).find(attr)) {
        optional<unsigned> prio = it->get_prio({d, list<unsigned>()});
        return prio ? *prio : LEAN_DEFAULT_PRIORITY;
    }
    throw_unknown_attribute(attr);
}

list<unsigned> get_attribute_params(environment const & env, name const & attr, name const & d) {
    if (auto it = attribute_ext::get_state(env).find(attr)) {
        if (auto record = it->get_key(attr_record {d, list<unsigned>()}))
                return record->m_params;
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
    g_attr_decls = new std::vector<attribute_decl>();
    g_incomp     = new std::vector<pair<std::string, std::string>>();
    g_class_name = new name("attribute");
    g_key        = new std::string("ATTR");
    attribute_ext::initialize();
}

void finalize_attribute_manager() {
    attribute_ext::finalize();
    delete g_key;
    delete g_class_name;
    delete g_incomp;
    delete g_attr_decls;
}
}
