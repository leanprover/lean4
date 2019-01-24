/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <string>
#include <algorithm>
#include <unordered_map>
#include "runtime/sstream.h"
#include "util/priority_queue.h"
#include "library/attribute_manager.h"
#include "library/scoped_ext.h"

namespace lean {
template class typed_attribute<indices_attribute_data>;

static name_map<attribute_ptr> * g_system_attributes = nullptr;
static user_attribute_ext * g_user_attribute_ext     = nullptr;
static attr_data_ptr * g_default_attr_data_ptr       = nullptr;

attr_data_ptr get_default_attr_data() {
    return *g_default_attr_data_ptr;
}

name_map<attribute_ptr> user_attribute_ext::get_attributes(environment const &) {
    return {};
}
void set_user_attribute_ext(std::unique_ptr<user_attribute_ext> ext) {
    if (g_user_attribute_ext) delete g_user_attribute_ext;
    g_user_attribute_ext = ext.release();
}

static std::vector<pair<name, name>> * g_incomp = nullptr;

bool is_system_attribute(name const & attr) {
    return g_system_attributes->contains(attr);
}
void register_system_attribute(attribute_ptr attr) {
    lean_assert(!is_system_attribute(attr->get_name()));
    (*g_system_attributes)[attr->get_name()] = attr;
}
bool is_attribute(environment const & env, name const & attr) {
    return is_system_attribute(attr) || g_user_attribute_ext->get_attributes(env).find(attr) != nullptr;
}

attribute const & get_system_attribute(name const & attr) {
    auto it = g_system_attributes->find(attr);
    if (it)
        return **it;
    throw exception(sstream() << "unknown system attribute '" << attr << "'");
}

attribute const & get_attribute(environment const & env, name const & attr) {
    auto it = g_system_attributes->find(attr);
    if (it)
        return **it;
    it = g_user_attribute_ext->get_attributes(env).find(attr);
    if (it)
        return **it;
    throw exception(sstream() << "unknown attribute '" << attr << "'");
}

struct attr_record {
    name          m_decl;
    attr_data_ptr m_data; // no data -> deleted

    attr_record() {}
    attr_record(name decl, attr_data_ptr data):
            m_decl(decl), m_data(data) {}

    unsigned hash() const {
        unsigned h = m_decl.hash();
        if (m_data)
            h = ::lean::hash(h, m_data->hash());
        return h;
    }

    bool deleted() const {
        return !static_cast<bool>(m_data);
    }
};

struct attr_record_cmp {
    int operator()(attr_record const & r1, attr_record const & r2) const {
        // Adding a new record with different arguments should override the old one
        return quick_cmp(r1.m_decl, r2.m_decl);
    }
};

struct attr_entry {
    name        m_attr;
    unsigned    m_prio;
    attr_record m_record;

    attr_entry() {}
    attr_entry(name const & attr, unsigned prio, attr_record const & record):
            m_attr(attr), m_prio(prio), m_record(record) {}
};

typedef priority_queue<attr_record, attr_record_cmp> attr_records;
typedef name_map<pair<attr_records, unsigned>> attr_state;

struct attr_config {
    typedef attr_state state;
    typedef attr_entry entry;

    static unsigned get_entry_hash(entry const & e) {
        return hash(hash(e.m_attr.hash(), e.m_record.hash()), e.m_prio);
    }

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        attr_records m;
        unsigned h = 0;
        if (auto q = s.find(e.m_attr)) {
            m = q->first;
            h = q->second;
        }
        m.insert(e.m_record, e.m_prio);
        h = hash(h, get_entry_hash(e));
        s.insert(e.m_attr, mk_pair(m, h));
    }

    static const char * get_serialization_key() { return "ATTR"; }

    static void write_entry(serializer & s, entry const & e) {
        s << e.m_attr << e.m_prio << e.m_record.m_decl << e.m_record.deleted();
        if (!e.m_record.deleted()) {
            if (is_system_attribute(e.m_attr))
                get_system_attribute(e.m_attr).write_entry(s, *e.m_record.m_data);
            else
                // dispatch over the extension, since we can't call get_attribute without an env
                g_user_attribute_ext->write_entry(s, *e.m_record.m_data);
        }
    }

    static entry read_entry(deserializer & d) {
        entry e; bool deleted;
        d >> e.m_attr >> e.m_prio >> e.m_record.m_decl >> deleted;
        if (!deleted) {
            if (is_system_attribute(e.m_attr))
                e.m_record.m_data = get_system_attribute(e.m_attr).read_entry(d);
            else
                // dispatch over the extension, since we can't call get_attribute without an env
                e.m_record.m_data = g_user_attribute_ext->read_entry(d);
        }
        return e;
    }
};

template class scoped_ext<attr_config>;
typedef scoped_ext<attr_config> attribute_ext;

environment attribute::set_core(environment const & env, io_state const & ios, name const & n, unsigned prio,
                                attr_data_ptr data, bool persistent) const {
    auto env2 = attribute_ext::add_entry(env, ios, attr_entry(m_id, prio, attr_record(n, data)), persistent);
    if (m_after_set)
        env2 = m_after_set(env2, ios, n, prio, persistent);
    return env2;
}

environment attribute::unset(environment env, io_state const & ios, name const & n, bool persistent) const {
    if (m_before_unset) {
        env = m_before_unset(env, ios, n, persistent);
    } else {
        if (m_after_set)
            throw exception(sstream() << "cannot remove attribute [" << get_name() << "]");
    }
    return attribute_ext::add_entry(env, ios, attr_entry(m_id, get_prio(env, n), attr_record(n, {})), persistent);
}

attr_data_ptr attribute::get_untyped(environment const & env, name const & n) const {
    if (auto p = attribute_ext::get_state(env).find(m_id)) {
        attr_records const & records = p->first;
        if (auto record = records.get_key({n, {}}))
            return record->m_data;
    }
    return {};
}

unsigned attribute::get_prio(environment const & env, name const & n) const {
    if (auto p = attribute_ext::get_state(env).find(get_name())) {
        attr_records const & records = p->first;
        if (auto prio = records.get_prio({n, {}}))
            return prio.value();
    }
    return LEAN_DEFAULT_PRIORITY;
}

void attribute::get_instances(environment const & env, buffer<name> & r) const {
    if (auto p = attribute_ext::get_state(env).find(m_id)) {
        attr_records const & records = p->first;
        records.for_each([&](attr_record const & rec) {
                if (!rec.deleted())
                    r.push_back(rec.m_decl);
            });
    }
}

priority_queue<name, name_quick_cmp> attribute::get_instances_by_prio(environment const & env) const {
    priority_queue<name, name_quick_cmp> q;
    buffer<name> b;
    get_instances(env, b);
    for (auto const & n : b)
        q.insert(n, get_prio(env, n));
    return q;
}

attr_data_ptr attribute::parse_data(abstract_parser &) const {
    return get_default_attr_data();
}

void indices_attribute_data::parse(abstract_parser & p) {
    buffer<unsigned> vs;
    while (p.curr_is_numeral()) {
        auto pos = p.pos();
        unsigned v = p.parse_small_nat();
        if (v == 0)
            throw parser_error("invalid attribute parameter, value must be positive", pos);
        vs.push_back(v - 1);
    }
    m_idxs = to_list(vs);
}

void register_incompatible(char const * attr1, char const * attr2) {
    lean_assert(is_system_attribute(attr1));
    lean_assert(is_system_attribute(attr2));
    name s1(attr1);
    name s2(attr2);
    if (s1 > s2)
        std::swap(s1, s2);
    g_incomp->emplace_back(s1, s2);
}

void get_attributes(environment const & env, buffer<attribute const *> & r) {
    g_system_attributes->for_each([&](name const &, attribute_ptr const & attr) {
        r.push_back(&*attr);
    });
    g_user_attribute_ext->get_attributes(env).for_each([&](name const &, attribute_ptr const & attr) {
        r.push_back(&*attr);
    });
}

bool has_attribute(environment const & env, name const & attr, name const & d) {
    return get_attribute(env, attr).is_instance(env, d);
}

bool are_incompatible(attribute const & attr1, attribute const & attr2) {
    name s1(attr1.get_name());
    name s2(attr2.get_name());
    if (s1 > s2)
        std::swap(s1, s2);
    return std::find(g_incomp->begin(), g_incomp->end(), mk_pair(s1, s2)) != g_incomp->end();
}

void initialize_attribute_manager() {
    g_default_attr_data_ptr = new attr_data_ptr(new attr_data);
    g_system_attributes     = new name_map<attribute_ptr>();
    g_user_attribute_ext    = new user_attribute_ext();
    g_incomp                = new std::vector<pair<name, name>>();
    attribute_ext::initialize();
}

void finalize_attribute_manager() {
    attribute_ext::finalize();
    delete g_incomp;
    delete g_user_attribute_ext;
    delete g_system_attributes;
    delete g_default_attr_data_ptr;
}
}
