/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <string>
#include "util/priority_queue.h"
#include "library/trace.h"
#include "library/scoped_ext.h"
#include "library/attribute_manager.h"
#include "library/vm/vm.h"
#include "library/tactic/simplifier/simp_extensions.h"

namespace lean {

static std::string * g_key = nullptr;

struct simp_ext_entry {
    unsigned m_prio;
    name m_head;
    name m_ext_name;

    simp_ext_entry(unsigned prio, name head, name ext_name):
        m_prio(prio), m_head(head), m_ext_name(ext_name) {}
};

struct simp_ext_record {
    name m_ext_name;
    unsigned m_ext_id;
    simp_ext_record() {}
    simp_ext_record(name ext_name, unsigned ext_id): m_ext_name(ext_name), m_ext_id(ext_id) {}
};

struct simp_ext_record_cmp {
    int operator()(simp_ext_record const & r1, simp_ext_record const & r2) const {
        // If the names are the same and the environments are compatible, then the ids must be the same as well
        return quick_cmp(r1.m_ext_name, r2.m_ext_name);
    }
};

typedef name_map<priority_queue<simp_ext_record, simp_ext_record_cmp>> simp_ext_state;

struct simp_ext_config {
    typedef simp_ext_entry entry;
    typedef simp_ext_state state;

    static void add_entry(environment const & env, io_state const &, state & s, entry const & e) {
        // TODO(dhs): better way to get the vm_decl?
        vm_state S(env);
        optional<vm_decl> ext_decl = S.get_decl(e.m_ext_name);
        if (!ext_decl) {
            throw exception(sstream() << "error in adding simplifier extension: no vm_decl for " << e.m_ext_name << "\n");
        }
        priority_queue<simp_ext_record, simp_ext_record_cmp> m;
        if (auto q = s.find(e.m_head)) {
            m = *q;
        }
        m.insert(simp_ext_record(e.m_ext_name, ext_decl->get_idx()), e.m_prio);
        s.insert(e.m_head, m);
    }

    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_prio << e.m_head << e.m_ext_name;
    }
    static entry read_entry(deserializer & d) {
        unsigned prio; name head; name ext_name;
        d >> prio >> head >> ext_name;
        return entry(prio, head, ext_name);
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(hash(e.m_head.hash(), hash(e.m_ext_name.hash(), e.m_prio)));
    }
};

typedef scoped_ext<simp_ext_config> simp_ext_ext;

environment add_simp_extension(environment const & env, io_state const & ios, name const & head, name const & simp_ext_name, unsigned prio, bool persistent) {
    return simp_ext_ext::add_entry(env, ios, simp_ext_entry(prio, head, simp_ext_name), persistent);
}

format pp_simp_extensions_for_head(priority_queue<simp_ext_record, simp_ext_record_cmp> const & q) {
    format fmt;
    q.for_each([&](simp_ext_record const & r) {
            fmt += format(r.m_ext_name);
            unsigned prio = *q.get_prio(r);
            if (prio != LEAN_DEFAULT_PRIORITY)
                fmt += space() + paren(format(prio));
            fmt += line();
        });
    return fmt;
}

format pp_simp_extensions(environment const & env) {
    simp_ext_state s = simp_ext_ext::get_state(env);
    format fmt;
    s.for_each([&](name const & head, priority_queue<simp_ext_record, simp_ext_record_cmp> const & q) {
            fmt += format("simplification extensions for ") + format(head) + line();
            fmt += pp_simp_extensions_for_head(q);
        });
    return fmt;
}

void get_simp_extensions_for(environment const & env, name const & head, buffer<unsigned> & ext_ids) {
    simp_ext_state s = simp_ext_ext::get_state(env);
    if (auto q = s.find(head)) {
        buffer<simp_ext_record> records;
        q->for_each([&](simp_ext_record const & r) {
                ext_ids.push_back(r.m_ext_id);
            });
    }
}

void initialize_simp_extensions() {
    g_key        = new std::string("SIMP_EXT");
    simp_ext_ext::initialize();
}

void finalize_simp_extensions() {
    simp_ext_ext::finalize();
    delete g_key;
}

}
