/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/scoped_ext.h"
#include "library/attribute_manager.h"
#include "library/blast/forward/forward_lemmas.h"
#include "library/blast/forward/pattern.h"

namespace lean {
static name * g_name       = nullptr;
static std::string * g_key = nullptr;

struct forward_lemma {
    name      m_name;
    unsigned  m_priority;
    forward_lemma() {}
    forward_lemma(name const & n, unsigned p):m_name(n), m_priority(p) {}
};

struct forward_lemmas_config {
    typedef forward_lemma  entry;
    typedef forward_lemmas state;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        s.insert(e.m_name, e.m_priority);
    }

    static name const & get_class_name() {
        return *g_name;
    }

    static std::string const & get_serialization_key() {
        return *g_key;
    }

    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_name << e.m_priority;
    }

    static entry read_entry(deserializer & d) {
        name n; unsigned p;
        d >> n >> p;
        return entry(n, p);
    }

    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(hash(e.m_name.hash(), e.m_priority));
    }
};

template class scoped_ext<forward_lemmas_config>;
typedef scoped_ext<forward_lemmas_config> forward_lemmas_ext;

environment add_forward_lemma(environment const & env, name const & n, unsigned priority, name const & ns, bool persistent) {
    return forward_lemmas_ext::add_entry(env, get_dummy_ios(), forward_lemma(n, priority), ns, persistent);
}

bool is_forward_lemma(environment const & env, name const & n) {
    return forward_lemmas_ext::get_state(env).contains(n);
}

forward_lemmas get_forward_lemmas(environment const & env) {
    return forward_lemmas_ext::get_state(env);
}

void initialize_forward_lemmas() {
    g_name              = new name("forward");
    g_key               = new std::string("FWD");
    forward_lemmas_ext::initialize();

    register_prio_attribute("forward", "forward chaining",
                            [](environment const & env, io_state const & ios, name const & d, unsigned prio, name const & ns, bool persistent) {
                                mk_multipatterns(env, ios, d); // try to create patterns
                                return add_forward_lemma(env, d, prio, ns, persistent);
                            },
                            is_forward_lemma,
                            [](environment const & env, name const & n) {
                                if (auto prio = get_forward_lemmas(env).find(n))
                                    return *prio;
                                else
                                    return LEAN_DEFAULT_PRIORITY;
                            });
}

void finalize_forward_lemmas() {
    forward_lemmas_ext::finalize();
    delete g_name;
    delete g_key;
}
}
