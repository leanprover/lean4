/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "util/priority_queue.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/scoped_ext.h"
#include "library/user_recursors.h"
#include "library/tmp_type_context.h"
#include "library/attribute_manager.h"
#include "library/blast/blast.h"
#include "library/blast/grinder/intro_elim_lemmas.h"

namespace lean {
static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct intro_elim_state {
    priority_queue<name, name_quick_cmp> m_elim_lemmas;
    priority_queue<name, name_quick_cmp> m_intro_lemmas;
};

typedef std::tuple<bool, unsigned, name> intro_elim_entry;

struct intro_elim_config {
    typedef intro_elim_entry entry;
    typedef intro_elim_state state;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        bool is_elim; unsigned prio; name n;
        std::tie(is_elim, prio, n) = e;
        if (is_elim) {
            s.m_elim_lemmas.insert(n, prio);
        } else {
            s.m_intro_lemmas.insert(n, prio);
        }
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        bool is_elim; unsigned prio; name n;
        std::tie(is_elim, prio, n) = e;
        s << is_elim << prio << n;
    }
    static entry read_entry(deserializer & d) {
        bool is_elim; unsigned prio; name n;
        d >> is_elim >> prio >> n;
        return entry(is_elim, prio, n);
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        bool is_elim; unsigned prio; name n;
        std::tie(is_elim, prio, n) = e;
        return some(hash(hash(n.hash(), prio), is_elim ? 17u : 31u));
    }
};

typedef scoped_ext<intro_elim_config> intro_elim_ext;

environment add_elim_lemma(environment const & env, io_state const & ios, name const & c, unsigned prio, name const & ns, bool persistent) {
    get_recursor_info(env, c);
    return intro_elim_ext::add_entry(env, ios, intro_elim_entry(true, prio, c), ns, persistent);
}

optional<name> get_intro_target(tmp_type_context & ctx, name const & c) {
    declaration const & d = ctx.env().get(c);
    buffer<level> us;
    unsigned num_us = d.get_num_univ_params();
    for (unsigned i = 0; i < num_us; i++)
        us.push_back(ctx.mk_uvar());
    // TODO(Leo): should we use relaxed_try_to_pi?
    expr type = ctx.try_to_pi(instantiate_type_univ_params(d, to_list(us)));
    while (is_pi(type)) {
        expr local = ctx.mk_tmp_local(binding_domain(type));
        type = ctx.try_to_pi(instantiate(binding_body(type), local));
    }
    expr const & fn = get_app_fn(type);
    if (is_constant(fn))
        return optional<name>(const_name(fn));
    else
        return optional<name>();
}

environment add_intro_lemma(environment const & env, io_state const & ios, name const & c, unsigned prio, name const & ns, bool persistent) {
    tmp_type_context ctx(env, ios.get_options());
    if (!get_intro_target(ctx, c))
        throw exception(sstream() << "invalid [intro] attribute for '" << c << "', head symbol of resulting type must be a constant");
    return intro_elim_ext::add_entry(env, ios, intro_elim_entry(false, prio, c), ns, persistent);
}

bool is_elim_lemma(environment const & env, name const & c) {
    return intro_elim_ext::get_state(env).m_elim_lemmas.contains(c);
}

bool is_intro_lemma(environment const & env, name const & c) {
    return intro_elim_ext::get_state(env).m_intro_lemmas.contains(c);
}

void get_elim_lemmas(environment const & env, buffer<name> & r) {
    return intro_elim_ext::get_state(env).m_elim_lemmas.to_buffer(r);
}

void get_intro_lemmas(environment const & env, buffer<name> & r) {
    return intro_elim_ext::get_state(env).m_intro_lemmas.to_buffer(r);
}

void initialize_intro_elim_lemmas() {
    g_class_name = new name("grinder");
    g_key        = new std::string("grinder");
    intro_elim_ext::initialize();

    register_prio_attribute("elim", "elimination rule that is eagerly applied by blast grinder",
                            add_elim_lemma,
                            is_elim_lemma,
                            [](environment const & env, name const & d) {
                                if (auto p = intro_elim_ext::get_state(env).m_elim_lemmas.get_prio(d))
                                    return *p;
                                else
                                    return LEAN_DEFAULT_PRIORITY;
                            });

    register_prio_attribute("intro!", "introduction rule that is eagerly applied by blast grinder",
                            add_intro_lemma,
                            is_intro_lemma,
                            [](environment const & env, name const & d) {
                                if (auto p = intro_elim_ext::get_state(env).m_intro_lemmas.get_prio(d))
                                    return *p;
                                else
                                    return LEAN_DEFAULT_PRIORITY;
                            });
}

void finalize_intro_elim_lemmas() {
    intro_elim_ext::finalize();
    delete g_key;
    delete g_class_name;
}

namespace blast {
head_map<gexpr> mk_intro_lemma_index() {
    head_map<gexpr> r;
    buffer<name> lemmas;
    blast_tmp_type_context ctx;
    get_intro_lemmas(env(), lemmas);
    unsigned i = lemmas.size();
    while (i > 0) {
        --i;
        ctx->clear();
        optional<name> target = get_intro_target(*ctx, lemmas[i]);
        if (!target) {
            lean_trace(name({"blast", "event"}),
                       tout() << "discarding [intro] lemma '" << lemmas[i] << "', failed to find target type\n";);
        } else {
            r.insert(head_index(*target), gexpr(lemmas[i]));
        }
    }
    return r;
}

name_map<name> mk_elim_lemma_index() {
    name_map<name> r;
    buffer<name> lemmas;
    get_elim_lemmas(env(), lemmas);
    for (name const & lemma : lemmas) {
        try {
            recursor_info info = get_recursor_info(env(), lemma);
            r.insert(info.get_type_name(), lemma);
        } catch (exception &) {
            lean_trace(name({"blast", "event"}),
                       tout() << "discarding [elim] lemma '" << lemma << "', failed to compute recursor information\n";);
        }
    }
    return r;
}
}}
