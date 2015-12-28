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
#include "library/blast/backward/backward_lemmas.h"

namespace lean {
static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

typedef priority_queue<name, name_quick_cmp> backward_state;
typedef std::tuple<unsigned, name> backward_entry;

struct backward_config {
    typedef backward_entry entry;
    typedef backward_state state;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        unsigned prio; name n;
        std::tie(prio, n) = e;
        s.insert(n, prio);
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        unsigned prio; name n;
        std::tie(prio, n) = e;
        s << prio << n;
    }
    static entry read_entry(deserializer & d) {
        unsigned prio; name n;
        d >> prio >> n;
        return entry(prio, n);
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        unsigned prio; name n;
        std::tie(prio, n) = e;
        return some(hash(n.hash(), prio));
    }
};

typedef scoped_ext<backward_config> backward_ext;

static optional<head_index> get_backward_target(tmp_type_context & ctx, expr type) {
    while (is_pi(type)) {
        expr local = ctx.mk_tmp_local(binding_domain(type));
        type = ctx.try_to_pi(instantiate(binding_body(type), local));
    }
    expr fn = get_app_fn(ctx.whnf(type));
    if (is_constant(fn) || is_local(fn))
        return optional<head_index>(fn);
    else
        return optional<head_index>();
}

static optional<head_index> get_backward_target(tmp_type_context & ctx, name const & c) {
    declaration const & d = ctx.env().get(c);
    buffer<level> us;
    unsigned num_us = d.get_num_univ_params();
    for (unsigned i = 0; i < num_us; i++)
        us.push_back(ctx.mk_uvar());
    expr type = ctx.try_to_pi(instantiate_type_univ_params(d, to_list(us)));
    return get_backward_target(ctx, type);
}

environment add_backward_lemma(environment const & env, io_state const & ios, name const & c, unsigned prio, name const & ns, bool persistent) {
    tmp_type_context ctx(env, ios.get_options());
    auto index = get_backward_target(ctx, c);
    if (!index || index->kind() != expr_kind::Constant)
        throw exception(sstream() << "invalid [intro] attribute for '" << c << "', head symbol of resulting type must be a constant");
    return backward_ext::add_entry(env, ios, backward_entry(prio, c), ns, persistent);
}

bool is_backward_lemma(environment const & env, name const & c) {
    return backward_ext::get_state(env).contains(c);
}

void get_backward_lemmas(environment const & env, buffer<name> & r) {
    return backward_ext::get_state(env).to_buffer(r);
}

void initialize_backward_lemmas() {
    g_class_name = new name("backward");
    g_key        = new std::string("BWD");
    backward_ext::initialize();
    register_prio_attribute("intro", "introduction rule for backward chaining",
                            add_backward_lemma,
                            is_backward_lemma,
                            [](environment const & env, name const & d) {
                                if (auto p = backward_ext::get_state(env).get_prio(d))
                                    return *p;
                                else
                                    return LEAN_DEFAULT_PRIORITY;
                            });
}

void finalize_backward_lemmas() {
    backward_ext::finalize();
    delete g_key;
    delete g_class_name;
}

namespace blast {
unsigned backward_lemma_prio_fn::operator()(backward_lemma const & r) const {
    if (r.is_universe_polymorphic()) {
        name const & n = r.to_name();
        auto const & s = backward_ext::get_state(env());
        if (auto prio = s.get_prio(n))
            return *prio;
    }
    return LEAN_DEFAULT_PRIORITY;
}

void backward_lemma_index::init() {
    m_index.clear();
    buffer<name> lemmas;
    blast_tmp_type_context ctx;
    auto const & s = backward_ext::get_state(env());
    s.to_buffer(lemmas);
    unsigned i = lemmas.size();
    while (i > 0) {
        --i;
        ctx->clear();
        optional<head_index> target = get_backward_target(*ctx, lemmas[i]);
        if (!target || target->kind() != expr_kind::Constant) {
            lean_trace(name({"blast", "event"}),
                       tout() << "discarding [intro] lemma '" << lemmas[i] << "', failed to find target type\n";);
        } else {
            m_index.insert(*target, backward_lemma(lemmas[i]));
        }
    }
}

void backward_lemma_index::insert(expr const & href) {
    blast_tmp_type_context ctx;
    expr href_type = ctx->infer(href);
    if (optional<head_index> target = get_backward_target(*ctx, href_type)) {
        m_index.insert(*target, backward_lemma(gexpr(href)));
    }
}

void backward_lemma_index::erase(expr const & href) {
    blast_tmp_type_context ctx;
    expr href_type = ctx->infer(href);
    if (optional<head_index> target = get_backward_target(*ctx, href_type)) {
        m_index.erase(*target, backward_lemma(gexpr(href)));
    }
}

list<backward_lemma> backward_lemma_index::find(head_index const & h) const {
    if (auto r = m_index.find(h))
        return *r;
    else
        return list<backward_lemma>();
}
}}
