/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "util/list_fn.h"
#include "util/priority_queue.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/scoped_ext.h"
#include "library/user_recursors.h"
#include "library/type_context.h"
#include "library/attribute_manager.h"
#include "library/vm/vm.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/backward/backward_lemmas.h"

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

static optional<head_index> get_backward_target(type_context & ctx, expr type) {
    type_context::tmp_locals locals(ctx);
    while (is_pi(type)) {
        expr local  = locals.push_local_from_binding(type);
        type = ctx.try_to_pi(instantiate(binding_body(type), local));
    }
    expr fn = get_app_fn(type);
    if (is_constant(fn) || is_local(fn))
        return optional<head_index>(fn);
    else
        return optional<head_index>();
}

static optional<head_index> get_backward_target(type_context & ctx, name const & c) {
    declaration const & d = ctx.env().get(c);
    list<level> us = param_names_to_levels(d.get_univ_params());
    expr type      = ctx.try_to_pi(instantiate_type_univ_params(d, us));
    return get_backward_target(ctx, type);
}

environment add_backward_lemma(environment const & env, io_state const & ios, name const & c, unsigned prio, name const & ns, bool persistent) {
    aux_type_context ctx(env, ios.get_options());
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

unsigned backward_lemma_prio_fn::operator()(backward_lemma const & r) const {
    if (r.is_universe_polymorphic()) {
        name const & n = r.to_name();
        if (auto prio = m_prios.get_prio(n))
            return *prio;
    }
    return LEAN_DEFAULT_PRIORITY;
}

backward_lemma_index::backward_lemma_index(type_context & ctx):
    m_index(backward_lemma_prio_fn(backward_ext::get_state(ctx.env()))) {
    buffer<name> lemmas;
    auto const & s = backward_ext::get_state(ctx.env());
    s.to_buffer(lemmas);
    unsigned i = lemmas.size();
    while (i > 0) {
        --i;
        optional<head_index> target = get_backward_target(ctx, lemmas[i]);
        if (!target || target->kind() != expr_kind::Constant) {
            lean_trace(name({"tactic", "back_chaining"}),
                       tout() << "discarding [intro] lemma '" << lemmas[i] << "', failed to find target type\n";);
        } else {
            m_index.insert(*target, backward_lemma(lemmas[i]));
        }
    }
}

void backward_lemma_index::insert(type_context & ctx, expr const & href) {
    expr href_type = ctx.infer(href);
    if (optional<head_index> target = get_backward_target(ctx, href_type)) {
        m_index.insert(*target, backward_lemma(gexpr(href)));
    }
}

void backward_lemma_index::erase(type_context & ctx, expr const & href) {
    expr href_type = ctx.infer(href);
    if (optional<head_index> target = get_backward_target(ctx, href_type)) {
        m_index.erase(*target, backward_lemma(gexpr(href)));
    }
}

list<backward_lemma> backward_lemma_index::find(head_index const & h) const {
    if (auto r = m_index.find(h))
        return *r;
    else
        return list<backward_lemma>();
}

struct vm_backward_lemmas : public vm_external {
    backward_lemma_index m_val;
    vm_backward_lemmas(backward_lemma_index const & v):m_val(v) {}
    virtual void dealloc() override { this->~vm_backward_lemmas(); get_vm_allocator().deallocate(sizeof(vm_backward_lemmas), this); }
};

backward_lemma_index const & to_backward_lemmas(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_backward_lemmas*>(to_external(o)));
    return static_cast<vm_backward_lemmas*>(to_external(o))->m_val;
}

vm_obj to_obj(backward_lemma_index const & idx) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_backward_lemmas))) vm_backward_lemmas(idx));
}

vm_obj tactic_mk_backward_lemmas(vm_obj const & m, vm_obj const & s) {
    type_context ctx = mk_type_context_for(s, m);
    return mk_tactic_success(to_obj(backward_lemma_index(ctx)), to_tactic_state(s));
}

vm_obj tactic_backward_lemmas_insert(vm_obj const & m, vm_obj const & lemmas, vm_obj const & lemma, vm_obj const & s) {
    type_context ctx = mk_type_context_for(s, m);
    backward_lemma_index new_lemmas = to_backward_lemmas(lemmas);
    new_lemmas.insert(ctx, to_expr(lemma));
    return mk_tactic_success(to_obj(new_lemmas), to_tactic_state(s));
}

vm_obj tactic_backward_lemmas_find(vm_obj const & lemmas, vm_obj const & h, vm_obj const & s) {
    list<expr> r = map2<expr>(to_backward_lemmas(lemmas).find(head_index(to_expr(h))),
                              [](backward_lemma const & lemma) -> expr { return lemma.to_bare_expr(); });
    return mk_tactic_success(to_obj(r), to_tactic_state(s));
}

void initialize_backward_lemmas() {
    g_class_name = new name("backward");
    g_key        = new std::string("BWD");
    backward_ext::initialize();
    register_trace_class(name{"tactic", "back_chaining"});
    register_prio_attribute("intro", "introduction rule for backward chaining",
                            add_backward_lemma,
                            is_backward_lemma,
                            [](environment const & env, name const & d) {
                                if (auto p = backward_ext::get_state(env).get_prio(d))
                                    return *p;
                                else
                                    return LEAN_DEFAULT_PRIORITY;
                            });
    DECLARE_VM_BUILTIN(name({"tactic", "mk_back_lemmas_core"}),      tactic_mk_backward_lemmas);
    DECLARE_VM_BUILTIN(name({"tactic", "back_lemmas_insert_core"}),  tactic_backward_lemmas_insert);
    DECLARE_VM_BUILTIN(name({"tactic", "back_lemmas_find"}),         tactic_backward_lemmas_find);
}

void finalize_backward_lemmas() {
    backward_ext::finalize();
    delete g_key;
    delete g_class_name;
}
}
