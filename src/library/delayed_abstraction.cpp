/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/freset.h"
#include "kernel/free_vars.h"
#include "kernel/abstract.h"
#include "kernel/abstract_type_context.h"
#include "library/replace_visitor.h"
#include "library/metavar_context.h"

namespace lean {
static name * g_delayed_abstraction_macro = nullptr;
/** \brief Delayed abstraction macro. This is an auxiliary temporary macro used by the tactic framework.
    It is used in the following kind of situation.
    Suppose we have a goal ?M

            CTX |- A -> B

    Then, we apply the intro tactic and create the new goal ?M'

            CTX, H : A |- B

    The intro tactic adds the following assignment to the metavariable context

           ?M := fun H : A, (delayed_abstraction[H] ?M' #0)

     The delayed_abstraction macro indicates that when ?M' is instantiated, we need to replace
     the local constant H with the de-bruijn index 0 at this assignment.
*/
class delayed_abstraction_macro : public macro_definition_cell {
    list<name> m_value;
public:
    delayed_abstraction_macro(list<name> const & v):m_value(v) {}
    virtual bool lt(macro_definition_cell const & d) const override {
        /** TODO(Leo): improve if needed */
        return length(m_value) < length(static_cast<delayed_abstraction_macro const &>(d).m_value);
    }
    virtual name get_name() const override { return *g_delayed_abstraction_macro; }
    virtual expr check_type(expr const & e, abstract_type_context & ctx, bool) const override {
        return ctx.infer(macro_arg(e, macro_num_args(e) - 1));
    }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const override {
        return none_expr();
    }
    virtual unsigned trust_level() const override { return 0; }
    virtual bool operator==(macro_definition_cell const & other) const override {
        delayed_abstraction_macro const * other_ptr = dynamic_cast<delayed_abstraction_macro const *>(&other);
        return other_ptr && m_value == other_ptr->m_value;
    }
    virtual unsigned hash() const override {
        /** TODO(Leo): improve if needed */
        return length(m_value);
    }
    virtual void write(serializer &) const override { lean_unreachable(); }
    list<name> const & get_names() const { return m_value; }
};

/** \brief Each name occurs only once. */
bool validate_delayed_abstraction(buffer<name> const & b) {
    for (unsigned i = 0; i < b.size(); i++) {
        for (unsigned j = i + 1; j < b.size(); j++) {
            if (b[i] == b[j])
                return false;
        }
    }
    return true;
}

bool validate_delayed_abstraction(list<name> const & s) {
    buffer<name> b;
    to_buffer(s, b);
    return validate_delayed_abstraction(b);
}

expr mk_delayed_abstraction_core(expr const & e, buffer<name> const & ns, buffer<expr> const & vs) {
    lean_assert(is_metavar(e));
    lean_assert(ns.size() == vs.size());
    buffer<expr> args;
    args.append(vs);
    args.push_back(e);
    return mk_macro(macro_definition(new delayed_abstraction_macro(to_list(ns))), args.size(), args.data());
}

bool is_delayed_abstraction(expr const & e) {
    return is_macro(e) && dynamic_cast<delayed_abstraction_macro const *>(macro_def(e).raw()) != nullptr;
}

void get_delayed_abstraction_info(expr const & e, buffer<name> & ns, buffer<expr> & es) {
    lean_assert(is_delayed_abstraction(e));
    to_buffer(static_cast<delayed_abstraction_macro const *>(macro_def(e).raw())->get_names(), ns);
    es.append(macro_num_args(e) - 1, macro_args(e));
}

expr const & get_delayed_abstraction_expr(expr const & e) {
    lean_assert(is_delayed_abstraction(e));
    return macro_arg(e, macro_num_args(e) - 1);
}

struct push_delayed_abstraction_fn : public replace_visitor {
    buffer<name>            m_ns;
    buffer<expr>            m_vs;
    buffer<unsigned>        m_deltas;
    /* If m_mctx is not nullptr we use it to filter unnecessary delayed abstractions. */
    metavar_context const * m_mctx{nullptr};

    void add_vidxs(int v) {
        for (unsigned & d : m_deltas)
            d += v;
    }

    void inc_vidxs() { add_vidxs(1); }
    void dec_vidxs() { add_vidxs(-1); }

    virtual expr visit_binding(expr const & e) override {
        expr new_d = visit(binding_domain(e));
        inc_vidxs();
        expr new_b;
        {
            freset<cache> reset_cache(m_cache);
            new_b = visit(binding_body(e));
        }
        dec_vidxs();
        return update_binding(e, new_d, new_b);
    }

    virtual expr visit_let(expr const & e) override {
        expr new_t = visit(let_type(e));
        expr new_v = visit(let_value(e));
        inc_vidxs();
        expr new_b;
        {
            freset<cache> reset_cache(m_cache);
            new_b = visit(let_body(e));
        }
        dec_vidxs();
        return update_let(e, new_t, new_v, new_b);
    }

    virtual expr visit_app(expr const & e) override {
        expr new_f = visit(app_fn(e));
        expr new_a = visit(app_arg(e));
        return update_app(e, new_f, new_a);
    }

    virtual expr visit_var(expr const & e) override {
        return e;
    }

    virtual expr visit_local(expr const & e) override {
        for (unsigned i = 0; i < m_ns.size(); i++) {
            if (m_ns[i] == mlocal_name(e)) {
                return lift_free_vars(m_vs[i], m_deltas[i]);
            }
        }
        return e;
    }

    virtual expr visit_macro(expr const & e) override {
        if (is_delayed_abstraction(e)) {
            unsigned sz = m_vs.size();
            buffer<name> new_ns;
            buffer<expr> new_vs;
            get_delayed_abstraction_info(e, new_ns, new_vs);
            lean_assert(new_ns.size() == new_vs.size());
            for (expr & v : new_vs)
                v = visit(v);
            m_ns.append(new_ns);
            m_vs.append(new_vs);
            m_deltas.resize(m_vs.size(), 0);
            expr r;
            {
                freset<cache> reset_cache(m_cache);
                r = visit(get_delayed_abstraction_expr(e));
            }
            m_ns.shrink(sz);
            m_vs.shrink(sz);
            m_deltas.shrink(sz);
            return r;
        } else {
            return replace_visitor::visit_macro(e);
        }
    }

    virtual expr visit_meta(expr const & e) override {
        if (m_mctx && is_metavar_decl_ref(e)) {
            if (optional<metavar_decl> decl = m_mctx->find_metavar_decl(e)) {
                /* We only include delayed substitutions that are in the scope of `e` */
                local_context const & lctx = decl->get_context();
                buffer<name> new_ns;
                buffer<expr> new_vs;
                for (unsigned i = 0; i < m_vs.size(); i++) {
                    if (lctx.find_local_decl(m_ns[i])) {
                        new_ns.push_back(m_ns[i]);
                        new_vs.push_back(lift_free_vars(m_vs[i], m_deltas[i]));
                    }
                }
                if (new_vs.empty())
                    return e;
                else
                    return mk_delayed_abstraction_core(e, new_ns, new_vs);
            }
        }
        /* Otherwise include all delayed substitutions */
        buffer<expr> new_vs;
        for (unsigned i = 0; i < m_vs.size(); i++) {
            new_vs.push_back(lift_free_vars(m_vs[i], m_deltas[i]));
        }
        return mk_delayed_abstraction_core(e, m_ns, new_vs);
    }

    push_delayed_abstraction_fn(buffer<name> const & ns, buffer<expr> const & vs) {
        lean_assert(ns.size() == vs.size());
        m_ns.append(ns);
        m_vs.append(vs);
        m_deltas.resize(vs.size(), 0);
    }

    push_delayed_abstraction_fn(buffer<name> const & ns, buffer<expr> const & vs, metavar_context const & mctx):
        push_delayed_abstraction_fn(ns, vs) {
        m_mctx = &mctx;
    }
};

expr push_delayed_abstraction(expr const & e) {
    lean_assert(is_delayed_abstraction(e));
    expr const & a = get_delayed_abstraction_expr(e);
    if (is_metavar(a)) {
        return e;
    } else {
        buffer<name> ns;
        buffer<expr> vs;
        get_delayed_abstraction_info(e, ns, vs);
        return push_delayed_abstraction_fn(ns, vs)(a);
    }
}

expr append_delayed_abstraction(expr const & e, buffer<name> const & ns, buffer<expr> const & vs) {
    return push_delayed_abstraction_fn(ns, vs)(e);
}

expr mk_delayed_abstraction(expr const & e, buffer<name> const & ns) {
    lean_assert(ns.size() > 0);
    buffer<expr> vs;
    unsigned sz = ns.size();
    for (unsigned i = 0; i < sz; i++) {
        vs.push_back(mk_var(sz - i - 1));
    }
    if (is_metavar(e)) {
        return mk_delayed_abstraction_core(e, ns, vs);
    } else {
        return push_delayed_abstraction_fn(ns, vs)(e);
    }
}

expr mk_delayed_abstraction(expr const & e, name const & n) {
    buffer<name> ns;
    ns.push_back(n);
    return mk_delayed_abstraction(e, ns);
}

expr mk_delayed_abstraction_with_locals(expr const & e, buffer<expr> const & ls) {
    lean_assert(is_metavar(e));
    lean_assert(std::all_of(ls.begin(), ls.end(), is_local));
    buffer<name> ns;
    for (expr const & l : ls)
        ns.push_back(mlocal_name(l));
    return mk_delayed_abstraction_core(e, ns, ls);
}

expr mk_delayed_abstraction(expr const & e, buffer<name> const & ns, buffer<expr> const & vs) {
    lean_assert(ns.size() > 0);
    lean_assert(ns.size() == vs.size());
    if (is_metavar(e)) {
        return mk_delayed_abstraction_core(e, ns, vs);
    } else {
        return push_delayed_abstraction_fn(ns, vs)(e);
    }
}

expr delayed_abstract_locals(metavar_context const & mctx, expr const & e, unsigned nlocals, expr const * locals) {
    lean_assert(std::all_of(locals, locals + nlocals, is_local));
    if (!has_expr_metavar(e))
        return abstract_locals(e, nlocals, locals);
    buffer<name> ns;
    buffer<expr> vs;
    for (unsigned i = 0; i < nlocals; i++) {
        ns.push_back(mlocal_name(locals[i]));
        vs.push_back(mk_var(nlocals - i - 1));
    }
    return push_delayed_abstraction_fn(ns, vs, mctx)(e);
}

void initialize_delayed_abstraction() {
    g_delayed_abstraction_macro = new name("delayed_abstraction");
}

void finalize_delayed_abstraction() {
    delete g_delayed_abstraction_macro;
}
}
