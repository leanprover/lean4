/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract_type_context.h"
#include "library/replace_visitor.h"

namespace lean {
static name * g_lazy_abstraction_macro = nullptr;
/** \brief Lazy abstraction macro. This is an auxiliary temporary macro used by the tactic framework.
    It is used in the following kind of situation.
    Suppose we have a goal ?M

            CTX |- A -> B

    Then, we apply the intro tactic and create the new goal ?M'

            CTX, H : A |- B

    The intro tactic adds the following assignment to the metavariable context

           ?M := fun H : A, lazy_abstraction[(H, 0)] ?M'

     The lazy_abstraction macro indicates that when ?M' is instantiated, we need to replace
     the local constant H with the de-bruijn index 0 at this assignment.
*/
class lazy_abstraction_macro : public macro_definition_cell {
    list<pair<name, unsigned>> m_value;
public:
    lazy_abstraction_macro(list<pair<name, unsigned>> const & v):m_value(v) {}
    virtual bool lt(macro_definition_cell const & d) const {
        /** TODO(Leo): improve if needed */
        return length(m_value) < length(static_cast<lazy_abstraction_macro const &>(d).m_value);
    }
    virtual name get_name() const { return *g_lazy_abstraction_macro; }
    virtual expr check_type(expr const & e, abstract_type_context & ctx, bool) const {
        return ctx.infer(macro_arg(e, 0));
    }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const {
        return none_expr();
    }
    virtual unsigned trust_level() const { return 0; }
    virtual bool operator==(macro_definition_cell const & other) const {
        lazy_abstraction_macro const * other_ptr = dynamic_cast<lazy_abstraction_macro const *>(&other);
        return other_ptr && m_value == other_ptr->m_value;
    }
    virtual unsigned hash() const {
        /** TODO(Leo): improve if needed */
        return length(m_value);
    }
    virtual void write(serializer &) const { lean_unreachable(); }
    list<pair<name, unsigned>> const & get_value() const { return m_value; }
};

/** \brief Each name occurs only once. Each unsigned occurs only once. */
static bool validate_lazy_abstraction(buffer<pair<name, unsigned>> const & b) {
    for (unsigned i = 0; i < b.size(); i++) {
        for (unsigned j = i + 1; j < b.size(); j++) {
            if (b[i].first == b[j].first)
                return false;
            if (b[i].second == b[j].second)
                return false;
        }
    }
    return true;
}

static bool validate_lazy_abstraction(list<pair<name, unsigned>> const & s) {
    buffer<pair<name, unsigned>> b;
    to_buffer(s, b);
    return validate_lazy_abstraction(b);
}

expr mk_lazy_abstraction(list<pair<name, unsigned>> const & s, expr const & e) {
    lean_assert(!empty(s));
    lean_assert(validate_lazy_abstraction(s));
    return mk_macro(macro_definition(new lazy_abstraction_macro(s)), 1, &e);
}

expr mk_lazy_abstraction(name const & n, expr const & e) {
    return mk_lazy_abstraction(to_list(mk_pair(n, 0u)), e);
}

bool is_lazy_abstraction(expr const & e) {
    return is_macro(e) && dynamic_cast<lazy_abstraction_macro const *>(macro_def(e).raw()) != nullptr;
}

list<pair<name, unsigned>> const & get_lazy_abstraction_info(expr const & e) {
    lean_assert(is_lazy_abstraction(e));
    return static_cast<lazy_abstraction_macro const *>(macro_def(e).raw())->get_value();
}

expr const & get_lazy_abstraction_expr(expr const & e) {
    lean_assert(is_lazy_abstraction(e));
    return macro_arg(e, 0);
}

struct push_lazy_abstraction_fn : public replace_visitor {
    buffer<pair<name, unsigned>> m_s;

    void add_vidxs(int v) {
        for (pair<name, unsigned> & p : m_s) {
            lean_assert(static_cast<int>(p.second) + v >= 0);
            p.second += v;
        }
        m_cache.clear();
    }

    void inc_vidxs() { add_vidxs(1); }
    void dec_vidxs() { add_vidxs(-1); }

    expr visit_binding(expr const & e) override {
        expr new_d = visit(binding_domain(e));
        inc_vidxs();
        expr new_b = visit(binding_body(e));
        dec_vidxs();
        return update_binding(e, new_d, new_b);
    }

    expr visit_let(expr const & e) override {
        expr new_t = visit(let_type(e));
        expr new_v = visit(let_value(e));
        inc_vidxs();
        expr new_b = visit(let_body(e));
        dec_vidxs();
        return update_let(e, new_t, new_v, new_b);
    }

    expr visit_app(expr const & e) override {
        expr new_f = visit(app_fn(e));
        expr new_a = visit(app_arg(e));
        return update_app(e, new_f, new_a);
    }

    bool not_in_s(unsigned vidx) const {
        return std::all_of(m_s.begin(), m_s.end(),
                           [&](pair<name, unsigned> const & p) { return p.second != vidx; });
    }

    expr visit_var(expr const & e) override {
        lean_assert(not_in_s(var_idx(e)));
        return e;
    }

    expr visit_local(expr const & e) override {
        for (pair<name, unsigned> const & p : m_s) {
            if (p.first == mlocal_name(e))
                return mk_var(p.second);
        }
        return e;
    }

    expr visit_macro(expr const & e) override {
        if (is_lazy_abstraction(e)) {
            unsigned sz = m_s.size();
            to_buffer(get_lazy_abstraction_info(e), m_s);
            m_cache.clear();
            lean_assert(validate_lazy_abstraction(m_s));
            expr r = visit(get_lazy_abstraction_expr(e));
            m_s.shrink(sz);
            m_cache.clear();
            return r;
        } else {
            return replace_visitor::visit_macro(e);
        }
    }

    expr visit_meta(expr const & e) override {
        return mk_lazy_abstraction(to_list(m_s), e);
    }

    push_lazy_abstraction_fn(list<pair<name, unsigned>> const & ls) {
        to_buffer(ls, m_s);
        lean_assert(validate_lazy_abstraction(m_s));
    }
};

expr push_lazy_abstraction(expr const & e) {
    lean_assert(is_lazy_abstraction(e));
    expr const & a = get_lazy_abstraction_expr(e);
    if (is_metavar(a))
        return e;
    else
        return push_lazy_abstraction_fn(get_lazy_abstraction_info(e))(a);
}

void initialize_lazy_abstraction() {
    g_lazy_abstraction_macro = new name("lazy_abstraction");
}

void finalize_lazy_abstraction() {
    delete g_lazy_abstraction_macro;
}
}
