/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "pp.h"
#include "environment.h"
#include "scoped_set.h"
#include "for_each.h"
#include "instantiate.h"

namespace lean {
struct pp_fn {
    environment const *                  m_env;

    pp_fn(environment const * env):m_env(env) {}

    unsigned indent() const { return 2; }
    format pp_keyword(char const * k) { return highlight(format(k), format::format_color::ORANGE); }
    format pp_type_kwd() { return highlight(format("Type"), format::format_color::PINK); }
    format pp_eq_kwd() { return highlight(format(" = "), format::format_color::BLUE); }
    format pp_lambda_kwd() { return pp_keyword("\u03BB "); }
    format pp_lambda_sep() { return format(","); }
    format pp_pi_kwd() { return pp_keyword("\u03A0 "); }
    format pp_pi_sep() { return format(","); }
    format pp_type_arrow() { return format(" \u2192 "); }
    format pp_colon() { return format(" : "); }
    format pp_space() { return format(" "); }
    format pp_lp() { return format("("); }
    format pp_rp() { return format(")"); }

    bool is_atomic(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Var: case expr_kind::Constant: case expr_kind::Value: case expr_kind::Type:
            return true;
        case expr_kind::App: case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Eq: case expr_kind::Let:
            return false;
        }
        return false;
    }

    format pp_var(expr const & e) {
        unsigned vidx = var_idx(e);
        return compose(format("#"), format(vidx));
    }

    format pp_constant(expr const & e) {
        return ::lean::pp(const_name(e));
    }

    format pp_value(expr const & e) {
        return to_value(e).pp();
    }

    format pp_type(expr const & e) {
        if (e == Type()) {
            return pp_type_kwd();
        } else {
            return format{pp_type_kwd(), pp_space(), ::lean::pp(ty_level(e))};
        }
    }

    format pp_child(expr const & c) {
        if (is_atomic(c))
            return pp(c);
        else
            return format{pp_lp(), pp(c), pp_rp()};
    }

    format pp_eq(expr const & e) {
        return format{pp_child(eq_lhs(e)), pp_eq_kwd(), pp_child(eq_rhs(e))};
    }

    format pp_app(expr const & e) {
        // TODO: infix operators, implicit arguments

        // Prefix case
        format r = pp_child(arg(e, 0));
        for (unsigned i = 1; i < num_args(e); i++) {
            r += compose(line(), pp_child(arg(e, i)));
        }
        return group(nest(indent(), r));
    }

    format pp_arrow_body(expr const & e) {
        if (is_atomic(e) || is_arrow(e))
            return pp(e);
        else
            return pp_child(e);
    }

    struct is_used {};

    /** \brief Return true iff \c n is already used in body */
    bool used(name const & n, expr const & body) {
        auto visitor = [&](expr const & e, unsigned offset) -> void {
            if (is_constant(e)) {
                if (const_name(e) == n)
                    throw is_used();
            }
        };

        try {
            for_each_fn<decltype(visitor)> f(visitor);
            f(body);
            return false;
        } catch (is_used) {
            return true;
        }
    }

    format pp_bname(expr const & binder) {
        return ::lean::pp(abst_name(binder));
    }

    template<typename It>
    format pp_bnames(It const & begin, It const & end, bool use_line) {
        static_assert(std::is_same<typename std::iterator_traits<It>::value_type, expr>::value,
                      "pp_bnames takes an argument which is not an iterator containing expr.");
        auto it = begin;
        format r = pp_bname(*it);
        ++it;
        for (; it != end; ++it) {
            r += compose(use_line ? line() : pp_space(), pp_bname(*it));
        }
        return r;
    }

    expr collect_nested(expr const & e, expr_kind k, buffer<expr> & r) {
        if (e.kind() == k) {
            r.push_back(e);
            name const & n = abst_name(e);
            name n1    = n;
            unsigned i = 1;
            while (used(n1, abst_body(e))) {
                n1 = name(n, i);
                i++;
            }
            expr b = instantiate_with_closed(abst_body(e), mk_constant(n1));
            return collect_nested(b, k, r);
        } else {
            return e;
        }
    }

    format pp_abstraction(expr const & e) {
        if (is_arrow(e)) {
            return format{pp_child(abst_domain(e)), pp_type_arrow(), pp_arrow_body(abst_body(e))};
        } else {
            buffer<expr> nested;
            expr b = collect_nested(e, e.kind(), nested);
            lean_assert(b.kind() != e.kind());
            format head     = is_lambda(e) ? pp_lambda_kwd() : pp_pi_kwd();
            format body_sep = is_lambda(e) ? pp_lambda_sep() : pp_pi_sep();

            if (std::all_of(nested.begin(), nested.end(), [&](expr const & a) { return abst_domain(a) == abst_domain(e); })) {
                // Domain of all binders is the same
                format names = pp_bnames(nested.begin(), nested.end(), false);
                return group(nest(indent(), format{head, names, pp_colon(), pp(abst_domain(e)), body_sep, line(), pp(b)}));
            } else {
                auto it  = nested.begin();
                auto end = nested.end();
                // PP binders in blocks (names ... : type)
                bool first = true;
                format bindings;
                while (it != end) {
                    auto it2 = it;
                    ++it2;
                    while (it2 != end && abst_domain(*it2) == abst_domain(*it)) {
                        ++it2;
                    }
                    format block = group(nest(indent(), format{pp_lp(), pp_bnames(it, it2, true), pp_colon(), pp(abst_domain(*it)), pp_rp()}));
                    if (first) {
                        bindings = block;
                        first = false;
                    } else {
                        bindings += compose(line(), block);
                    }
                    it = it2;
                }
                return group(nest(indent(), format{head, group(bindings), body_sep, line(), pp(b)}));
            }
        }
    }

    format pp_let(expr const & e) {
        return format("TODO");
    }

    format pp(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Var:        return pp_var(e);
        case expr_kind::Constant:   return pp_constant(e);
        case expr_kind::Value:      return pp_value(e);
        case expr_kind::App:        return pp_app(e);
        case expr_kind::Lambda:
        case expr_kind::Pi:         return pp_abstraction(e);
        case expr_kind::Type:       return pp_type(e);
        case expr_kind::Eq:         return pp_eq(e);
        case expr_kind::Let:        return pp_let(e);
        }
        lean_unreachable();
        return format();
    }

    format operator()(expr const & e) {
        return pp(e);
    }
};
format pp(expr const & n) { return pp_fn(0)(n); }
format pp(expr const & n, environment const & env) { return pp_fn(&env)(n); }
}
