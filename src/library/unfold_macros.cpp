/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "kernel/type_checker.h"
#include "kernel/find_fn.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/unfold_macros.h"
#include "library/replace_visitor.h"
#include "library/generic_exception.h"

namespace lean {
class unfold_untrusted_macros_fn {
    typedef expr_bi_struct_map<expr> cache;

    type_checker m_tc;
    unsigned     m_trust_lvl;
    cache        m_cache;

    expr save_result(expr const & e, expr && r) {
        m_cache.insert(std::make_pair(e, r));
        return r;
    }

    expr visit_macro(expr const & e) {
        buffer<expr> new_args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            new_args.push_back(visit(macro_arg(e, i)));
        auto def = macro_def(e);
        expr r = update_macro(e, new_args.size(), new_args.data());
        if (def.trust_level() >= m_trust_lvl) {
            if (optional<expr> new_r = m_tc.expand_macro(r)) {
                return *new_r;
            } else {
                throw_generic_exception("failed to expand macro", e);
            }
        } else {
            return r;
        }
    }

    expr visit_app(expr const & e) {
        expr new_f = visit(app_fn(e));
        expr new_v = visit(app_arg(e));
        return update_app(e, new_f, new_v);
    }

    expr visit_binding(expr e) {
        expr_kind k = e.kind();
        buffer<expr>  es;
        buffer<expr>  ls;
        while (e.kind() == k) {
            expr d = visit(instantiate_rev(binding_domain(e), ls.size(), ls.data()));
            expr l = mk_local(m_tc.mk_fresh_name(), binding_name(e), d, binding_info(e));
            ls.push_back(l);
            es.push_back(e);
            e = binding_body(e);
        }
        e = visit(instantiate_rev(e, ls.size(), ls.data()));
        expr r = abstract_locals(e, ls.size(), ls.data());
        while (!ls.empty()) {
            expr d = mlocal_type(ls.back());
            ls.pop_back();
            d = abstract_locals(d, ls.size(), ls.data());
            r = update_binding(es.back(), d, r);
            es.pop_back();
        }
        return r;
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Sort:  case expr_kind::Constant:
        case expr_kind::Var:   case expr_kind::Meta:
        case expr_kind::Local:
            return e;
        default:
            break;
        }

        check_system("unfold macros");
        auto it = m_cache.find(e);
        if (it != m_cache.end())
            return it->second;

        switch (e.kind()) {
        case expr_kind::Sort:  case expr_kind::Constant:
        case expr_kind::Var:   case expr_kind::Meta:
        case expr_kind::Local:
            lean_unreachable();
        case expr_kind::Macro:
            return save_result(e, visit_macro(e));
        case expr_kind::App:
            return save_result(e, visit_app(e));
        case expr_kind::Lambda: case expr_kind::Pi:
            return save_result(e, visit_binding(e));
        }
        lean_unreachable();
    }

public:
    unfold_untrusted_macros_fn(environment const & env, unsigned lvl):
        m_tc(env), m_trust_lvl(lvl) {}

    expr operator()(expr const & e) { return visit(e); }
};

static bool contains_untrusted_macro(unsigned trust_lvl, expr const & e) {
    if (trust_lvl > LEAN_BELIEVER_TRUST_LEVEL)
        return false;
    return static_cast<bool>(find(e, [&](expr const & e, unsigned) {
                return is_macro(e) && macro_def(e).trust_level() >= trust_lvl;
            }));
}

expr unfold_untrusted_macros(environment const & env, expr const & e, unsigned trust_lvl) {
    if (contains_untrusted_macro(trust_lvl, e)) {
        return unfold_untrusted_macros_fn(env, trust_lvl)(e);
    } else {
        return e;
    }
}

expr unfold_untrusted_macros(environment const & env, expr const & e) {
    return unfold_untrusted_macros(env, e, env.trust_lvl());
}

expr unfold_all_macros(environment const & env, expr const & e) {
    return unfold_untrusted_macros(env, e, 0);
}

static bool contains_untrusted_macro(unsigned trust_lvl, declaration const & d) {
    if (trust_lvl > LEAN_BELIEVER_TRUST_LEVEL)
        return false;
    if (contains_untrusted_macro(trust_lvl, d.get_type()))
        return true;
    return (d.is_definition() || d.is_theorem()) && contains_untrusted_macro(trust_lvl, d.get_value());
}

declaration unfold_untrusted_macros(environment const & env, declaration const & d, unsigned trust_lvl) {
    if (contains_untrusted_macro(trust_lvl, d)) {
        expr new_t = unfold_untrusted_macros(env, d.get_type(), trust_lvl);
        if (d.is_theorem()) {
            expr new_v = unfold_untrusted_macros(env, d.get_value(), trust_lvl);
            return mk_theorem(d.get_name(), d.get_univ_params(), new_t, new_v,
                              d.get_height());
        } else if (d.is_definition()) {
            expr new_v = unfold_untrusted_macros(env, d.get_value(), trust_lvl);
            return mk_definition(d.get_name(), d.get_univ_params(), new_t, new_v,
                                 d.get_height(), d.use_conv_opt());
        } else if (d.is_axiom()) {
            return mk_axiom(d.get_name(), d.get_univ_params(), new_t);
        } else if (d.is_constant_assumption()) {
            return mk_constant_assumption(d.get_name(), d.get_univ_params(), new_t);
        } else {
            lean_unreachable();
        }
    } else {
        return d;
    }
}

declaration unfold_untrusted_macros(environment const & env, declaration const & d) {
    return unfold_untrusted_macros(env, d, env.trust_lvl());
}

declaration unfold_all_macros(environment const & env, declaration const & d) {
    return unfold_untrusted_macros(env, d, 0);
}
}
