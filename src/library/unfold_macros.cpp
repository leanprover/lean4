/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "kernel/find_fn.h"
#include "kernel/expr_maps.h"
#include "library/type_context.h"
#include "library/unfold_macros.h"
#include "library/replace_visitor_with_tc.h"
#include "library/exception.h"

/* If the trust level of all macros is < LEAN_BELIEVER_TRUST_LEVEL,
   then we skip the unfold_untrusted_macros potentially expensive step.
   The following definition is commented because we are currently testing the AC macros. */
// #define LEAN_ALL_MACROS_HAVE_SMALL_TRUST_LVL

namespace lean {
class unfold_untrusted_macros_fn : public replace_visitor_with_tc {
    optional<unsigned> m_trust_lvl;

    virtual expr visit_macro(expr const & e) override {
        buffer<expr> new_args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            new_args.push_back(visit(macro_arg(e, i)));
        auto def = macro_def(e);
        expr r = update_macro(e, new_args.size(), new_args.data());
        if (!m_trust_lvl || def.trust_level() >= *m_trust_lvl) {
            if (optional<expr> new_r = m_ctx.expand_macro(r)) {
                return visit(*new_r);
            } else {
                throw generic_exception(e, "failed to expand macro");
            }
        } else {
            return r;
        }
    }

public:
    unfold_untrusted_macros_fn(type_context_old & ctx, optional<unsigned> const & lvl):
        replace_visitor_with_tc(ctx), m_trust_lvl(lvl) {}
};

static bool contains_untrusted_macro(unsigned trust_lvl, expr const & e) {
#if defined(LEAN_ALL_MACROS_HAVE_SMALL_TRUST_LVL)
    if (trust_lvl > LEAN_BELIEVER_TRUST_LEVEL) return false;
#endif
    return static_cast<bool>(find(e, [&](expr const & e, unsigned) {
                return is_macro(e) && macro_def(e).trust_level() >= trust_lvl;
            }));
}

expr unfold_untrusted_macros(environment const & env, expr const & e, optional<unsigned> const & trust_lvl) {
    if (!trust_lvl || contains_untrusted_macro(*trust_lvl, e)) {
        type_context_old ctx(env, transparency_mode::All);
        return unfold_untrusted_macros_fn(ctx, trust_lvl)(e);
    } else {
        return e;
    }
}

expr unfold_untrusted_macros(environment const & env, expr const & e) {
    return unfold_untrusted_macros(env, e, optional<unsigned>(env.trust_lvl()));
}

expr unfold_all_macros(environment const & env, expr const & e) {
    return unfold_untrusted_macros(env, e, {});
}

static bool contains_untrusted_macro(unsigned trust_lvl, declaration const & d) {
#if defined(LEAN_ALL_MACROS_HAVE_SMALL_TRUST_LVL)
    if (trust_lvl > LEAN_BELIEVER_TRUST_LEVEL) return false;
#endif
    if (!d.is_trusted())
        return false;
    if (contains_untrusted_macro(trust_lvl, d.get_type()))
        return true;
    return (d.is_definition() || d.is_theorem()) && contains_untrusted_macro(trust_lvl, d.get_value());
}

declaration unfold_untrusted_macros(environment const & env, declaration const & d, optional<unsigned> const & trust_lvl) {
    if (!trust_lvl || contains_untrusted_macro(*trust_lvl, d)) {
        expr new_t = unfold_untrusted_macros(env, d.get_type(), trust_lvl);
        if (d.is_theorem()) {
            expr new_v = unfold_untrusted_macros(env, d.get_value(), trust_lvl);
            return mk_theorem(d.get_name(), d.get_univ_params(), new_t, new_v);
        } else if (d.is_definition()) {
            expr new_v = unfold_untrusted_macros(env, d.get_value(), trust_lvl);
            return mk_definition(d.get_name(), d.get_univ_params(), new_t, new_v,
                                 d.get_hints(), d.is_trusted());
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
    return unfold_untrusted_macros(env, d, optional<unsigned>(env.trust_lvl()));
}

declaration unfold_all_macros(environment const & env, declaration const & d) {
    return unfold_untrusted_macros(env, d, {});
}
}
