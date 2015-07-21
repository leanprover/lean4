/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "library/util.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/relation_tactics.h"
#include "library/simplifier/simp_tactic.h"

namespace lean {
expr const * g_simp_tactic = nullptr;

expr mk_simp_tactic_expr(buffer<expr> const & ls, buffer<name> const & ns,
                         buffer<name> const & ex, optional<expr> const & pre_tac,
                         location const & loc) {
    expr e  = mk_expr_list(ls.size(), ls.data());
    expr n  = ids_to_tactic_expr(ns);
    expr x  = ids_to_tactic_expr(ex);
    expr t;
    if (pre_tac) {
        t = mk_app(mk_constant(get_option_some_name()), *pre_tac);
    } else {

        t = mk_constant(get_option_none_name());
    }
    expr l = mk_location_expr(loc);
    expr r = mk_app({*g_simp_tactic, e, n, x, t, l});
    return r;
}

class simp_tactic_fn {
    environment      m_env;
    io_state         m_ios;
    name_generator   m_ngen;
    optional<tactic> m_tactic;

public:
    simp_tactic_fn(environment const & env, io_state const & ios, name_generator && ngen,
                   buffer<expr> const & /* ls */, buffer<name> const & /* ns */, buffer<name> const & /* ex */,
                   optional<tactic> const & tac):m_env(env), m_ios(ios), m_ngen(ngen), m_tactic(tac) {
    }

    pair<goal, substitution> operator()(goal const & g, location const & /* loc */, substitution const & s) {
        // TODO(Leo)
        return mk_pair(g, s);
    }
};

tactic mk_simp_tactic(elaborate_fn const & elab, buffer<expr> const & ls, buffer<name> const & ns,
                      buffer<name> const & ex, optional<tactic> tac, location const & loc) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
            goals const & gs = s.get_goals();
            if (empty(gs)) {
                throw_no_goal_if_enabled(s);
                return proof_state_seq();
            }
            goal const & g = head(gs);
            name_generator new_ngen  = s.get_ngen();
            substitution   new_subst = s.get_subst();
            buffer<expr>   new_ls;
            for (expr const & l : ls) {
                expr new_l; constraints cs;
                bool report_unassigned = true;
                std::tie(new_l, new_subst, cs) = elab(g, new_ngen.mk_child(), l, none_expr(), new_subst, report_unassigned);
                if (cs)
                    throw_tactic_exception_if_enabled(s, "invalid 'simp' tactic, fail to resolve generated constraints");
                new_ls.push_back(new_l);
            }
            simp_tactic_fn simp(env, ios, new_ngen.mk_child(), new_ls, ns, ex, tac);
            pair<goal, substitution> r = simp(g, loc, new_subst);
            goal new_g = r.first;
            new_subst  = r.second;
            proof_state new_s(s, cons(new_g, tail(gs)), new_subst, new_ngen);

            bool fail_if_metavars = true;
            tactic post_tac = try_tactic(refl_tactic(elab, fail_if_metavars));
            // TODO(Leo): remove now_tactic
            post_tac = then(post_tac, now_tactic());
            return post_tac(env, ios, new_s);
        });
}

void initialize_simp_tactic() {
    name simp_name{"tactic", "simp_tac"};
    g_simp_tactic = new expr(mk_constant(simp_name));

    register_tac(simp_name,
                 [](type_checker & tc, elaborate_fn const & elab, expr const & e, pos_info_provider const * p) {
                     buffer<expr> args;
                     get_app_args(e, args);
                     if (args.size() != 5)
                         throw expr_to_tactic_exception(e, "invalid 'simp' tactic, incorrect number of arguments");
                     buffer<expr> lemmas;
                     get_tactic_expr_list_elements(args[0], lemmas, "invalid 'simp' tactic, invalid argument #1");
                     buffer<name> ns, ex;
                     get_tactic_id_list_elements(args[1], ns, "invalid 'simp' tactic, invalid argument #2");
                     get_tactic_id_list_elements(args[2], ex, "invalid 'simp' tactic, invalid argument #3");
                     optional<tactic> tac;
                     expr A, t;
                     if (is_some(args[3], A, t)) {
                         tac = expr_to_tactic(tc, elab, t, p);
                     } else if (is_none(args[3], A)) {
                         // do nothing
                     } else {
                         throw expr_to_tactic_exception(e, "invalid 'simp' tactic, invalid argument #4");
                     }
                     check_tactic_expr(args[4], "invalid 'simp' tactic, invalid argument #5");
                     expr loc_expr = get_tactic_expr_expr(args[4]);
                     if (!is_location_expr(loc_expr))
                         throw expr_to_tactic_exception(e, "invalid 'simp' tactic, invalid argument #5");
                     location loc = get_location_expr_location(loc_expr);
                     return mk_simp_tactic(elab, lemmas, ns, ex, tac, loc);
                 });
}

void finalize_simp_tactic() {
    delete g_simp_tactic;
}
}
