/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/user_recursors.h"
#include "library/constants.h"
#include "library/reducible.h"
#include "library/locals.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
class has_rec_opaque_converter : public default_converter {
    has_recursors_pred m_pred;
public:
    has_rec_opaque_converter(environment const & env):default_converter(env), m_pred(env) {}
    virtual bool is_opaque(declaration const & d) const {
        if (m_pred(d.get_name()))
            return true;
        return default_converter::is_opaque(d);
    }
};

class induction_tac {
    environment const &   m_env;
    io_state const &      m_ios;
    type_checker &        m_tc;
    name                  m_h_name;
    optional<name>        m_rec_name;
    list<name>            m_ids;
    name_generator        m_ngen;
    substitution          m_subst;
    bool                  m_throw_ex;
    bool                  m_standard;

    void assign(goal const & g, expr const & val) {
        ::lean::assign(m_subst, g, val);
    }

    /** \brief Split hyps into two "telescopes".
        - non_deps : hypotheses that do not depend on H nor its indices
        - deps     : hypotheses that depend on H or its indices (directly or indirectly)
    */
    void split_deps(buffer<expr> const & hyps, expr const & h, buffer<expr> const & indices, buffer<expr> & non_deps, buffer<expr> & deps) {
        for (expr const & hyp : hyps) {
            if (hyp == h) {
                // we clear h
            } else if (std::find(indices.begin(), indices.end(), hyp) != indices.end()) {
                // hyp is an index
                non_deps.push_back(hyp);
            } else if (depends_on(hyp, h) || depends_on_any(hyp, indices) || depends_on_any(hyp, deps)) {
                deps.push_back(hyp);
            } else {
                non_deps.push_back(hyp);
            }
        }
    }

    bool validate_rec_info(goal const & g, expr const & h, expr const & h_type, recursor_info const & rec_info) {
        unsigned nindices = rec_info.get_num_indices();
        if (nindices == 0)
            return true;
        buffer<expr> args;
        get_app_args(h_type, args);
        if (rec_info.get_num_params() + nindices != args.size())
            return false;
        unsigned fidx = args.size() - nindices;
        for (unsigned i = fidx; i < args.size(); i++) {
            if (!is_local(args[i]))
                return false; // the indices must be local constants
            for (unsigned j = 0; j < i; j++) {
                if (is_local(args[j]) && mlocal_name(args[j]) == mlocal_name(args[i]))
                    return false; // the indices must be distinct local constants
            }
        }
        if (!rec_info.has_dep_elim() && depends_on(g.get_type(), h))
            return false;
        return true;
    }

    goals apply_recursor(goal const & g, expr const & h, expr const & h_type, recursor_info const & rec_info) {
        expr const & g_type = g.get_type();
        level g_lvl         = sort_level(m_tc.ensure_type(g_type).first);
        buffer<expr> I_args;
        expr const & I = get_app_args(h_type, I_args);
        buffer<expr> params;
        params.append(rec_info.get_num_params(), I_args.data());
        buffer<expr> indices;
        indices.append(rec_info.get_num_indices(), I_args.data() + params.size());
        levels rec_levels;
        if (auto lpos = rec_info.get_motive_univ_pos()) {
            buffer<level> ls;
            unsigned i = 0;
            for (level const & l : ls) {
                if (i == *lpos)
                    ls.push_back(g_lvl);
                ls.push_back(l);
                i++;
            }
            if (i == *lpos)
                ls.push_back(g_lvl);
            rec_levels = to_list(ls);
        } else {
            if (!is_zero(g_lvl)) {
                throw tactic_exception(sstream() << "invalid 'induction' tactic, recursor '" << rec_info.get_name()
                                       << "' can only eliminate into Prop");
            }
            rec_levels = const_levels(I);
        }
        expr rec = mk_constant(rec_info.get_name(), rec_levels);
        rec      = mk_app(rec, params);
        expr motive = g_type;
        if (rec_info.has_dep_elim())
            motive  = Fun(h, motive);
        motive = Fun(indices, motive);
        rec      = mk_app(rec, motive);

        // TODO(Leo):
        regular(m_env, m_ios) << ">> rec: " << rec << "\n";

        return goals();
    }

    optional<goals> execute(goal const & g, expr const & h, expr const & h_type, name const & rec) {
        try {
            recursor_info rec_info = get_recursor_info(m_env, rec);
            if (!validate_rec_info(g, h, h_type, rec_info)) {
                throw tactic_exception(sstream() << "invalid 'induction' tactic, indices occurring in the hypothesis '"
                                       << h << "' must be distinct variables");
            }
            unsigned nindices = rec_info.get_num_indices();
            buffer<expr> h_type_args;
            get_app_args(h_type, h_type_args);
            buffer<expr> indices;
            indices.append(nindices, h_type_args.end() - nindices);
            buffer<expr> hyps, non_deps, deps;
            g.get_hyps(hyps);
            split_deps(hyps, h, indices, non_deps, deps);
            buffer<expr> & new_hyps = non_deps;
            new_hyps.push_back(h);
            expr new_type = Pi(deps, g.get_type());
            expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(new_hyps, new_type)), new_hyps);
            goal new_g(new_meta, new_type);
            expr val      = mk_app(new_meta, deps);
            assign(g, val);
            regular(m_env, m_ios) << new_g << "\n";
            goals new_gs  = apply_recursor(new_g, h, h_type, rec_info);
            // TODO(Leo): finish
            return optional<goals>();
        } catch (exception const & ex) {
            throw tactic_exception(sstream() << "invalid 'induction' tactic, " << ex.what());
        }
    }

public:
    induction_tac(environment const & env, io_state const & ios, name_generator const & ngen,
                  type_checker & tc, substitution const & subst, name const & h_name,
                  optional<name> const & rec_name, list<name> const & ids,
                  bool throw_ex):
        m_env(env), m_ios(ios), m_tc(tc), m_h_name(h_name), m_rec_name(rec_name), m_ids(ids),
        m_ngen(ngen), m_subst(subst), m_throw_ex(throw_ex) {
        m_standard = is_standard(env);
    }

    name_generator const & get_ngen() const { return m_ngen; }

    substitution const & get_subst() const { return m_subst; }

    expr normalize_H_type(expr const & H) {
        lean_assert(is_local(H));
        type_checker aux_tc(m_env, m_ngen.mk_child(), std::unique_ptr<converter>(new has_rec_opaque_converter(m_env)));
        return aux_tc.whnf(mlocal_type(H)).first;
    }

    optional<goals> execute(goal const & g) {
        try {
            auto p = g.find_hyp(m_h_name);
            if (!p)
                throw tactic_exception(sstream() << "invalid 'induction' tactic, unknown hypothesis '" << m_h_name << "'");
            expr H      = p->first;
            expr H_type = normalize_H_type(H);
            expr I = get_app_fn(H_type);
            if (is_constant(I)) {
                if (m_rec_name) {
                    return execute(g, H, H_type, *m_rec_name);
                } else if (inductive::is_inductive_decl(m_env, const_name(I))) {
                    return execute(g, H, H_type, inductive::get_elim_name(const_name(I)));
                } else if (auto rs = get_recursors_for(m_env, const_name(I))) {
                    return execute(g, H, H_type, head(rs));
                }
            }
            throw tactic_exception(sstream() << "invalid 'induction' tactic, hypothesis '" << m_h_name
                                   << "' must have a type that is associated with a recursor");
        } catch (tactic_exception & ex) {
            if (m_throw_ex)
                throw;
            return optional<goals>();
        }
    }
};

tactic induction_tactic(name const & H, optional<name> rec, list<name> const & ids) {
    name rec1 = "unknown";
    if (rec) rec1 = *rec;
    std::cout << "induction: " << H << " " << rec1 << " " << ids << "\n";

    auto fn = [=](environment const & env, io_state const & ios, proof_state const & ps) -> optional<proof_state> {
        goals const & gs  = ps.get_goals();
        if (empty(gs)) {
            throw_no_goal_if_enabled(ps);
            return none_proof_state();
        }
        goal  g                          = head(gs);
        goals tail_gs                    = tail(gs);
        name_generator ngen              = ps.get_ngen();
        std::unique_ptr<type_checker> tc = mk_type_checker(env, ngen.mk_child());
        induction_tac tac(env, ios, ngen, *tc, ps.get_subst(), H, rec, ids, ps.report_failure());
        if (auto res = tac.execute(g)) {
            proof_state new_s(ps, append(*res, tail_gs), tac.get_subst(), tac.get_ngen());
            return some_proof_state(new_s);
        } else {
            return none_proof_state();
        }
    };
    return tactic01(fn);
}

void initialize_induction_tactic() {
    register_tac(name{"tactic", "induction"},
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     buffer<expr> args;
                     get_app_args(e, args);
                     if (args.size() != 3)
                         throw expr_to_tactic_exception(e, "invalid 'induction' tactic, insufficient number of arguments");
                     name H = tactic_expr_to_id(args[0], "invalid 'induction' tactic, argument must be an identifier");
                     buffer<name> ids;
                     get_tactic_id_list_elements(args[2], ids, "invalid 'induction' tactic, list of identifiers expected");
                     check_tactic_expr(args[1], "invalid 'induction' tactic, invalid argument");
                     expr rec = get_tactic_expr_expr(args[1]);
                     if (!is_constant(rec)) {
                         throw expr_to_tactic_exception(args[1], "invalid 'induction' tactic, constant expected");
                     }
                     name const & cname = const_name(rec);
                     if (cname == get_tactic_none_expr_name()) {
                         return induction_tactic(H, optional<name>(), to_list(ids.begin(), ids.end()));
                     } else {
                         return induction_tactic(H, optional<name>(cname), to_list(ids.begin(), ids.end()));
                     }
                 });
}
void finalize_induction_tactic() {
}
}
