/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/user_recursors.h"
#include "library/constants.h"
#include "library/reducible.h"
#include "library/locals.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/class_instance_synth.h"

namespace lean {
class rec_opaque_converter : public default_converter {
    name m_I;
public:
    rec_opaque_converter(environment const & env, name const & I):default_converter(env), m_I(I) {}
    virtual bool is_opaque(declaration const & d) const {
        if (d.get_name() == m_I)
            return true;
        return default_converter::is_opaque(d);
    }
};

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
    constraint_seq        m_cs;
    expr                  m_ref; // reference expression for location information

    void assign(goal const & g, expr const & val) {
        ::lean::assign(m_subst, g, val);
    }

    /** \brief Split hyps into two "telescopes".
        - non_deps : hypotheses that do not depend on H nor its indices
        - deps     : hypotheses that depend on H or its indices (directly or indirectly)
    */
    void split_deps(buffer<expr> const & hyps, expr const & h, buffer<expr> const & indices,
                    buffer<expr> & non_deps, buffer<expr> & deps) {
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

    void throw_ill_formed_recursor(recursor_info const & rec_info) {
        throw tactic_exception(sstream() << "invalid 'induction' tactic, recursor '" << rec_info.get_name()
                               << "' is ill-formed");
    }

    expr mk_type_class_param(goal const & g, expr const & type) {
        bool use_local_insts = true;
        bool is_strict       = false;
        local_context ctx    = g.to_local_context();
        unifier_config cfg(m_ios.get_options());
        auto mc = mk_class_instance_elaborator(
            m_env, m_ios, ctx, m_ngen.next(), optional<name>(),
            use_local_insts, is_strict,
            some_expr(type), m_ref.get_tag(), cfg, nullptr);
        m_cs += mc.second;
        return mc.first;
    }

    expr mk_type_class_param(goal const & g, expr const & rec, recursor_info const & rec_info) {
        expr rec_type = m_tc.whnf(m_tc.infer(rec, m_cs), m_cs);
        if (!is_pi(rec_type)) {
            throw_ill_formed_recursor(rec_info);
        }
        return mk_type_class_param(g, binding_domain(rec_type));
    }

    goals apply_recursor(goal const & g, unsigned num_deps, expr const & h, expr const & h_type,
                         buffer<optional<expr>> const & params, buffer<expr> const & indices,
                         recursor_info const & rec_info) {
        expr const & g_type = g.get_type();
        level g_lvl         = sort_level(m_tc.ensure_type(g_type, m_cs));
        buffer<level> rec_lvls;
        expr const & I = get_app_fn(h_type);
        buffer<level> I_lvls;
        to_buffer(const_levels(I), I_lvls);
        bool found_g_lvl = false;
        for (unsigned idx : rec_info.get_universe_pos()) {
            if (idx == recursor_info::get_motive_univ_idx()) {
                rec_lvls.push_back(g_lvl);
                found_g_lvl = true;
            } else {
                if (idx >= I_lvls.size())
                    throw_ill_formed_recursor(rec_info);
                rec_lvls.push_back(I_lvls[idx]);
            }
        }
        if (!found_g_lvl && !is_zero(g_lvl)) {
            throw tactic_exception(sstream() << "invalid 'induction' tactic, recursor '" << rec_info.get_name()
                                   << "' can only eliminate into Prop");
        }
        expr rec    = mk_constant(rec_info.get_name(), to_list(rec_lvls));
        for (optional<expr> const & p : params) {
            if (p) {
                rec = mk_app(rec, *p);
            } else {
                rec = mk_app(rec, mk_type_class_param(g, rec, rec_info));
            }
        }
        expr motive = g_type;
        if (rec_info.has_dep_elim())
            motive  = Fun(h, motive);
        motive = Fun(indices, motive);
        rec      = mk_app(rec, motive);
        buffer<expr> hyps;
        g.get_hyps(hyps);
        buffer<expr> new_hyps;
        for (expr const & curr_h : hyps) {
            if (mlocal_name(curr_h) != mlocal_name(h) &&
                std::all_of(indices.begin(), indices.end(),
                            [&](expr const & idx) { return mlocal_name(curr_h) != mlocal_name(idx); })) {
                new_hyps.push_back(curr_h);
            }
        }
        expr rec_type          = m_tc.whnf(m_tc.infer(rec, m_cs), m_cs);
        unsigned curr_pos      = params.size() + 1 /* motive */;
        unsigned first_idx_pos = rec_info.get_first_index_pos();
        bool consumed_major    = false;
        buffer<goal> new_goals;
        list<bool> produce_motive = rec_info.get_produce_motive();
        while (is_pi(rec_type) && curr_pos < rec_info.get_num_args()) {
            if (first_idx_pos == curr_pos) {
                for (expr const & idx : indices) {
                    rec      = mk_app(rec, idx);
                    rec_type = m_tc.whnf(instantiate(binding_body(rec_type), idx), m_cs);
                    if (!is_pi(rec_type)) {
                        throw_ill_formed_recursor(rec_info);
                    }
                    curr_pos++;
                }
                rec      = mk_app(rec, h);
                rec_type = m_tc.whnf(instantiate(binding_body(rec_type), h), m_cs);
                consumed_major = true;
                curr_pos++;
            } else {
                if (!produce_motive)
                    throw_ill_formed_recursor(rec_info);
                buffer<expr> new_goal_hyps;
                new_goal_hyps.append(new_hyps);
                expr new_type  = binding_domain(rec_type);
                expr rec_arg;
                if (binding_info(rec_type).is_inst_implicit()) {
                    rec_arg   = mk_type_class_param(g, binding_domain(rec_type));
                } else {
                    unsigned arity = get_arity(new_type);
                    // introduce minor arguments
                    buffer<expr> minor_args;
                    for (unsigned i = 0; i < arity; i++) {
                        expr arg_type = head_beta_reduce(binding_domain(new_type));
                        name arg_name;
                        if (m_ids) {
                            arg_name = head(m_ids);
                            m_ids    = tail(m_ids);
                        } else {
                            arg_name = binding_name(new_type);
                        }
                        expr new_h = mk_local(m_ngen.next(), get_unused_name(arg_name, new_goal_hyps),
                                              arg_type, binder_info());
                        minor_args.push_back(new_h);
                        new_goal_hyps.push_back(new_h);
                        new_type = instantiate(binding_body(new_type), new_h);
                    }
                    new_type = head_beta_reduce(new_type);
                    buffer<expr> new_deps;
                    if (head(produce_motive)) {
                        // introduce deps
                        for (unsigned i = 0; i < num_deps; i++) {
                            if (!is_pi(new_type)) {
                                throw_ill_formed_recursor(rec_info);
                            }
                            expr dep_type = binding_domain(new_type);
                            expr new_dep  = mk_local(m_ngen.next(), get_unused_name(binding_name(new_type), new_goal_hyps),
                                                     dep_type, binder_info());
                            new_deps.push_back(new_dep);
                            new_goal_hyps.push_back(new_dep);
                            new_type = instantiate(binding_body(new_type), new_dep);
                        }
                    }
                    expr new_meta  = mk_app(mk_metavar(m_ngen.next(), Pi(new_goal_hyps, new_type)), new_goal_hyps);
                    goal new_g(new_meta, new_type);
                    new_goals.push_back(new_g);
                    rec_arg   = Fun(minor_args, Fun(new_deps, new_meta));
                }
                produce_motive = tail(produce_motive);
                rec            = mk_app(rec, rec_arg);
                rec_type       = m_tc.whnf(instantiate(binding_body(rec_type), rec_arg), m_cs);
                curr_pos++;
            }
        }
        if (!consumed_major) {
            throw_ill_formed_recursor(rec_info);
        }
        assign(g, rec);
        return to_list(new_goals);
    }

    optional<goals> execute(goal const & g, expr const & h, expr const & h_type, name const & rec) {
        try {
            recursor_info rec_info = get_recursor_info(m_env, rec);
            buffer<expr> h_type_args;
            get_app_args(h_type, h_type_args);
            buffer<optional<expr>> params;
            for (optional<unsigned> const & pos : rec_info.get_params_pos()) {
                if (!pos) {
                    params.push_back(none_expr());
                } else if (*pos >= h_type_args.size()) {
                    throw tactic_exception("invalid 'induction' tactic, major premise type is ill-formed");
                } else {
                    params.push_back(some_expr(h_type_args[*pos]));
                }
            }
            buffer<expr> indices;
            for (unsigned pos : rec_info.get_indices_pos()) {
                if (pos >= h_type_args.size()) {
                    throw tactic_exception("invalid 'induction' tactic, major premise type is ill-formed");
                }
                expr const & idx = h_type_args[pos];
                if (!is_local(idx)) {
                    throw tactic_exception(sstream() << "invalid 'induction' tactic, argument #"
                                           << pos+1 << " of major premise '" << h << "' type is not a variable");
                }
                for (unsigned i = 0; i < h_type_args.size(); i++) {
                    if (i != pos && is_local(h_type_args[i]) && mlocal_name(h_type_args[i]) == mlocal_name(idx)) {
                        throw tactic_exception(sstream() << "invalid 'induction' tactic, argument #"
                                               << pos+1 << " of major premise '" << h << "' type is an index, "
                                               << "but it occurs more than once");
                    }
                }
                indices.push_back(idx);
            }
            if (!rec_info.has_dep_elim() && depends_on(g.get_type(), h)) {
                throw tactic_exception(sstream() << "invalid 'induction' tactic, recursor '" << rec
                                       << "' does not support dependent elimination, but conclusion "
                                       << "depends on major premise '" << h << "'");
            }
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
            return optional<goals>(apply_recursor(new_g, deps.size(), h, h_type, params, indices, rec_info));
        } catch (exception const & ex) {
            throw tactic_exception(sstream() << "invalid 'induction' tactic, " << ex.what());
        }
    }

public:
    induction_tac(environment const & env, io_state const & ios, name_generator const & ngen,
                  type_checker & tc, substitution const & subst, name const & h_name,
                  optional<name> const & rec_name, list<name> const & ids,
                  bool throw_ex, expr const & ref):
        m_env(env), m_ios(ios), m_tc(tc), m_h_name(h_name), m_rec_name(rec_name), m_ids(ids),
        m_ngen(ngen), m_subst(subst), m_throw_ex(throw_ex), m_ref(ref) {
        m_standard = is_standard(env);
    }

    name_generator const & get_ngen() const { return m_ngen; }

    substitution const & get_subst() const { return m_subst; }

    constraint_seq get_new_constraints() const { return m_cs; }

    expr normalize_H_type(expr const & H) {
        lean_assert(is_local(H));
        if (m_rec_name) {
            recursor_info info = get_recursor_info(m_env, *m_rec_name);
            type_checker aux_tc(m_env, m_ngen.mk_child(),
                                std::unique_ptr<converter>(new rec_opaque_converter(m_env, info.get_type_name())));
            return aux_tc.whnf(mlocal_type(H)).first;
        } else {
            type_checker aux_tc(m_env, m_ngen.mk_child(),
                                std::unique_ptr<converter>(new has_rec_opaque_converter(m_env)));
            return aux_tc.whnf(mlocal_type(H)).first;
        }
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
                } else if (list<name> rs = get_recursors_for(m_env, const_name(I))) {
                    while (rs) {
                        name r = head(rs);
                        rs     = tail(rs);
                        if (!rs) {
                            // last one
                            return execute(g, H, H_type, r);
                        } else {
                            try {
                                flet<list<name>>     save_ids(m_ids, m_ids);
                                flet<constraint_seq> save_cs(m_cs, m_cs);
                                return execute(g, H, H_type, r);
                            } catch (exception &) {}
                        }
                    }
                }
            }
            throw tactic_exception(sstream() << "invalid 'induction' tactic, hypothesis '" << m_h_name
                                   << "' must have a type that is associated with a recursor");
        } catch (tactic_exception & ex) {
            if (m_throw_ex)
                throw;
            return optional<goals>();
        } catch (exception & ex) {
            if (m_throw_ex)
                throw tactic_exception(sstream() << "invalid 'induction' tactic, " << ex.what());
            return optional<goals>();
        }
    }
};

tactic induction_tactic(name const & H, optional<name> rec, list<name> const & ids, expr const & ref) {
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
        induction_tac tac(env, ios, ngen, *tc, ps.get_subst(), H, rec, ids, ps.report_failure(), ref);
        if (auto res = tac.execute(g)) {
            proof_state new_s(ps, append(*res, tail_gs), tac.get_subst(), tac.get_ngen());
            if (solve_constraints(env, ios, new_s, tac.get_new_constraints()))
                return some_proof_state(new_s);
            else
                return none_proof_state();
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
                         return induction_tactic(H, optional<name>(), to_list(ids.begin(), ids.end()), e);
                     } else {
                         return induction_tactic(H, optional<name>(cname), to_list(ids.begin(), ids.end()), e);
                     }
                 });
}
void finalize_induction_tactic() {
}
}
