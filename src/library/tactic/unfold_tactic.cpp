/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/constants.h"
#include "library/replace_visitor.h"
#include "library/tactic/unfold_tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
class unfold_core_fn : public replace_visitor {
protected:
    bool m_unfolded;

    virtual expr visit_app(expr const & e) {
        expr const & f = get_app_fn(e);
        if (is_constant(f)) {
            expr new_f = visit(f);
            bool modified = new_f != f;
            buffer<expr> new_args;
            get_app_args(e, new_args);
            for (unsigned i = 0; i < new_args.size(); i++) {
                expr arg    = new_args[i];
                new_args[i] = visit(arg);
                if (!modified && new_args[i] != arg)
                    modified = true;
            }
            if (is_lambda(new_f)) {
                std::reverse(new_args.begin(), new_args.end());
                return apply_beta(new_f, new_args.size(), new_args.data());
            } else if (modified) {
                return mk_app(new_f, new_args);
            } else {
                return e;
            }
        } else {
            return replace_visitor::visit_app(e);
        }
    }
public:
    unfold_core_fn():m_unfolded(false) {}
    bool unfolded() const { return m_unfolded; }
};

class unfold_fn : public unfold_core_fn {
protected:
    name const &              m_name;
    level_param_names const & m_ps;
    expr const &              m_def;

    virtual expr visit_constant(expr const & c) {
        if (const_name(c) == m_name) {
            m_unfolded = true;
            return instantiate_univ_params(m_def, m_ps, const_levels(c));
        } else {
            return c;
        }
    }

public:
    unfold_fn(name const & n, level_param_names const & ps, expr const & d):m_name(n), m_ps(ps), m_def(d) {}
};

class unfold_all_fn : public unfold_core_fn {
protected:
    environment m_env;

    virtual expr visit_constant(expr const & c) {
        optional<declaration> d = m_env.find(const_name(c));
        if (d && d->is_definition() && (!d->is_opaque() || d->get_module_idx() == 0)) {
            m_unfolded = true;
            return instantiate_value_univ_params(*d, const_levels(c));
        } else {
            return c;
        }
    }

public:
    unfold_all_fn(environment const & env):m_env(env) {}
};

optional<proof_state> unfold_tactic_core(unfold_core_fn & fn, proof_state const & s) {
    bool reduced = false;
    goals new_gs = map_goals(s, [&](goal const & g) -> optional<goal> {
            expr new_meta = fn(g.get_meta());
            expr new_type = fn(g.get_type());
            if (new_meta != g.get_meta() || new_type != g.get_type())
                reduced = true;
            return some(goal(new_meta, new_type));
        });
    if (reduced) {
        return some(proof_state(s, new_gs));
    } else {
        return none_proof_state();
    }
}

tactic unfold_tactic(name const & n) {
    return tactic01([=](environment const & env, io_state const &, proof_state const & s) -> optional<proof_state> {
            optional<declaration> d = env.find(n);
            if (!d || !d->is_definition() || (d->is_opaque() && d->get_module_idx() != 0))
                return none_proof_state(); // tactic failed
            unfold_fn fn(n, d->get_univ_params(), d->get_value());
            return unfold_tactic_core(fn, s);
        });
}

tactic unfold_tactic() {
    return tactic01([=](environment const & env, io_state const &, proof_state const & s) -> optional<proof_state> {
            unfold_all_fn fn(env);
            return unfold_tactic_core(fn, s);
        });
}

void initialize_unfold_tactic() {
    register_tac(get_tactic_unfold_name(),
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     name const & id = tactic_expr_to_id(app_arg(e),
                                                         "invalid 'unfold' tactic, argument must be an identifier");
                     return unfold_tactic(id);
                 });
}
void finalize_unfold_tactic() {
}
}
