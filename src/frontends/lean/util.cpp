/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/replace_fn.h"
#include "library/scoped_ext.h"
#include "library/locals.h"
#include "library/explicit.h"
#include "frontends/lean/parser.h"

namespace lean {
void check_atomic(name const & n) {
    if (!n.is_atomic())
        throw exception(sstream() << "invalid declaration name '" << n << "', identifier must be atomic");
}

void check_in_section_or_context(parser const & p) {
    if (!in_section_or_context(p.env()))
        throw exception(sstream() << "invalid command, it must be used in a section");
}
static name g_root("_root_");
bool is_root_namespace(name const & n) {
    return n == g_root;
}
name remove_root_prefix(name const & n) {
    return n.replace_prefix(g_root, name());
}

// Sort local_names by order of occurrence in the section, and copy the associated parameters to section_ps
void sort_section_params(expr_struct_set const & locals, parser const & p, buffer<expr> & section_ps) {
    for (expr const & l : locals)
        section_ps.push_back(l);
    std::sort(section_ps.begin(), section_ps.end(), [&](expr const & p1, expr const & p2) {
            return p.get_local_index(mlocal_name(p1)) < p.get_local_index(mlocal_name(p2));
        });
}

// Return the levels in \c ls that are defined in the section
levels collect_section_levels(level_param_names const & ls, parser & p) {
    buffer<level> section_ls_buffer;
    for (name const & l : ls) {
        if (p.get_local_level_index(l))
            section_ls_buffer.push_back(mk_param_univ(l));
        else
            break;
    }
    return to_list(section_ls_buffer.begin(), section_ls_buffer.end());
}

// Collect local (section) constants occurring in type and value, sort them, and store in section_ps
void collect_section_locals(expr const & type, expr const & value, parser const & p, buffer<expr> & section_ps) {
    expr_struct_set ls;
    collect_locals(type, ls);
    collect_locals(value, ls);
    sort_section_params(ls, p, section_ps);
}

list<expr> locals_to_context(expr const & e, parser const & p) {
    expr_struct_set ls;
    collect_locals(e, ls);
    buffer<expr> locals;
    sort_section_params(ls, p, locals);
    std::reverse(locals.begin(), locals.end());
    return to_list(locals.begin(), locals.end());
}

expr Fun(buffer<expr> const & locals, expr const & e, parser & p) {
    return p.rec_save_pos(Fun(locals, e), p.pos_of(e));
}

expr Pi(buffer<expr> const & locals, expr const & e, parser & p) {
    return p.rec_save_pos(Pi(locals, e), p.pos_of(e));
}

template<bool is_lambda>
static expr mk_binding_as_is(unsigned num, expr const * locals, expr const & b) {
    expr r     = abstract_locals(b, num, locals);
    unsigned i = num;
    while (i > 0) {
        --i;
        expr const & l = locals[i];
        expr t = abstract_locals(mlocal_type(l), i, locals);
        if (is_lambda)
            r = mk_lambda(local_pp_name(l), mk_as_is(t), r, local_info(l));
        else
            r = mk_pi(local_pp_name(l), mk_as_is(t), r, local_info(l));
    }
    return r;
}

expr Fun_as_is(buffer<expr> const & locals, expr const & e, parser & p) {
    return p.rec_save_pos(mk_binding_as_is<true>(locals.size(), locals.data(), e), p.pos_of(e));
}

expr Pi_as_is(buffer<expr> const & locals, expr const & e, parser & p) {
    return p.rec_save_pos(mk_binding_as_is<false>(locals.size(), locals.data(), e), p.pos_of(e));
}

level mk_result_level(environment const & env, buffer<level> const & r_lvls) {
    bool impredicative = env.impredicative();
    if (r_lvls.empty()) {
        return impredicative ? mk_level_one() : mk_level_zero();
    } else {
        level r = r_lvls[0];
        for (unsigned i = 1; i < r_lvls.size(); i++)
            r = mk_max(r, r_lvls[i]);
        r = normalize(r);
        if (is_not_zero(r))
            return normalize(r);
        else
            return impredicative ? normalize(mk_max(r, mk_level_one())) : normalize(r);
    }
}

bool occurs(level const & u, level const & l) {
    bool found = false;
    for_each(l, [&](level const & l) {
            if (found) return false;
            if (l == u) { found = true; return false; }
            return true;
        });
    return found;
}

/** \brief Functional object for converting the universe metavariables in an expression in new universe parameters.
    The substitution is updated with the mapping metavar -> new param.
    The set of parameter names m_params and the buffer m_new_params are also updated.
*/
class univ_metavars_to_params_fn {
    environment const &        m_env;
    local_decls<level> const & m_lls;
    substitution &             m_subst;
    name_set &                 m_params;
    buffer<name> &             m_new_params;
    unsigned                   m_next_idx;

    /** \brief Create a new universe parameter s.t. the new name does not occur in \c m_params, nor it is
        a global universe in \e m_env or in the local_decls<level> m_lls.
        The new name is added to \c m_params, and the new level parameter is returned.
        The name is of the form "l_i" where \c i >= m_next_idx.
    */
    level mk_new_univ_param() {
        name l("l");
        name r = l.append_after(m_next_idx);
        while (m_lls.contains(r) || m_params.contains(r) || m_env.is_universe(r)) {
            m_next_idx++;
            r = l.append_after(m_next_idx);
        }
        m_params.insert(r);
        m_new_params.push_back(r);
        return mk_param_univ(r);
    }

public:
    univ_metavars_to_params_fn(environment const & env, local_decls<level> const & lls, substitution & s,
                               name_set & ps, buffer<name> & new_ps):
        m_env(env), m_lls(lls), m_subst(s), m_params(ps), m_new_params(new_ps), m_next_idx(1) {}

    level apply(level const & l) {
        return replace(l, [&](level const & l) {
                if (!has_meta(l))
                    return some_level(l);
                if (is_meta(l)) {
                    if (auto it = m_subst.get_level(meta_id(l))) {
                        return some_level(*it);
                    } else {
                        level new_p = mk_new_univ_param();
                        m_subst.assign(l, new_p);
                        return some_level(new_p);
                    }
                }
                return none_level();
            });
    }

    expr apply(expr const & e) {
        if (!has_univ_metavar(e)) {
            return e;
        } else {
            return replace(e, [&](expr const & e) {
                    if (!has_univ_metavar(e)) {
                        return some_expr(e);
                    } else if (is_sort(e)) {
                        return some_expr(update_sort(e, apply(sort_level(e))));
                    } else if (is_constant(e)) {
                        levels ls = map(const_levels(e), [&](level const & l) { return apply(l); });
                        return some_expr(update_constant(e, ls));
                    } else {
                        return none_expr();
                    }
                });
        }
    }

    expr operator()(expr const & e) { return apply(e); }
};

expr univ_metavars_to_params(environment const & env, local_decls<level> const & lls, substitution & s,
                             name_set & ps, buffer<name> & new_ps, expr const & e) {
    return univ_metavars_to_params_fn(env, lls, s, ps, new_ps)(e);
}

expr instantiate_meta(expr const & meta, substitution & subst) {
    lean_assert(is_meta(meta));
    buffer<expr> locals;
    expr mvar = get_app_args(meta, locals);
    mvar = update_mlocal(mvar, subst.instantiate_all(mlocal_type(mvar)));
    for (auto & local : locals)
        local = subst.instantiate_all(local);
    return mk_app(mvar, locals);
}

justification mk_failed_to_synthesize_jst(environment const & env, expr const & m) {
    return mk_justification(m, [=](formatter const & fmt, substitution const & subst) {
            substitution tmp(subst);
            expr new_m    = instantiate_meta(m, tmp);
            expr new_type = type_checker(env).infer(new_m).first;
            proof_state ps(goals(goal(new_m, new_type)), substitution(), name_generator("dontcare"));
            return format("failed to synthesize placeholder") + line() + ps.pp(fmt);
        });
}
}
