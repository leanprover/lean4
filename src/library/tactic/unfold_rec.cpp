/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/replace_visitor.h"
#include "library/constants.h"
#include "library/user_recursors.h"
#include "library/tactic/location.h"

extern void pp_detail(lean::environment const & env, lean::expr const & e);
extern void pp(lean::environment const & env, lean::expr const & e);

namespace lean {
// Auxiliary visitor the implements the common parts for unfold_rec_fn and fold_rec_fn
class replace_visitor_aux : public replace_visitor {
protected:
    virtual name mk_fresh_name() = 0;

    expr visit_app_default(expr const & e, expr const & fn, buffer<expr> & args) {
        bool modified = false;
        for (expr & arg : args) {
            expr new_arg = visit(arg);
            if (arg != new_arg)
                modified = true;
            arg = new_arg;
        }
        if (!modified)
            return e;
        return mk_app(fn, args);
    }

    virtual expr visit_binding(expr const & b) {
        expr new_domain = visit(binding_domain(b));
        expr l          = mk_local(mk_fresh_name(), new_domain);
        expr new_body   = abstract(visit(instantiate(binding_body(b), l)), l);
        return update_binding(b, new_domain, new_body);
    }
};


class unfold_rec_fn : public replace_visitor_aux {
    environment const & m_env;
    name_generator      m_ngen;
    bool                m_force_unfold;
    type_checker_ptr    m_tc;
    type_checker_ptr    m_norm_decl_tc;
    list<name>          m_to_unfold;
    occurrence          m_occs;
    unsigned            m_occ_idx;

    virtual name mk_fresh_name() { return m_ngen.next(); }

    static void throw_ill_formed() {
        throw exception("ill-formed expression");
    }

    bool is_rec_building_part(name const & n) {
        if (n == get_prod_pr1_name() || n == get_prod_pr2_name())
            return true;
        if (is_user_defined_recursor(m_env, n))
            return true;
        if (n.is_atomic() || !n.is_string())
            return false;
        char const * str = n.get_string();
        return
            strcmp(str, "rec_on") == 0 ||
            strcmp(str, "cases_on") == 0 ||
            strcmp(str, "brec_on") == 0 ||
            strcmp(str, "below") == 0 ||
            strcmp(str, "no_confusion") == 0;
    }

    optional<unsigned> get_local_pos(buffer<expr> const & locals, expr const & e) {
        if (!is_local(e))
            return optional<unsigned>();
        unsigned i = 0;
        for (expr const & local : locals) {
            if (mlocal_name(local) == mlocal_name(e))
                return optional<unsigned>(i);
            i++;
        }
        return optional<unsigned>();
    }

    // return true if e is of the form (C.rec ...)
    bool is_rec_app(expr const & e, buffer<expr> const & locals, name & rec_name, buffer<unsigned> & indices_pos,
                    unsigned & main_arg_pos, buffer<unsigned> & rec_arg_pos) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);
        if (!is_constant(fn))
            return false;
        optional<name> I = inductive::is_elim_rule(m_env, const_name(fn));
        rec_name = const_name(fn);
        if (!I)
            return false;
        if (!is_recursive_datatype(m_env, *I))
            return false;
        unsigned major_idx = *inductive::get_elim_major_idx(m_env, const_name(fn));
        unsigned nindices  = *inductive::get_num_indices(m_env, *I);
        lean_assert(nindices <= major_idx);
        unsigned rel_idx   = major_idx - nindices; // first index we should track
        // Collect position of indices (at least the ones that occur in e)
        while (rel_idx < args.size() && rel_idx < major_idx) {
            if (auto it2 = get_local_pos(locals, args[rel_idx])) {
                indices_pos.push_back(*it2);
            } else {
                return false;
            }
            rel_idx++;
        }

        if (major_idx >= args.size()) {
            // Some indices and the major premise may not occur in e because of eta-reduction
            main_arg_pos      = locals.size() + major_idx - args.size();
            for (unsigned i = rel_idx; i < major_idx; i++)
                indices_pos.push_back(locals.size() + i - args.size());
            return true;
        }

        if (auto it = get_local_pos(locals, args[major_idx])) {
            main_arg_pos = *it;
        } else {
            return false;
        }

        for (unsigned i = major_idx+1; i < args.size(); i++) {
            if (auto it2 = get_local_pos(locals, args[i])) {
                rec_arg_pos.push_back(*it2);
            } else {
                return false;
            }
        }
        return true;
    }

    enum rec_kind { BREC, REC, NOREC };

    // try to detect the kind of recursive definition
    rec_kind get_rec_kind(expr const & e, buffer<expr> const & locals, name & rec_name,
                          buffer<unsigned> & indices_pos, unsigned & main_arg_pos, buffer<unsigned> & rec_arg_pos) {
        if (is_rec_app(e, locals, rec_name, indices_pos, main_arg_pos, rec_arg_pos))
            return REC;
        buffer<expr> args;
        expr fn = get_app_args(e, args);
        if (is_constant(fn) && const_name(fn) == inductive::get_elim_name(get_prod_name()) &&
            args.size() >= 5) {
            // try do detect brec_on pattern
            if (is_rec_app(args[4], locals, rec_name, indices_pos, main_arg_pos, rec_arg_pos) &&
                // for brec, eta is not applicable, so main_arg_pos must be < locals.size()
                main_arg_pos < locals.size()) {
                for (unsigned i = 5; i < args.size(); i++) {
                    if (auto it2 = get_local_pos(locals, args[i])) {
                        rec_arg_pos.push_back(*it2);
                    } else {
                        return NOREC;
                    }
                }
                return BREC;
            }
        }
        return NOREC;
    }

    // just unfold the application without trying to fold recursive call
    expr unfold_simple(expr const & fn, buffer<expr> & args) {
        expr new_app = mk_app(fn, args);
        if (auto r = unfold_term(m_env, new_app)) {
            return visit(*r);
        } else {
            return new_app;
        }
    }

    expr get_fn_decl(expr const & fn, buffer<expr> & locals) {
        lean_assert(is_constant(fn));
        declaration decl = m_env.get(const_name(fn));
        if (length(const_levels(fn)) != decl.get_num_univ_params())
            throw_ill_formed();
        expr fn_body     = instantiate_value_univ_params(decl, const_levels(fn));
        while (is_lambda(fn_body)) {
            expr local = mk_local(m_ngen.next(), binding_domain(fn_body));
            locals.push_back(local);
            fn_body    = instantiate(binding_body(fn_body), local);
        }
        return m_norm_decl_tc->whnf(fn_body).first;
    }

    struct fold_failed {};

    struct fold_rec_fn : public replace_visitor_aux {
        type_checker_ptr &       m_tc;
        expr                     m_fn;    // function being unfolded
        buffer<expr> const &     m_args;  // arguments of the function being unfolded
        rec_kind                 m_kind;
        name                     m_rec_name;
        unsigned                 m_major_idx; // position of the major premise in the recursor
        buffer<unsigned> const & m_indices_pos; // position of the datatype indices in the function being unfolded
        unsigned                 m_main_pos;  // position of the (recursive) argument in the function being unfolded
        buffer<unsigned> const & m_rec_arg_pos; // position of the other arguments that are not fixed in the recursion
        name                     m_prod_rec_name;

        fold_rec_fn(type_checker_ptr & tc, expr const & fn, buffer<expr> const & args, rec_kind k, name const & rec_name,
                    buffer<unsigned> const & indices_pos, unsigned main_pos, buffer<unsigned> const & rec_arg_pos):
            m_tc(tc), m_fn(fn), m_args(args), m_kind(k), m_rec_name(rec_name),
            m_major_idx(*inductive::get_elim_major_idx(m_tc->env(), rec_name)),
            m_indices_pos(indices_pos),
            m_main_pos(main_pos), m_rec_arg_pos(rec_arg_pos) {
            m_prod_rec_name = inductive::get_elim_name(get_prod_name());
            lean_assert(m_main_pos < args.size());
            lean_assert(std::all_of(rec_arg_pos.begin(), rec_arg_pos.end(), [&](unsigned pos) { return pos < args.size(); }));
        }

        virtual name mk_fresh_name() { return m_tc->mk_fresh_name(); }

        expr fold_rec(expr const & e, buffer<expr> const & args) {
            if (args.size() != m_major_idx + 1 + m_rec_arg_pos.size())
                throw fold_failed();
            buffer<expr> new_args;
            new_args.append(m_args);
            unsigned nindices = m_indices_pos.size();
            for (unsigned i = 0; i < m_indices_pos.size(); i++) {
                new_args[m_indices_pos[i]] = args[m_major_idx - nindices + i];
            }
            new_args[m_main_pos] = args[m_major_idx];
            for (unsigned i = 0; i < m_rec_arg_pos.size(); i++) {
                new_args[m_rec_arg_pos[i]] = args[m_major_idx + 1 + i];
            }
            expr folded_app = mk_app(m_fn, new_args);
            if (!m_tc->is_def_eq(folded_app, e).first)
                throw fold_failed();
            return folded_app;
        }

        expr fold_brec_core(expr const & e, buffer<expr> const & args, unsigned prefix_size, unsigned major_pos) {
            if (args.size() != prefix_size + m_rec_arg_pos.size()) {
                throw fold_failed();
            }
            buffer<expr> nested_args;
            get_app_args(args[major_pos], nested_args);

            if (nested_args.size() != m_major_idx+1) {
                throw fold_failed();
            }
            buffer<expr> new_args;
            new_args.append(m_args);
            unsigned nindices = m_indices_pos.size();
            for (unsigned i = 0; i < m_indices_pos.size(); i++) {
                new_args[m_indices_pos[i]] = nested_args[m_major_idx - nindices + i];
            }
            new_args[m_main_pos] = nested_args[m_major_idx];
            for (unsigned i = 0; i < m_rec_arg_pos.size(); i++) {
                new_args[m_rec_arg_pos[i]] = args[prefix_size + i];
            }
            expr folded_app = mk_app(m_fn, new_args);
            if (!m_tc->is_def_eq(folded_app, e).first)
                throw fold_failed();
            return folded_app;
        }

        expr fold_brec_pr1(expr const & e, buffer<expr> const & args) {
            return fold_brec_core(e, args, 3, 1);
        }

        expr fold_brec_prod_rec(expr const & e, buffer<expr> const & args) {
            return fold_brec_core(e, args, 5, 4);
        }

        virtual expr visit_app(expr const & e) {
            buffer<expr> args;
            expr fn = get_app_args(e, args);
            if (m_kind == REC && is_constant(fn) && const_name(fn) == m_rec_name) {
                expr new_e = m_tc->whnf(e).first;
                if (new_e != e)
                    return visit_app(new_e);
                else
                    return fold_rec(e, args);
            }
            if (m_kind == BREC && is_constant(fn) && const_name(fn) == get_prod_pr1_name() && args.size() >= 3) {
                expr rec_fn = get_app_fn(args[1]);
                if (is_constant(rec_fn) && const_name(rec_fn) == m_rec_name)
                    return fold_brec_pr1(e, args);
            }
            if (m_kind == BREC && is_constant(fn) && const_name(fn) == m_prod_rec_name && args.size() >= 5) {
                expr rec_fn = get_app_fn(args[4]);
                if (is_constant(rec_fn) && const_name(rec_fn) == m_rec_name)
                    return fold_brec_prod_rec(e, args);
            }
            return visit_app_default(e, fn, args);
        }
    };

    expr unfold(expr const & fn, buffer<expr> args) {
        buffer<expr> fn_locals;
        expr fn_body = get_fn_decl(fn, fn_locals);
        if (args.size() < fn_locals.size()) {
            // insufficient args
            return unfold_simple(fn, args);
        }
        name rec_name;
        unsigned main_pos = 0;
        buffer<unsigned> indices_pos;
        buffer<unsigned> rec_arg_pos;
        rec_kind k = get_rec_kind(fn_body, fn_locals, rec_name, indices_pos, main_pos, rec_arg_pos);
        if (k == NOREC || main_pos >= args.size()) {
            // norecursive definition
            return unfold_simple(fn, args);
        }
        unsigned rest = main_pos >= fn_locals.size() ? main_pos+1 : fn_locals.size();
        for (unsigned i = rest; i < args.size(); i++)
            rec_arg_pos.push_back(i);
        auto new_main_cs  = m_tc->whnf(args[main_pos]);
        if (!is_constructor_app(m_env, new_main_cs.first) || new_main_cs.second) {
            // argument is not a constructor or constraints were generated
            throw fold_failed();
        }
        args[main_pos]    = new_main_cs.first;
        expr fn_body_abst = abstract_locals(fn_body, fn_locals.size(), fn_locals.data());
        expr new_e        = instantiate_rev(fn_body_abst, fn_locals.size(), args.data());
        new_e             = mk_app(new_e, args.size() - fn_locals.size(), args.data() + fn_locals.size());
        auto new_e_cs     = m_norm_decl_tc->whnf(new_e);
        if (new_e_cs.second) {
            // constraints were generated
            throw fold_failed();
        }
        new_e               = new_e_cs.first;
        expr const new_head = get_app_fn(new_e);
        // TODO(Leo): create an option for the following conditions?
        // if (is_constant(new_head) && inductive::is_elim_rule(m_env, const_name(new_head))) {
        //    //head is a recursor... so the unfold is probably not generating a nice result...
        //    throw fold_failed();
        // }
        return fold_rec_fn(m_tc, fn, args, k, rec_name, indices_pos, main_pos, rec_arg_pos)(new_e);
    }

    bool unfold_cnst(expr const & e) {
        if (!is_constant(e))
            return false;
        if (std::find(m_to_unfold.begin(), m_to_unfold.end(), const_name(e)) == m_to_unfold.end())
            return false;
        m_occ_idx++;
        return m_occs.contains(m_occ_idx);
    }

    virtual expr visit_app(expr const & e) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);
        bool modified = false;
        for (expr & arg : args) {
            expr new_arg = visit(arg);
            if (arg != new_arg)
                modified = true;
            arg = new_arg;
        }
        if (unfold_cnst(fn)) {
            try {
                return unfold(fn, args);
            } catch (fold_failed &) {
                if (m_force_unfold)
                    return unfold_simple(fn, args);
            }
        }
        if (!modified) {
            return e;
        } else {
            return mk_app(fn, args);
        }
    }

    virtual expr visit_constant(expr const & e) {
        if (unfold_cnst(e)) {
            if (auto r = unfold_term(m_env, e))
                return *r;
        }
        return e;
    }

public:
    unfold_rec_fn(environment const & env, name_generator && ngen, bool force_unfold, list<name> const & to_unfold,
                  occurrence const & occs):
        m_env(env),
        m_ngen(ngen),
        m_force_unfold(force_unfold),
        m_tc(mk_type_checker(m_env, m_ngen.mk_child(), [](name const &) { return false; })),
        m_norm_decl_tc(mk_type_checker(m_env, m_ngen.mk_child(), [&](name const & n) { return !is_rec_building_part(n); })),
        m_to_unfold(to_unfold),
        m_occs(occs),
        m_occ_idx(0)
        {}

    expr operator()(expr const & e) {
        m_occ_idx = 0;
        return replace_visitor_aux::operator()(e);
    }
};

optional<expr> unfold_rec(environment const & env, name_generator && ngen, bool force_unfold, expr const & e, list<name> const & to_unfold,
                          occurrence const & occs) {
    lean_assert(std::all_of(to_unfold.begin(), to_unfold.end(), [&](name const & n) { return env.get(n).is_definition(); }));
    try {
        expr r = unfold_rec_fn(env, std::move(ngen), force_unfold, to_unfold, occs)(e);
        if (r == e)
            return none_expr();
        return some_expr(r);
    } catch (exception &) {
        return none_expr();
    }
}
}
