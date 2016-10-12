/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/type_context.h"
#include "library/replace_visitor.h"
#include "library/constants.h"
#include "library/user_recursors.h"
#include "library/eqn_lemmas.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/occurrences.h"

namespace lean {
/* Auxiliary visitor the implements the common parts for unfold_rec_fn and fold_rec_fn. */
class replace_visitor_aux : public replace_visitor {
protected:
    virtual type_context & ctx() = 0;

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

    virtual expr visit_binding(expr const & b) override {
        expr new_domain = visit(binding_domain(b));
        type_context::tmp_locals locals(ctx());
        expr l          = locals.push_local(binding_name(b), new_domain, binding_info(b));
        expr new_body   = ctx().abstract_locals(visit(instantiate(binding_body(b), l)), 1, &l);
        return update_binding(b, new_domain, new_body);
    }
};


class unfold_rec_fn : public replace_visitor_aux {
    environment const & m_env;
    bool                m_force_unfold;
    type_context &      m_ctx;
    list<name>          m_to_unfold;
    occurrences         m_occs;
    unsigned            m_occ_idx;

    static void throw_ill_formed() {
        throw exception("ill-formed expression");
    }

    virtual type_context & ctx() override { return m_ctx; }

    bool is_rec_building_part(name const & n) {
        if (n == get_prod_fst_name() || n == get_prod_snd_name())
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

    /* Return true iff \c e is of the form (C.rec ...) */
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

    /* Try to detect the kind of recursive definition */
    rec_kind get_rec_kind(expr const & e, buffer<expr> const & locals, name & rec_name,
                          buffer<unsigned> & indices_pos, unsigned & main_arg_pos, buffer<unsigned> & rec_arg_pos) {
        // tout() << "get_rec_kind: " << e << "\n";
        if (is_rec_app(e, locals, rec_name, indices_pos, main_arg_pos, rec_arg_pos))
            return REC;
        buffer<expr> args;
        expr fn = get_app_args(e, args);
        if (is_constant(fn) && const_name(fn) == get_prod_fst_name() &&
            args.size() >= 3) {
            // try do detect brec_on pattern
            if (is_rec_app(args[2], locals, rec_name, indices_pos, main_arg_pos, rec_arg_pos) &&
                // for brec, eta is not applicable, so main_arg_pos must be < locals.size()
                main_arg_pos < locals.size()) {
                for (unsigned i = 3; i < args.size(); i++) {
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

    /* Just unfold the application without trying to fold recursive call */
    expr unfold_simple(expr const & fn, buffer<expr> & args) {
        expr new_app = mk_app(fn, args);
        if (auto r = unfold_term(m_env, new_app)) {
            return visit(*r);
        } else {
            return new_app;
        }
    }

    struct fold_failed {};

    struct fold_rec_fn : public replace_visitor_aux {
        type_context &           m_ctx;
        expr                     m_fn;    // function being unfolded
        buffer<expr> const &     m_args;  // arguments of the function being unfolded
        rec_kind                 m_kind;
        name                     m_rec_name;
        unsigned                 m_major_idx; // position of the major premise in the recursor
        buffer<unsigned> const & m_indices_pos; // position of the datatype indices in the function being unfolded
        unsigned                 m_main_pos;  // position of the (recursive) argument in the function being unfolded
        buffer<unsigned> const & m_rec_arg_pos; // position of the other arguments that are not fixed in the recursion
        name                     m_prod_rec_name;

        fold_rec_fn(type_context & ctx, expr const & fn, buffer<expr> const & args, rec_kind k, name const & rec_name,
                    buffer<unsigned> const & indices_pos, unsigned main_pos, buffer<unsigned> const & rec_arg_pos):
            m_ctx(ctx), m_fn(fn), m_args(args), m_kind(k), m_rec_name(rec_name),
            m_major_idx(*inductive::get_elim_major_idx(m_ctx.env(), rec_name)),
            m_indices_pos(indices_pos),
            m_main_pos(main_pos), m_rec_arg_pos(rec_arg_pos) {
            m_prod_rec_name = inductive::get_elim_name(get_prod_name());
            lean_assert(m_main_pos < args.size());
            lean_assert(std::all_of(rec_arg_pos.begin(), rec_arg_pos.end(), [&](unsigned pos) { return pos < args.size(); }));
        }

        virtual type_context & ctx() override { return m_ctx; }

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
            if (!m_ctx.is_def_eq(folded_app, e))
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
            if (!m_ctx.is_def_eq(folded_app, e))
                throw fold_failed();
            return folded_app;
        }

        expr fold_brec_fst(expr const & e, buffer<expr> const & args) {
            return fold_brec_core(e, args, 3, 1);
        }

        expr fold_brec_prod_rec(expr const & e, buffer<expr> const & args) {
            return fold_brec_core(e, args, 5, 4);
        }

        virtual expr visit_app(expr const & e) override {
            buffer<expr> args;
            expr fn = get_app_args(e, args);
            if (m_kind == REC && is_constant(fn) && const_name(fn) == m_rec_name) {
                expr new_e = m_ctx.whnf(e);
                if (new_e != e)
                    return visit_app(new_e);
                else
                    return fold_rec(e, args);
            }
            if (m_kind == BREC && is_constant(fn) && const_name(fn) == get_prod_fst_name() && args.size() >= 3) {
                expr rec_fn = get_app_fn(args[1]);
                if (is_constant(rec_fn) && const_name(rec_fn) == m_rec_name)
                    return fold_brec_fst(e, args);
            }
            if (m_kind == BREC && is_constant(fn) && const_name(fn) == m_prod_rec_name && args.size() >= 5) {
                expr rec_fn = get_app_fn(args[4]);
                if (is_constant(rec_fn) && const_name(rec_fn) == m_rec_name)
                    return fold_brec_prod_rec(e, args);
            }
            return visit_app_default(e, fn, args);
        }
    };

    expr whnf_rec(expr const & e) {
        return m_ctx.whnf_pred(e, [&](expr const & c) {
                expr const & fn = get_app_fn(c);
                return is_constant(fn) && is_rec_building_part(const_name(fn));
            });
    }

    expr get_fn_decl(expr const & fn, type_context::tmp_locals & locals) {
        lean_assert(is_constant(fn));
        declaration decl = m_env.get(const_name(fn));
        if (length(const_levels(fn)) != decl.get_num_univ_params())
            throw_ill_formed();
        if (!decl.is_definition())
            throw exception(sstream() << "unfold tactic failed, '" << const_name(fn) << "' is not a definition");
        expr fn_body     = instantiate_value_univ_params(decl, const_levels(fn));
        while (is_lambda(fn_body)) {
            expr local = locals.push_local_from_binding(fn_body);
            fn_body    = instantiate(binding_body(fn_body), local);
        }
        return whnf_rec(fn_body);
    }

    expr unfold(expr const & fn, buffer<expr> args) {
        type_context::tmp_locals fn_locals(m_ctx);
        expr fn_body = get_fn_decl(fn, fn_locals);
        if (args.size() < fn_locals.size()) {
            // insufficient args
            return unfold_simple(fn, args);
        }
        name rec_name;
        unsigned main_pos = 0;
        buffer<unsigned> indices_pos;
        buffer<unsigned> rec_arg_pos;
        rec_kind k = get_rec_kind(fn_body, fn_locals.as_buffer(), rec_name, indices_pos, main_pos, rec_arg_pos);
        if (k == NOREC || main_pos >= args.size()) {
            // norecursive definition
            return unfold_simple(fn, args);
        }
        unsigned rest = main_pos >= fn_locals.size() ? main_pos+1 : fn_locals.size();
        for (unsigned i = rest; i < args.size(); i++)
            rec_arg_pos.push_back(i);
        expr new_main  = m_ctx.whnf(args[main_pos]);
        if (!is_constructor_app(m_env, new_main)) {
            // argument is not a constructor or constraints were generated
            throw fold_failed();
        }
        args[main_pos]      = new_main;
        expr fn_body_abst   = m_ctx.abstract_locals(fn_body, fn_locals.as_buffer().size(), fn_locals.as_buffer().data());
        expr new_e          = instantiate_rev(fn_body_abst, fn_locals.as_buffer().size(), args.data());
        new_e               = mk_app(new_e, args.size() - fn_locals.as_buffer().size(), args.data() + fn_locals.as_buffer().size());
        new_e               = whnf_rec(new_e);
        expr const new_head = get_app_fn(new_e);
        // TODO(Leo): create an option for the following conditions?
        if (is_constant(new_head) && inductive::is_elim_rule(m_env, const_name(new_head))) {
            // head is a recursor... so the unfold is probably not generating a nice result...
            throw fold_failed();
        }
        return fold_rec_fn(m_ctx, fn, args, k, rec_name, indices_pos, main_pos, rec_arg_pos)(new_e);
    }

    bool unfold_cnst(expr const & e) {
        if (!is_constant(e))
            return false;
        if (std::find(m_to_unfold.begin(), m_to_unfold.end(), const_name(e)) == m_to_unfold.end())
            return false;
        m_occ_idx++;
        return m_occs.contains(m_occ_idx);
    }

    virtual expr visit_app(expr const & e) override {
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

    virtual expr visit_constant(expr const & e) override {
        if (unfold_cnst(e)) {
            if (auto r = unfold_term(m_env, e))
                return *r;
        }
        return e;
    }

public:
    unfold_rec_fn(type_context & ctx, bool force_unfold, list<name> const & to_unfold, occurrences const & occs):
        m_env(ctx.env()),
        m_force_unfold(force_unfold),
        m_ctx(ctx),
        m_to_unfold(to_unfold),
        m_occs(occs),
        m_occ_idx(0) {}

    expr operator()(expr const & e) {
        m_occ_idx = 0;
        return replace_visitor_aux::operator()(e);
    }
};

vm_obj tactic_unfold_expr(vm_obj const & force, vm_obj const & occs, vm_obj const & to_unfold, vm_obj const & e, vm_obj const & s) {
    try {
        type_context ctx = mk_type_context_for(to_tactic_state(s));
        expr r = unfold_rec_fn(ctx, to_bool(force), to_list_name(to_unfold), to_occurrences(occs))(to_expr(e));
        return mk_tactic_success(to_obj(r), to_tactic_state(s));
    } catch (exception & ex) {
        return mk_tactic_exception(ex, to_tactic_state(s));
    }
}

vm_obj tactic_unfold_projection_core(vm_obj const & m, vm_obj const & _e, vm_obj const & _s) {
    expr const & e = to_expr(_e);
    tactic_state const & s = to_tactic_state(_s);
    try {
        expr const & fn = get_app_fn(e);
        type_context ctx = mk_type_context_for(s, to_transparency_mode(m));
        if (!is_constant(fn) || !is_projection(s.env(), const_name(fn)))
            return mk_tactic_exception("unfold projection failed, expression is not a projection application", s);
        if (auto new_e = ctx.reduce_projection(e))
            return mk_tactic_success(to_obj(*new_e), s);
        return mk_tactic_exception("unfold projection failed, failed to unfold", s);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj tactic_dunfold_expr(vm_obj const & _e, vm_obj const & _s) {
    expr const & e = to_expr(_e);
    tactic_state const & s = to_tactic_state(_s);
    try {
        environment const & env = s.env();
        expr const & fn = get_app_fn(e);
        if (!is_constant(fn))
            return mk_tactic_exception("dunfold_expr failed, expression is not a constant nor a constant application", s);
        expr new_e;
        if (has_eqn_lemmas(env, const_name(fn))) {
            type_context ctx = mk_type_context_for(s);
            buffer<simp_lemma> lemmas;
            bool refl_only = true;
            get_eqn_lemmas_for(env, const_name(fn), refl_only, lemmas);
            for (simp_lemma const & sl : lemmas) {
                expr new_e = refl_lemma_rewrite(ctx, e, sl);
                if (new_e != e)
                    return mk_tactic_success(to_obj(new_e), s);
            }
            return mk_tactic_exception("dunfold_expr failed, none of the rfl lemmas is application", s);
        } else {
            declaration d = env.get(const_name(fn));
            if (!d.is_definition())
                return mk_tactic_exception(sstream() << "dunfold_expr failed, '" << d.get_name() << "' is not a definition", s);
            if (d.get_num_univ_params() != length(const_levels(fn)))
                return mk_tactic_exception("dunfold_expr failed, incorrect number of universe levels", s);
            buffer<expr> args;
            get_app_args(e, args);
            expr new_e = head_beta_reduce(mk_app(instantiate_value_univ_params(d, const_levels(fn)), args.size(), args.data()));
            return mk_tactic_success(to_obj(new_e), s);
        }
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

void initialize_unfold_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "unfold_expr_core"}), tactic_unfold_expr);
    DECLARE_VM_BUILTIN(name({"tactic", "unfold_projection_core"}), tactic_unfold_projection_core);
    DECLARE_VM_BUILTIN(name({"tactic", "dunfold_expr"}),           tactic_dunfold_expr);
}

void finalize_unfold_tactic() {
}
}
