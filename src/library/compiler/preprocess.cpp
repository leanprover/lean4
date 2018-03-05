/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/declaration.h"
#include "kernel/type_checker.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "kernel/scope_pos_info_provider.h"
#include "library/trace.h"
#include "library/projection.h"
#include "library/constants.h"
#include "library/aux_recursors.h"
#include "library/user_recursors.h"
#include "library/util.h"
#include "library/quote.h"
#include "library/noncomputable.h"
#include "library/context_cache.h"
#include "library/module.h"
#include "library/vm/vm.h"
#include "library/compiler/util.h"
#include "library/compiler/preprocess.h"
#include "library/compiler/compiler_step_visitor.h"
#include "library/compiler/comp_irrelevant.h"
#include "library/compiler/nat_value.h"
#include "library/compiler/eta_expansion.h"
#include "library/compiler/inliner.h"
#include "library/compiler/elim_recursors.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/reduce_arity.h"
#include "library/compiler/lambda_lifting.h"
#include "library/compiler/simp_inductive.h"
#include "library/compiler/elim_unused_lets.h"
#include "library/compiler/extract_values.h"
#include "library/compiler/cse.h"

namespace lean {
class expand_aux_fn : public compiler_step_visitor {
    enum class recursor_kind { Aux, CasesOn, NotRecursor };
    /* We only expand auxiliary recursors and user-defined recursors.
       However, we don't unfold recursors of the form C.cases_on if C != eq. */
    recursor_kind get_recursor_app_kind(expr const & e) const {
        if (!is_app(e))
            return recursor_kind::NotRecursor;
        expr const & fn = get_app_fn(e);
        if (!is_constant(fn))
            return recursor_kind::NotRecursor;
        name const & n = const_name(fn);
        if (is_cases_on_recursor(env(), n) && n != get_eq_cases_on_name()) {
            return recursor_kind::CasesOn;
        } else if (::lean::is_aux_recursor(env(), n) || is_user_defined_recursor(env(), n)) {
            return recursor_kind::Aux;
        } else {
            return recursor_kind::NotRecursor;
        }
    }

    bool is_aux_recursor(expr const & e) const {
        return get_recursor_app_kind(e) == recursor_kind::Aux;
    }

    expr visit_cases_on(expr const & e) {
        /* Try to reduce cases_on.
           Remark: we only unfold reducible constants. */
        type_context_old::transparency_scope scope(ctx(), transparency_mode::Reducible);
        if (auto r1 = ctx().reduce_aux_recursor(e)) {
            if (auto r2 = ctx().norm_ext(*r1)) {
                return compiler_step_visitor::visit(*r2);
            }
        }
        return compiler_step_visitor::visit_app(e);
    }

    bool is_not_vm_function(expr const & e) {
        expr const & fn = get_app_fn(e);
        if (!is_constant(fn))
            return false;
        name const & n = const_name(fn);
        declaration d   = env().get(n);
        if (!d.is_definition() || d.is_theorem() || is_projection(env(), n) || is_no_confusion(env(), n) ||
            ::lean::is_aux_recursor(env(), n) || is_user_defined_recursor(env(), n))
            return false;
        return !is_vm_function(env(), n);
    }

    bool is_pack_unpack(expr const & e) {
        return ::lean::is_pack_unpack(m_env, e);
    }

    bool is_noncomputable_const(expr const & e) {
        return is_constant(e) && is_noncomputable(env(), const_name(e));
    }

    bool is_inline(expr const & e) {
        return is_constant(e) && ::lean::is_inline(env(), const_name(e));
    }

    bool should_unfold(expr const & e) {
        return
            (is_not_vm_function(e) && !ctx().is_proof(e) && !is_pack_unpack(e) && !is_noncomputable_const(e)) ||
            (is_inline(e));
    }

    expr unfold(expr const & e) {
        if (auto r = unfold_term(env(), e)) {
            return visit(*r);
        } else {
            throw exception(sstream() << "failed to generate bytecode, VM does not have code for '" << get_app_fn(e) << "'");
        }
    }

    virtual expr visit_constant(expr const & e) override {
        type_context_old::nozeta_scope scope(ctx());
        if (should_unfold(e))
            return visit(unfold(e));
        else
            return e;
    }

    virtual expr visit_app(expr const & e) override {
        type_context_old::nozeta_scope scope(ctx());
        switch (get_recursor_app_kind(e)) {
        case recursor_kind::NotRecursor: {
            if (should_unfold(e))
                return visit(unfold(e));
            expr new_e;
            {
                type_context_old::transparency_scope scope(ctx(), transparency_mode::Reducible);
                new_e = copy_tag(e, ctx().whnf_head_pred(e, [&](expr const &) { return false; }));
            }
            if (is_eqp(new_e, e))
                return compiler_step_visitor::visit_app(new_e);
            else
                return compiler_step_visitor::visit(new_e);
        }
        case recursor_kind::CasesOn:
            return visit_cases_on(e);
        case recursor_kind::Aux:
            expr new_e;
            {
                type_context_old::transparency_scope scope(ctx(), transparency_mode::Reducible);
                new_e = copy_tag(e, ctx().whnf_head_pred(e, [&](expr const & e) { return is_aux_recursor(e); }));
            }
            return compiler_step_visitor::visit(new_e);
        }
        lean_unreachable();
    }

public:
    expand_aux_fn(environment const & env, abstract_context_cache & cache):compiler_step_visitor(env, cache) {}
};

static expr expand_aux(environment const & env, abstract_context_cache & cache, expr const & e) {
    return expand_aux_fn(env, cache)(e);
}

static name * g_tmp_prefix = nullptr;

class preprocess_fn {
    environment    m_env;
    context_cache  m_cache;

    bool check(declaration const & d, expr const & v) {
        bool memoize      = true;
        bool trusted_only = false;
        type_checker tc(m_env, memoize, trusted_only);
        expr t = tc.check(v, d.get_univ_params());
        if (!tc.is_def_eq(d.get_type(), t))
            throw exception("preprocess failed");
        return true;
    }

    void display(buffer<procedure> const & procs) {
        for (auto const & p : procs) {
            tout() << ">> " << p.m_name << "\n" << p.m_code << "\n";
        }
    }

    void erase_irrelevant(buffer<procedure> & procs) {
        for (procedure & p : procs) {
            p.m_code = ::lean::erase_irrelevant(m_env, m_cache, p.m_code);
        }
    }

#if 0
    void dump_pos_info(expr const & v) {
        std::cout << v << "\n\n";
        for_each(v, [&](expr const & e, unsigned) {
                auto pip = get_pos_info_provider();
                if (!pip) return false;
                if (auto p = pip->get_pos_info(e))
                    std::cout << "pos[" << ((unsigned)e.kind()) << "]: " << p->first << ":" << p->second << "\n"
                              << e << "\n";
                return true;
            });
        std::cout << "------------\n";
    }

    void dump_pos_info(buffer<pair<name, expr>> & procs) {
        for (auto p : procs) dump_pos_info(p.second);
    }
#endif

    /* If type of d is a proposition or return a type, we don't need to compile it.
       We can just generate (fun args, neutral_expr)

       This procedure returns true if type of d is a proposition or return a type,
       and store the dummy code above in */
    bool compile_irrelevant(declaration const & d, buffer<procedure> & procs) {
        type_context_old ctx(m_env, transparency_mode::All);
        expr type = d.get_type();
        type_context_old::tmp_locals locals(ctx);
        while (true) {
            type = ctx.relaxed_whnf(type);
            if (!is_pi(type))
                break;
            expr local = locals.push_local_from_binding(type);
            type       = instantiate(binding_body(type), local);
        }
        if (ctx.is_prop(type) || is_sort(type)) {
            expr r = locals.mk_lambda(mk_neutral_expr());
            procs.emplace_back(d.get_name(), optional<pos_info>(), r);
            return true;
        } else {
            return false;
        }
    }

public:
    preprocess_fn(environment const & env):
        m_env(env) {}

    void operator()(declaration const & d, buffer<procedure> & procs) {
        if (compile_irrelevant(d, procs))
            return;
        expr v = d.get_value();
        lean_trace(name({"compiler", "input"}), tout() << "\n" << v << "\n";);
        v = inline_simple_definitions(m_env, m_cache, v);
        lean_cond_assert("compiler", check(d, v));
        lean_trace(name({"compiler", "inline"}), tout() << "\n" << v << "\n";);
        v = expand_aux(m_env, m_cache, v);
        lean_cond_assert("compiler", check(d, v));
        lean_trace(name({"compiler", "expand_aux"}), tout() << "\n" << v << "\n";);
        v = mark_comp_irrelevant_subterms(m_env, m_cache, v);
        lean_cond_assert("compiler", check(d, v));
        v = find_nat_values(m_env, v);
        lean_cond_assert("compiler", check(d, v));
        v = eta_expand(m_env, m_cache, v);
        lean_cond_assert("compiler", check(d, v));
        lean_trace(name({"compiler", "eta_expansion"}), tout() << "\n" << v << "\n";);
        v = elim_recursors(m_env, m_cache, d.get_name(), v, procs);
        procs.emplace_back(d.get_name(), get_decl_pos_info(m_env, d.get_name()), v);
        lean_cond_assert("compiler", check(d, procs.back().m_code));
        lean_trace(name({"compiler", "elim_recursors"}), tout() << "\n"; display(procs););
        erase_irrelevant(procs);
        lean_trace(name({"compiler", "erase_irrelevant"}), tout() << "\n"; display(procs););
        reduce_arity(m_env, m_cache, procs);
        lean_trace(name({"compiler", "reduce_arity"}), tout() << "\n"; display(procs););
        erase_trivial_structures(m_env, m_cache, procs);
        lean_trace(name({"compiler", "erase_trivial_structures"}), tout() << "\n"; display(procs););
        lambda_lifting(m_env, m_cache, d.get_name(), procs);
        lean_trace(name({"compiler", "lambda_lifting"}), tout() << "\n"; display(procs););
        simp_inductive(m_env, m_cache, procs);
        lean_trace(name({"compiler", "simplify_inductive"}), tout() << "\n"; display(procs););
        elim_unused_lets(m_env, m_cache, procs);
        lean_trace(name({"compiler", "elim_unused_lets"}), tout() << "\n"; display(procs););
        extract_values(m_env, m_cache, d.get_name(), procs);
        lean_trace(name({"compiler", "extract_values"}), tout() << "\n"; display(procs););
        cse(m_env, m_cache, procs);
        lean_trace(name({"compiler", "cse"}), tout() << "\n"; display(procs););
        lean_trace(name({"compiler", "preprocess"}), tout() << "\n"; display(procs););
    }
};

void preprocess(environment const & env, declaration const & d, buffer<procedure> & result) {
    return preprocess_fn(env)(d, result);
}

void preprocess(environment const & env, buffer<declaration> const & ds, buffer<procedure> & result) {
    for (declaration const & d : ds) {
        buffer<procedure> procs;
        preprocess(env, d, procs);
        result.append(procs);
    }
}

void initialize_preprocess() {
    register_trace_class("compiler");
    register_trace_class({"compiler", "input"});
    register_trace_class({"compiler", "expand_aux"});
    register_trace_class({"compiler", "eta_expansion"});
    register_trace_class({"compiler", "simplify_pr1"});
    register_trace_class({"compiler", "inline"});
    register_trace_class({"compiler", "elim_recursors"});
    register_trace_class({"compiler", "erase_irrelevant"});
    register_trace_class({"compiler", "reduce_arity"});
    register_trace_class({"compiler", "erase_trivial_structures"});
    register_trace_class({"compiler", "lambda_lifting"});
    register_trace_class({"compiler", "simplify_inductive"});
    register_trace_class({"compiler", "elim_unused_lets"});
    register_trace_class({"compiler", "extract_values"});
    register_trace_class({"compiler", "cse"});
    register_trace_class({"compiler", "preprocess"});
    g_tmp_prefix = new name(name::mk_internal_unique_name());
}

void finalize_preprocess() {
    delete g_tmp_prefix;
}
}
