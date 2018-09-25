/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/timeit.h"
#include "kernel/declaration.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/for_each_fn.h"
#include "library/scope_pos_info_provider.h"
#include "library/trace.h"
#include "library/projection.h"
#include "library/constants.h"
#include "library/aux_recursors.h"
#include "library/user_recursors.h"
#include "library/util.h"
#include "library/noncomputable.h"
#include "library/context_cache.h"
#include "library/module.h"
#include "library/max_sharing.h"
#include "library/vm/vm.h"
#include "library/compiler/old_util.h"
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
#include "library/compiler/old_cse.h"

#include "library/compiler/util.h"
#include "library/compiler/lcnf.h"
#include "library/compiler/csimp.h"
#include "library/compiler/elim_dead_let.h"
#include "library/compiler/cse.h"

namespace lean {
class expand_aux_fn : public compiler_step_visitor {
    name_set m_decl_names; /* functions being compiled */

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
            if (auto r2 = ctx().reduce_recursor(*r1)) {
                return compiler_step_visitor::visit(*r2);
            }
        }
        return compiler_step_visitor::visit_app(e);
    }

    bool is_not_vm_function(expr const & e) {
        expr const & fn = get_app_fn(e);
        if (!is_constant(fn))
            return false;
        name const & n  = const_name(fn);
        constant_info info = env().get(n);
        if (!info.is_definition() || is_projection(env(), n) || is_no_confusion(env(), n) ||
            ::lean::is_aux_recursor(env(), n) || is_user_defined_recursor(env(), n))
            return false;
        return !is_vm_function(env(), n);
    }

    bool is_noncomputable_const(expr const & e) {
        return is_constant(e) && is_noncomputable(env(), const_name(e));
    }

    bool is_inline(expr const & e) {
        return is_constant(e) && ::lean::is_inline(env(), const_name(e));
    }

    bool is_function_being_compiled(expr const & e) const {
        expr const & f = get_app_fn(e);
        return is_constant(f) && m_decl_names.contains(const_name(f));
    }

    bool should_unfold(expr const & e) {
        return
            !is_function_being_compiled(e) &&
            ((is_not_vm_function(e) && !ctx().is_proof(e) && !is_noncomputable_const(e)) ||
             (is_inline(e)));
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
                new_e = ctx().whnf_head_pred(e, [&](expr const & e) { return get_recursor_app_kind(e) == recursor_kind::NotRecursor; });
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
                new_e = ctx().whnf_head_pred(e, [&](expr const & e) { return is_aux_recursor(e); });
            }
            return compiler_step_visitor::visit(new_e);
        }
        lean_unreachable();
    }

public:
    expand_aux_fn(environment const & env, name_set const & decl_names, abstract_context_cache & cache):
        compiler_step_visitor(env, cache),
        m_decl_names(decl_names) {}
};

static expr expand_aux(environment const & env, name_set const & ns, abstract_context_cache & cache, expr const & e) {
    return expand_aux_fn(env, ns, cache)(e);
}

static name * g_tmp_prefix = nullptr;

class preprocess_fn {
    environment    m_env;
    context_cache  m_cache;
    name_set       m_decl_names; /* name of the functions being compiled */

    bool check(constant_info const & d, expr const & v) {
        bool non_meta_only = false;
        type_checker tc(m_env, non_meta_only);
        expr t = tc.check(v, d.get_lparams());
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

    /* If type of d is a proposition or return a type, we don't need to compile it.
       We can just generate (fun args, neutral_expr)

       This procedure returns true if type of d is a proposition or return a type,
       and store the dummy code above in */
    bool compile_irrelevant(constant_info const & d, buffer<procedure> & procs) {
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

    expr remove_meta_rec(expr const & e) {
        return replace(e, [&](expr const & c, unsigned) {
                if (is_constant(c)) {
                    if (optional<name> new_c = is_meta_rec_name(const_name(c)))
                        return some_expr(mk_constant(*new_c, const_levels(c)));
                }
                return none_expr();
            });
    }

    void exec_new_compiler(constant_info const & d) {
        name n  = get_real_name(d.get_name());
        // timeit timer(std::cout, (sstream() << "compiling " << n).str().c_str(), 0.05);
        expr v  = d.get_value();
        // TODO(Leo): add option for disabling eta-expansion
        v       = type_checker(m_env, local_ctx()).eta_expand(v);
        lean_trace(name({"compiler", "eta_expand"}), tout() << n << "\n" << v << "\n";);
        v       = to_lcnf(m_env, local_ctx(), v);
        lean_trace(name({"compiler", "lcnf"}), tout() << n << "\n" << v << "\n";);
        lean_cond_assert("compiler", check(d, v));
        v       = cce(m_env, local_ctx(), v);
        lean_trace(name({"compiler", "cce"}), tout() << n << "\n" << v << "\n";);
        lean_cond_assert("compiler", check(d, v));
        v       = csimp(m_env, local_ctx(), v);
        lean_cond_assert("compiler", check(d, v));
        lean_trace(name({"compiler", "simp"}), tout() << "\n" << v << "\n";);
        v       = elim_dead_let(v);
        lean_trace(name({"compiler", "elim_dead_let"}), tout() << "\n" << v << "\n";);
        lean_cond_assert("compiler", check(d, v));
        v       = cse(m_env, v);
        lean_trace(name({"compiler", "cse"}), tout() << "\n" << v << "\n";);
        lean_cond_assert("compiler", check(d, v));
        // std::cout << "done compiling " << n << "\n";
        v       = max_sharing(v);
        lean_trace(name({"compiler", "stage1"}), tout() << n << "\n" << v << "\n";);
        declaration simp_decl = mk_definition(mk_cstage1_name(n), d.get_lparams(), d.get_type(),
                                              v, reducibility_hints::mk_opaque(), true);
        /* IMPORTANT: We do not need to save the auxiliary declaration in the environment.
           This is just a temporary hack.
           We should store this information in a different place. In the meantime,
           I just invoke `module::add` with `check = false`. This is a temporary
           solution since we will not have this parameter in the final version. */
        m_env = module::add(m_env, simp_decl, false);
    }

    name get_real_name(name const & n) {
        if (optional<name> new_n = is_meta_rec_name(n))
            return *new_n;
        else
            return n;
    }

public:
    preprocess_fn(environment const & env, constant_info const & d):
        m_env(env) {
        m_decl_names.insert(get_real_name(d.get_name()));
    }

    preprocess_fn(environment const & env, buffer<constant_info> const & ds):
        m_env(env) {
        for (constant_info const & d : ds)
            m_decl_names.insert(get_real_name(d.get_name()));
    }

    environment const & env() const { return m_env; }

    environment operator()(constant_info const & d, buffer<procedure> & procs) {
        lean_trace(name({"compiler", "input"}), tout() << d.get_name() << "\n";);
        if (compile_irrelevant(d, procs))
            return m_env;
        exec_new_compiler(d);
        expr v = d.get_value();
        v = remove_meta_rec(v);
        lean_trace(name({"compiler", "input"}), tout() << "\n" << v << "\n";);
        v = inline_simple_definitions(m_env, m_cache, v);
        lean_cond_assert("compiler", check(d, v));
        lean_trace(name({"compiler", "inline"}), tout() << "\n" << v << "\n";);
        v = expand_aux(m_env, m_decl_names, m_cache, v);
        lean_cond_assert("compiler", check(d, v));
        lean_trace(name({"compiler", "expand_aux"}), tout() << "\n" << v << "\n";);
        v = mark_comp_irrelevant_subterms(m_env, m_cache, v);
        lean_cond_assert("compiler", check(d, v));
        v = find_nat_values(m_env, v);
        lean_cond_assert("compiler", check(d, v));
        v = eta_expand(m_env, m_cache, v);
        lean_cond_assert("compiler", check(d, v));
        lean_trace(name({"compiler", "eta_expansion"}), tout() << "\n" << v << "\n";);
        name n = get_real_name(d.get_name());
        v = elim_recursors(m_env, m_cache, n, v, procs);
        procs.emplace_back(n, optional<pos_info>(), v);
        lean_cond_assert("compiler", check(d, procs.back().m_code));
        lean_trace(name({"compiler", "elim_recursors"}), tout() << "\n"; display(procs););
        erase_irrelevant(procs);
        lean_trace(name({"compiler", "erase_irrelevant"}), tout() << "\n"; display(procs););
        reduce_arity(m_env, m_cache, procs);
        lean_trace(name({"compiler", "reduce_arity"}), tout() << "\n"; display(procs););
        erase_trivial_structures(m_env, m_cache, procs);
        lean_trace(name({"compiler", "erase_trivial_structures"}), tout() << "\n"; display(procs););
        lambda_lifting(m_env, m_cache, n, procs);
        lean_trace(name({"compiler", "lambda_lifting"}), tout() << "\n"; display(procs););
        simp_inductive(m_env, m_cache, procs);
        lean_trace(name({"compiler", "simplify_inductive"}), tout() << "\n"; display(procs););
        elim_unused_lets(m_env, m_cache, procs);
        lean_trace(name({"compiler", "elim_unused_lets"}), tout() << "\n"; display(procs););
        extract_values(m_env, m_cache, n, procs);
        lean_trace(name({"compiler", "extract_values"}), tout() << "\n"; display(procs););
        old_cse(m_env, m_cache, procs);
        lean_trace(name({"compiler", "cse"}), tout() << "\n"; display(procs););
        lean_trace(name({"compiler", "preprocess"}), tout() << "\n"; display(procs););
        return m_env;
    }
};

environment preprocess(environment const & env, constant_info const & d, buffer<procedure> & result) {
    return preprocess_fn(env, d)(d, result);
}

environment preprocess(environment const & env, buffer<constant_info> const & ds, buffer<procedure> & result) {
    preprocess_fn F(env, ds);
    for (constant_info const & d : ds) {
        buffer<procedure> procs;
        F(d, procs);
        result.append(procs);
    }
    return F.env();
}

void initialize_preprocess() {
    register_trace_class("compiler");
    register_trace_class({"compiler", "input"});
    register_trace_class({"compiler", "eta_expand"});
    register_trace_class({"compiler", "lcnf"});
    register_trace_class({"compiler", "elim_dead_let"});
    register_trace_class({"compiler", "cce"});
    register_trace_class({"compiler", "simp"});
    register_trace_class({"compiler", "stage1"});
    register_trace_class({"compiler", "expand_aux"});
    register_trace_class({"compiler", "eta_expansion"});
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
