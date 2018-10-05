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
#include "library/compiler/preprocess.h"
#include "library/compiler/compiler_step_visitor.h"
#include "library/compiler/lambda_lifting.h"
#include "library/compiler/simp_inductive.h"

#include "library/compiler/util.h"
#include "library/compiler/lcnf.h"
#include "library/compiler/csimp.h"
#include "library/compiler/elim_dead_let.h"
#include "library/compiler/cse.h"
#include "library/compiler/specialize.h"
#include "library/compiler/erase_irrelevant.h"

namespace lean {
class preprocess_fn {
    environment    m_env;
    context_cache  m_cache;
    name_set       m_decl_names; /* name of the functions being compiled */

    void display(buffer<procedure> const & procs) {
        for (auto const & p : procs) {
            tout() << ">> " << p.m_name << "\n" << p.m_code << "\n";
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
            expr r = locals.mk_lambda(mk_enf_neutral());
            procs.emplace_back(d.get_name(), r);
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
        name n = get_real_name(d.get_name());
        expr v = d.get_value();

        v       = type_checker(m_env, local_ctx()).eta_expand(v);
        lean_trace(name({"compiler", "eta_expand"}), tout() << n << "\n" << v << "\n";);
        v       = to_lcnf(m_env, v);
        lean_trace(name({"compiler", "lcnf"}), tout() << n << "\n" << v << "\n";);
        v       = cce(m_env, v);
        lean_trace(name({"compiler", "cce"}), tout() << n << "\n" << v << "\n";);
        v       = csimp(m_env, v);
        lean_trace(name({"compiler", "simp"}), tout() << "\n" << v << "\n";);
        v       = elim_dead_let(v);
        lean_trace(name({"compiler", "elim_dead_let"}), tout() << "\n" << v << "\n";);
        v       = cse(m_env, v);
        lean_trace(name({"compiler", "cse"}), tout() << "\n" << v << "\n";);
        std::tie(m_env, v) = specialize(m_env, local_ctx(), v);
        lean_trace(name({"compiler", "specialize"}), tout() << "\n" << v << "\n";);
        v       = max_sharing(v);
        lean_trace(name({"compiler", "stage1"}), tout() << n << "\n" << v << "\n";);
        declaration simp_decl = mk_definition(mk_cstage1_name(n), d.get_lparams(), d.get_type(),
                                              v, reducibility_hints::mk_opaque(), true);
        /* IMPORTANT: We do not need to save the auxiliary declaration in the environment.
           This is just a temporary hack.
           We should store this information in a different place. In the meantime,
           I just invoke `module::add` with `check = false`. This is a temporary
           solution since we will not have this parameter in the final version. */
        m_env   = module::add(m_env, simp_decl, false);
        v       = erase_irrelevant(m_env, v);
        lean_trace(name({"compiler", "erase_irrelevant"}), tout() << "\n" << v << "\n";);
        procs.emplace_back(n, v);

        lambda_lifting(m_env, m_cache, n, procs);
        lean_trace(name({"compiler", "lambda_lifting"}), tout() << "\n"; display(procs););

        for (procedure & p : procs) {
            p.m_code = elim_dead_let(p.m_code);
            p.m_code = cse(m_env, p.m_code);
        }

        simp_inductive(m_env, m_cache, procs);
        lean_trace(name({"compiler", "simplify_inductive"}), tout() << "\n"; display(procs););
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
    register_trace_class({"compiler", "specialize"});
    register_trace_class({"compiler", "erase_irrelevant"});
    register_trace_class({"compiler", "lambda_lifting"});
    register_trace_class({"compiler", "simplify_inductive"});
    register_trace_class({"compiler", "cse"});
}

void finalize_preprocess() {
}
}
