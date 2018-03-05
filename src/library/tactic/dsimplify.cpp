/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "util/interrupt.h"
#include "kernel/instantiate.h"
#include "library/defeq_canonizer.h"
#include "library/constants.h"
#include "library/fun_info.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/reducible.h"
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/dsimplify.h"
#include "library/tactic/simp_lemmas.h"
#include "library/tactic/tactic_state.h"

#ifndef LEAN_DEFAULT_DSIMPLIFY_MAX_STEPS
#define LEAN_DEFAULT_DSIMPLIFY_MAX_STEPS 1000000
#endif

namespace lean {
expr reduce_beta_eta_proj_iota(type_context_old & ctx, expr e, bool beta, bool eta, bool proj, bool iota) {
    bool p;
    do {
        p = false;
        if (beta) {
            expr new_e = head_beta_reduce(e);
            if (!is_eqp(new_e, e)) {
                e = new_e;
                p = true;
            }
        }
        if (proj) {
            if (auto v = ctx.reduce_projection(e)) {
                e = *v;
                p = true;
            }
        }
        if (eta) {
            expr new_e = try_eta(e);
            if (!is_eqp(new_e, e)) {
                e = new_e;
                p = true;
            }
        }
        if (iota) {
            if (auto v = ctx.reduce_recursor(e)) {
                e = *v;
                p = true;
            }
        }
    } while (p);
    return e;
}

optional<expr> unfold_step(type_context_old & ctx, expr const & e, name_set const & to_unfold, bool unfold_reducible) {
    if (!unfold_reducible && to_unfold.empty())
        return none_expr();
    if (!is_app(e) && !is_constant(e))
        return none_expr();
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        return none_expr();
    name const & fn_name = const_name(fn);

    bool in_to_unfold = to_unfold.contains(const_name(fn));

    if (!in_to_unfold && !unfold_reducible)
        return none_expr();

    if (is_projection(ctx.env(), const_name(fn))) {
        if (in_to_unfold) {
            type_context_old::transparency_scope scope(ctx, transparency_mode::Instances);
            return ctx.reduce_projection(e);
        } else {
            return none_expr();
        }
    } else if (in_to_unfold) {
        return unfold_term(ctx.env(), e);
    } else if (unfold_reducible && is_reducible(ctx.env(), fn_name)) {
        type_context_old::transparency_scope scope(ctx, transparency_mode::Reducible);
        return unfold_term(ctx.env(), e);
    } else {
        return none_expr();
    }
}

dsimp_config::dsimp_config():
    m_md(transparency_mode::Reducible),
    m_max_steps(LEAN_DEFAULT_DSIMPLIFY_MAX_STEPS),
    m_canonize_instances(true),
    m_single_pass(false),
    m_fail_if_unchanged(true),
    m_eta(false),
    m_zeta(false),
    m_beta(true),
    m_proj(true),
    m_iota(true),
    m_unfold_reducible(false),
    m_memoize(true) {
}
dsimp_config::dsimp_config(vm_obj const & o) {
    m_md                 = to_transparency_mode(cfield(o, 0));
    m_max_steps          = force_to_unsigned(cfield(o, 1));
    m_canonize_instances = to_bool(cfield(o, 2));
    m_single_pass        = to_bool(cfield(o, 3));
    m_fail_if_unchanged  = to_bool(cfield(o, 4));
    m_eta                = to_bool(cfield(o, 5));
    m_zeta               = to_bool(cfield(o, 6));
    m_beta               = to_bool(cfield(o, 7));
    m_proj               = to_bool(cfield(o, 8));
    m_iota               = to_bool(cfield(o, 9));
    m_unfold_reducible   = to_bool(cfield(o, 10));
    m_memoize            = to_bool(cfield(o, 11));
}

#define lean_dsimp_trace(CTX, N, CODE) lean_trace(N, scope_trace_env _scope1(CTX.env(), CTX); CODE)

optional<pair<expr, bool>> dsimplify_core_fn::pre(expr const &) {
    return optional<pair<expr, bool>>();
}

optional<pair<expr, bool>> dsimplify_core_fn::post(expr const &) {
    return optional<pair<expr, bool>>();
}

expr dsimplify_core_fn::visit_macro(expr const & e) {
    buffer<expr> new_args;
    for (unsigned i = 0; i < macro_num_args(e); i++)
        new_args.push_back(visit(macro_arg(e, i)));
    return update_macro(e, new_args.size(), new_args.data());
}

expr dsimplify_core_fn::visit_binding(expr const & e) {
    expr_kind k = e.kind();
    type_context_old::tmp_locals locals(m_ctx);
    expr b = e;
    bool modified = false;
    while (b.kind() == k) {
        expr d = instantiate_rev(binding_domain(b), locals.size(), locals.data());
        expr new_d = visit(d);
        if (!is_eqp(d, new_d)) modified = true;
        locals.push_local(binding_name(b), new_d, binding_info(b));
        b = binding_body(b);
    }
    b = instantiate_rev(b, locals.size(), locals.data());
    expr new_b = visit(b);
    if (!is_eqp(b, new_b)) modified = true;
    if (modified)
        return k == expr_kind::Pi ? locals.mk_pi(new_b) : locals.mk_lambda(new_b);
    else
        return e;
}

expr dsimplify_core_fn::visit_let(expr const & e) {
    if (m_cfg.m_zeta) {
        return visit(instantiate(let_body(e), let_value(e)));
    } else {
        type_context_old::tmp_locals locals(m_ctx);
        expr b = e;
        bool modified = false;
        while (is_let(b)) {
            expr t     = instantiate_rev(let_type(b), locals.size(), locals.data());
            expr v     = instantiate_rev(let_value(b), locals.size(), locals.data());
            expr new_t = visit(t);
            expr new_v = visit(v);
            if (!is_eqp(t, new_t) || !is_eqp(v, new_v)) modified = true;
            locals.push_let(let_name(b), new_t, new_v);
            b = let_body(b);
        }
        b = instantiate_rev(b, locals.size(), locals.data());
        expr new_b = visit(b);
        if (!is_eqp(b, new_b)) modified = true;
        if (modified)
            return locals.mk_lambda(new_b);
        else
            return e;
    }
}

expr dsimplify_core_fn::visit_app(expr const & e) {
    buffer<expr> args;
    bool modified = false;
    expr f        = get_app_args(e, args);
    unsigned i    = 0;
    if (!m_cfg.m_canonize_instances) {
        fun_info info = get_fun_info(m_ctx, f, args.size());
        for (param_info const & pinfo : info.get_params_info()) {
            lean_assert(i < args.size());
            expr new_a;
            if (pinfo.is_inst_implicit()) {
                new_a = m_defeq_canonizer.canonize(args[i], m_need_restart);
            } else {
                new_a = visit(args[i]);
            }
            if (new_a != args[i])
                modified = true;
            args[i] = new_a;
            i++;
        }
    }
    for (; i < args.size(); i++) {
        expr new_a = visit(args[i]);
        if (new_a != args[i])
            modified = true;
        args[i] = new_a;
    }
    if (modified)
        return mk_app(f, args);
    else
        return e;
}

expr dsimplify_core_fn::visit_meta(expr const & e) {
    return m_ctx.instantiate_mvars(e);
}

void dsimplify_core_fn::inc_num_steps() {
    m_num_steps++;
    if (m_num_steps > m_cfg.m_max_steps)
        throw exception("dsimplify failed, maximum number of steps exceeded");
}

expr dsimplify_core_fn::visit(expr const & e) {
    check_system("dsimplify");
    inc_num_steps();

    lean_trace_inc_depth("dsimplify");
    lean_dsimp_trace(m_ctx, "dsimplify", tout() << e << "\n";);

    if (m_cfg.m_memoize) {
        auto it = m_cache.find(e);
        if (it != m_cache.end())
            return it->second;
    }

    expr curr_e = e;
    if (auto p1 = pre(curr_e)) {
        if (!p1->second) {
            if (m_cfg.m_memoize)
                m_cache.insert(mk_pair(e, p1->first));
            return p1->first;
        }
        curr_e = p1->first;
    }

    while (true) {
        expr new_e;
        switch (curr_e.kind()) {
        case expr_kind::Local:
        case expr_kind::Sort:
        case expr_kind::Constant:
            new_e = curr_e;
            break;
        case expr_kind::Var:
            lean_unreachable();
        case expr_kind::Meta:
            new_e = visit_meta(curr_e);
            break;
        case expr_kind::Macro:
            new_e = visit_macro(curr_e);
            break;
        case expr_kind::Lambda:
        case expr_kind::Pi:
            new_e = visit_binding(curr_e);
            break;
        case expr_kind::App:
            new_e = visit_app(curr_e);
            break;
        case expr_kind::Let:
            new_e = visit_let(curr_e);
            break;
        }

        if (auto p2 = post(new_e)) {
            if (!p2->second || p2->first == curr_e) {
                curr_e = p2->first;
                break;
            }
            curr_e = p2->first;
            if (m_cfg.m_single_pass)
                break;
        } else {
            curr_e = new_e;
            break;
        }
    }
    if (m_cfg.m_memoize)
        m_cache.insert(mk_pair(e, curr_e));
    return curr_e;
}

dsimplify_core_fn::dsimplify_core_fn(type_context_old & ctx, defeq_canonizer::state & dcs, dsimp_config const & cfg):
    m_ctx(ctx), m_defeq_canonizer(ctx, dcs), m_num_steps(0), m_need_restart(false), m_cfg(cfg) {}

expr dsimplify_core_fn::operator()(expr e) {
    while (true) {
        m_need_restart = false;
        e = visit(e);
        if (!m_need_restart || m_cfg.m_single_pass)
            return e;
        m_cache.clear();
    }
}

metavar_context const & dsimplify_core_fn::mctx() const {
    return m_ctx.mctx();
}

expr dsimplify_fn::reduce(expr const & e) {
    return reduce_beta_eta_proj_iota(m_ctx, e, m_cfg.m_beta, m_cfg.m_eta, m_cfg.m_proj, m_cfg.m_iota);
}

optional<pair<expr, bool>> dsimplify_fn::pre(expr const & e) {
    type_context_old::transparency_scope s(m_ctx, m_cfg.m_md);
    expr new_e = reduce(e);
    if (new_e != e) {
        lean_dsimp_trace(m_ctx, "dsimplify", tout() << "reduce\n" << e << "\n==>\n" << new_e << "\n";);
        return optional<pair<expr, bool>>(new_e, true);
    } else {
        return optional<pair<expr, bool>>();
    }
}

optional<pair<expr, bool>> dsimplify_fn::post(expr const & e) {
    if (auto r = unfold_step(m_ctx, e, m_to_unfold, m_cfg.m_unfold_reducible))
        return optional<pair<expr, bool>>(*r, true);
    expr curr_e;
    {
        type_context_old::transparency_scope s(m_ctx, m_cfg.m_md);
        curr_e = reduce(e);
        if (curr_e != e) {
            lean_dsimp_trace(m_ctx, "dsimplify", tout() << "reduce\n" << e << "\n==>\n" << curr_e << "\n";);
        }
    }
    while (true) {
        check_system("dsimplify");
        inc_num_steps();
        list<simp_lemma> const * simp_lemmas_ptr = m_simp_lemmas.find(curr_e);
        if (!simp_lemmas_ptr) break;
        buffer<simp_lemma> simp_lemmas;
        to_buffer(*simp_lemmas_ptr, simp_lemmas);

        expr new_e = curr_e;
        for (simp_lemma const & sl : simp_lemmas) {
            if (sl.is_refl()) {
                lean_dsimp_trace(m_ctx, name({"debug", "dsimplify"}),
                                 tout() << "try rewrite " << sl.get_id() << "\n";);
                new_e = refl_lemma_rewrite(m_ctx, curr_e, sl);
                if (new_e != curr_e)
                    break;
            }
        }
        if (new_e == curr_e) break;
        lean_dsimp_trace(m_ctx, "dsimplify", tout() << "rewrite\n" << curr_e << "\n==>\n" << new_e << "\n";);
        curr_e = new_e;
        if (m_cfg.m_single_pass)
            break;
    }
    if (curr_e == e)
        return optional<pair<expr, bool>>();
    else
        return optional<pair<expr, bool>>(curr_e, true);
}

dsimplify_fn::dsimplify_fn(type_context_old & ctx, defeq_canonizer::state & dcs, simp_lemmas_for const & lemmas,
                           list<name> const & to_unfold, dsimp_config const & cfg):
    dsimplify_core_fn(ctx, dcs, cfg),
    m_simp_lemmas(lemmas),
    m_to_unfold(to_name_set(to_unfold)) {
}

class tactic_dsimplify_fn : public dsimplify_core_fn {
    vm_obj       m_a;
    vm_obj       m_pre;
    vm_obj       m_post;
    tactic_state m_s;

    optional<pair<expr, bool>> invoke_fn(vm_obj const & fn, expr const & e) {
        m_s = set_mctx_lctx_dcs(m_s, m_ctx.mctx(), m_ctx.lctx(), m_defeq_canonizer.get_state());
        vm_obj r = invoke(fn, m_a, to_obj(e), to_obj(m_s));
        if (optional<tactic_state> new_s = tactic::is_success(r)) {
            m_s = *new_s;
            m_ctx.set_mctx(m_s.mctx());
            m_defeq_canonizer.set_state(m_s.dcs());
            vm_obj p   = tactic::get_success_value(r);
            m_a        = cfield(p, 0);
            vm_obj p1  = cfield(p, 1);
            expr new_e = to_expr(cfield(p1, 0));
            bool flag  = to_bool(cfield(p1, 1));
            return optional<pair<expr, bool>>(new_e, flag);
        } else {
            return optional<pair<expr, bool>>();
        }
    }

    virtual optional<pair<expr, bool>> pre(expr const & e) override {
        return invoke_fn(m_pre, e);
    }

    virtual optional<pair<expr, bool>> post(expr const & e) override {
        return invoke_fn(m_post, e);
    }

public:
    tactic_dsimplify_fn(type_context_old & ctx, defeq_canonizer::state & dcs,
                        vm_obj const & a, vm_obj const & pre, vm_obj const & post,
                        tactic_state const & s, dsimp_config const & cfg):
        dsimplify_core_fn(ctx, dcs, cfg),
        m_a(a),
        m_pre(pre),
        m_post(post),
        m_s(s) {
    }

    vm_obj const & get_a() const { return m_a; }
};

vm_obj tactic_dsimplify_core(vm_obj const &, vm_obj const & a,
                             vm_obj const & pre, vm_obj const & post, vm_obj const & e,
                             vm_obj const & _cfg, vm_obj const & _s) {
    tactic_state s = tactic::to_state(_s);
    dsimp_config cfg(_cfg);
    try {
        tactic_state_context_cache cache(s);
        type_context_old ctx = cache.mk_type_context(cfg.m_md);
        defeq_can_state dcs = s.dcs();
        tactic_dsimplify_fn F(ctx, dcs, a, pre, post, s, cfg);
        expr new_e = F(to_expr(e));
        if (cfg.m_fail_if_unchanged && to_expr(e) == new_e) {
            return tactic::mk_exception("dsimplify tactic failed to simplify", s);
        } else {
            tactic_state new_s = set_mctx_dcs(s, F.mctx(), dcs);
            return tactic::mk_success(mk_vm_pair(F.get_a(), to_obj(new_e)), new_s);
        }
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj simp_lemmas_dsimplify(vm_obj const & lemmas, vm_obj const & u, vm_obj const & e, vm_obj const & _cfg, vm_obj const & _s) {
    tactic_state s = tactic::to_state(_s);
    dsimp_config cfg(_cfg);
    try {
        tactic_state_context_cache cache(s);
        type_context_old ctx     = cache.mk_type_context(cfg.m_md);
        defeq_can_state dcs  = s.dcs();
        list<name> to_unfold = to_list_name(u);
        simp_lemmas_for dlemmas;
        if (auto * dls = to_simp_lemmas(lemmas).find(get_eq_name()))
            dlemmas = *dls;
        dsimplify_fn F(ctx, dcs, dlemmas, to_unfold, cfg);
        expr new_e = F(to_expr(e));
        if (cfg.m_fail_if_unchanged && to_expr(e) == new_e) {
            return tactic::mk_exception("dsimplify tactic failed to simplify", s);
        } else {
            tactic_state new_s = set_mctx_dcs(s, F.mctx(), dcs);
            return tactic::mk_success(to_obj(new_e), new_s);
        }
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

void initialize_dsimplify() {
    register_trace_class("dsimplify");
    register_trace_class(name{"debug", "dsimplify"});
    DECLARE_VM_BUILTIN(name({"tactic", "dsimplify_core"}), tactic_dsimplify_core);
    DECLARE_VM_BUILTIN(name({"simp_lemmas", "dsimplify"}), simp_lemmas_dsimplify);
}

void finalize_dsimplify() {
}
}
