/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/attribute_manager.h"
#include "library/trace.h"
#include "library/simp_lemmas.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_name.h"
#include "library/tactic/simp_result.h"
#include "library/tactic/tactic_state.h"

namespace lean {
struct vm_simp_lemmas : public vm_external {
    simp_lemmas m_val;
    vm_simp_lemmas(simp_lemmas const & v): m_val(v) {}
    virtual ~vm_simp_lemmas() {}
    virtual void dealloc() override { this->~vm_simp_lemmas(); get_vm_allocator().deallocate(sizeof(vm_simp_lemmas), this); }
};

simp_lemmas const & to_simp_lemmas(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_simp_lemmas*>(to_external(o)));
    return static_cast<vm_simp_lemmas*>(to_external(o))->m_val;
}

vm_obj to_obj(simp_lemmas const & idx) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_simp_lemmas))) vm_simp_lemmas(idx));
}

vm_obj tactic_mk_default_simp_lemmas(vm_obj const & m, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    environment const & env = to_tactic_state(s).env();
    simp_lemmas r = get_default_simp_lemmas(env, to_transparency_mode(m));
    return mk_tactic_success(to_obj(r), to_tactic_state(s));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

vm_obj tactic_simp_lemmas_insert(vm_obj const & m, vm_obj const & lemmas, vm_obj const & lemma, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context tctx = mk_type_context_for(s, m);
    expr e = to_expr(lemma);
    name id;
    if (is_constant(e))
        id = const_name(e);
    else if (is_local(e))
        id = local_pp_name(e);

    expr e_type = tctx.infer(e);
    // TODO(dhs): accept priority as an argument
    // Reason for postponing: better plumbing of numerals through the vm
    simp_lemmas new_lemmas = add(tctx, to_simp_lemmas(lemmas), id, tctx.infer(e), e, LEAN_DEFAULT_PRIORITY);
    return mk_tactic_success(to_obj(new_lemmas), to_tactic_state(s));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

vm_obj tactic_simp_lemmas_insert_constant(vm_obj const & m, vm_obj const & lemmas, vm_obj const & lemma_name, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context ctx = mk_type_context_for(s, m);
    simp_lemmas new_lemmas = add(ctx, to_simp_lemmas(lemmas), to_name(lemma_name), LEAN_DEFAULT_PRIORITY);
    return mk_tactic_success(to_obj(new_lemmas), to_tactic_state(s));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

vm_obj simp_lemmas_mk() {
    return to_obj(simp_lemmas());
}

vm_obj simp_lemmas_join(vm_obj const & lemmas1, vm_obj const & lemmas2) {
    return to_obj(join(to_simp_lemmas(lemmas1), to_simp_lemmas(lemmas2)));
}

vm_obj simp_lemmas_erase(vm_obj const & lemmas, vm_obj const & lemma_list) {
    name_set S;
    for (name const & l : to_list_name(lemma_list))
        S.insert(l);
    simp_lemmas new_lemmas = to_simp_lemmas(lemmas);
    new_lemmas.erase(S);
    return to_obj(new_lemmas);
}

static optional<expr> prove(type_context & ctx, vm_obj const & prove_fn, expr const & e) {
    tactic_state s         = mk_tactic_state_for(ctx.env(), ctx.get_options(), ctx.lctx(), e);
    vm_obj r_obj           = invoke(prove_fn, to_obj(s));
    optional<tactic_state> s_new = is_tactic_success(r_obj);
    if (!s_new || s_new->goals()) return none_expr();
    metavar_context mctx   = s_new->mctx();
    expr result            = mctx.instantiate_mvars(s_new->main());
    if (has_expr_metavar(result)) return none_expr();
    ctx.set_mctx(mctx);
    return some_expr(result);
}

static bool instantiate_emetas(type_context & ctx, vm_obj const & prove_fn, unsigned num_emeta, list<expr> const & emetas, list<bool> const & instances) {
    environment const & env = ctx.env();
    bool failed = false;
    unsigned i  = num_emeta;
    for_each2(emetas, instances, [&](expr const & m, bool const & is_instance) {
            i--;
            if (failed) return;
            expr m_type = ctx.instantiate_mvars(ctx.infer(m));
            if (has_metavar(m_type)) {
                failed = true;
                return;
            }

            if (ctx.get_tmp_mvar_assignment(i)) return;

            if (is_instance) {
                if (auto v = ctx.mk_class_instance(m_type)) {
                    if (!ctx.is_def_eq(m, *v)) {
                        lean_trace("simp_lemmas", scope_trace_env scope(env, ctx);
                                   tout() << "unable to assign instance for: " << m_type << "\n";);
                        failed = true;
                        return;
                    }
                } else {
                    lean_trace("simp_lemmas", scope_trace_env scope(env, ctx);
                               tout() << "unable to synthesize instance for: " << m_type << "\n";);
                    failed = true;
                    return;
                }
            }

            if (ctx.get_tmp_mvar_assignment(i)) return;

            // Note: m_type has no metavars
            if (ctx.is_prop(m_type)) {
                if (auto pf = prove(ctx, prove_fn, m_type)) {
                    lean_verify(ctx.is_def_eq(m, *pf));
                    return;
                }
            }

            lean_trace("simp_lemmas", scope_trace_env scope(env, ctx);
                       tout() << "failed to assign: " << m << " : " << m_type << "\n";);

            failed = true;
            return;
        });

    return !failed;
}


static simp_result simp_lemma_apply(type_context & ctx, simp_lemma const & sl, vm_obj const & prove_fn, expr const & e) {
    type_context::tmp_mode_scope scope(ctx, sl.get_num_umeta(), sl.get_num_emeta());
    if (!ctx.is_def_eq(e, sl.get_lhs())) {
        lean_trace("simp_lemmas", tout() << "fail to unify: " << sl.get_id() << "\n";);
        return simp_result(e);
    }

    if (!instantiate_emetas(ctx, prove_fn, sl.get_num_emeta(), sl.get_emetas(), sl.get_instances())) {
        lean_trace("simp_lemmas", tout() << "fail to instantiate emetas: " << sl.get_id() << "\n";);
        return simp_result(e);
    }

    for (unsigned i = 0; i < sl.get_num_umeta(); i++) {
        if (!ctx.get_tmp_uvar_assignment(i)) return simp_result(e);
    }

    expr new_lhs = ctx.instantiate_mvars(sl.get_lhs());
    expr new_rhs = ctx.instantiate_mvars(sl.get_rhs());
    if (sl.is_permutation()) {
        if (!is_lt(new_rhs, new_lhs, false)) {
            lean_trace("simp_lemmas", scope_trace_env scope(ctx.env(), ctx);
                       tout() << "perm rejected: " << new_rhs << " !< " << new_lhs << "\n";);
            return simp_result(e);
        }
    }
    if (sl.is_refl()) {
        return simp_result(new_rhs);
    } else {
        expr pf = ctx.instantiate_mvars(sl.get_proof());
        return simp_result(new_rhs, pf);
    }
}

vm_obj simp_lemmas_apply(transparency_mode const & m, simp_lemmas const & sls, vm_obj const & prove_fn,
                         name const & R, expr const & e, tactic_state const & s) {
    LEAN_TACTIC_TRY;
    simp_lemmas_for const * sr = sls.find(R);
    if (!sr) return mk_tactic_exception("failed to apply simp_lemmas, no lemmas for the given relation", s);

    list<simp_lemma> const * srs = sr->find(e);
    if (!srs) return mk_tactic_exception("failed to apply simp_lemmas, no simp lemma", s);

    type_context ctx = mk_type_context_for(s, m);

    for (simp_lemma const & lemma : *srs) {
        simp_result r = simp_lemma_apply(ctx, lemma, prove_fn, e);
        if (!is_eqp(r.get_new(), e)) {
            lean_trace("simp_lemmas", scope_trace_env scope(ctx.env(), ctx);
                       tout() << "[" << lemma.get_id() << "]: " << e << " ==> " << r.get_new() << "\n";);
            vm_obj new_e  = to_obj(r.get_new());
            vm_obj new_pr = to_obj(r.get_proof());
            return mk_tactic_success(mk_vm_pair(new_e, new_pr), s);
        }
    }
    return mk_tactic_exception("failed to apply simp_lemmas, no simp lemma", s);
    LEAN_TACTIC_CATCH(s);
}

static vm_obj tactic_simp_lemmas_apply(vm_obj const & m, vm_obj const & sls, vm_obj const & prove_fn,
                                       vm_obj const & R, vm_obj const & e, vm_obj const & s) {
    return simp_lemmas_apply(to_transparency_mode(m), to_simp_lemmas(sls), prove_fn,
                             to_name(R), to_expr(e), to_tactic_state(s));
}

void initialize_simp_lemmas_tactics() {
    DECLARE_VM_BUILTIN(name({"simp_lemmas", "mk"}), simp_lemmas_mk);
    DECLARE_VM_BUILTIN(name({"simp_lemmas", "join"}), simp_lemmas_join);
    DECLARE_VM_BUILTIN(name({"simp_lemmas", "erase"}), simp_lemmas_erase);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_default_simp_lemmas_core"}),      tactic_mk_default_simp_lemmas);
    DECLARE_VM_BUILTIN(name({"tactic", "simp_lemmas_insert_core"}),          tactic_simp_lemmas_insert);
    DECLARE_VM_BUILTIN(name({"tactic", "simp_lemmas_insert_constant_core"}), tactic_simp_lemmas_insert_constant);
    DECLARE_VM_BUILTIN(name({"tactic", "simp_lemmas_apply_core"}),           tactic_simp_lemmas_apply);
}

void finalize_simp_lemmas_tactics() {
}
}
