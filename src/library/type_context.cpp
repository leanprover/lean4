/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "runtime/interrupt.h"
#include "runtime/flet.h"
#include "util/option_declarations.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/quot.h"
#include "kernel/inductive.h"
#include "library/error_msgs.h"
#include "library/trace.h"
#include "library/class.h"
#include "library/pp_options.h"
#include "library/annotation.h"
#include "library/idx_metavar.h"
#include "library/reducible.h"
#include "library/suffixes.h"
#include "library/constants.h"
#include "library/metavar_util.h"
#include "library/exception.h"
#include "library/type_context.h"
#include "library/locals.h"
#include "library/aux_recursors.h"
#include "library/fun_info.h"
#include "library/num.h"
#include "library/check.h"
#include "library/aux_match.h"
#include "library/time_task.h"

namespace lean {
bool is_at_least_semireducible(transparency_mode m) {
    return m == transparency_mode::All || m == transparency_mode::Semireducible;
}

bool is_at_least_instances(transparency_mode m) {
    return m == transparency_mode::All || m == transparency_mode::Semireducible || m == transparency_mode::Instances;
}

transparency_mode ensure_semireducible_mode(transparency_mode m) {
    return is_at_least_semireducible(m) ? m : transparency_mode::Semireducible;
}

transparency_mode ensure_instances_mode(transparency_mode m) {
    return is_at_least_instances(m) ? m : transparency_mode::Instances;
}

/* =====================
   type_context_old::tmp_locals
   ===================== */
type_context_old::tmp_locals::~tmp_locals() {
    for (unsigned i = 0; i < m_locals.size(); i++)
        m_ctx.pop_local();
}

bool type_context_old::tmp_locals::all_let_decls() const {
    for (expr const & l : m_locals) {
        if (optional<local_decl> d = m_ctx.m_lctx.find_local_decl(l)) {
            if (!d->get_value())
                return false;
        } else {
            lean_unreachable();
        }
    }
    return true;
}

/* =====================
   type_context_old
   ===================== */

void type_context_old::cache_failure(expr const & t, expr const & s) {
    m_cache->set_is_def_eq_failure(m_transparency_mode, t, s);
}

bool type_context_old::is_cached_failure(expr const & t, expr const & s) {
    if (has_expr_metavar(t) || has_expr_metavar(s)) {
        return false;
    } else {
        return m_cache->get_is_def_eq_failure(m_transparency_mode, t, s);
    }
}

void type_context_old::init_local_instances() {
    m_local_instances = local_instances();
    m_lctx.for_each([&](local_decl const & decl) {
            /* Do not use auxiliary declarations introduced by equation compiler.
               This can happen when using meta definitions.
               Example:

               class has_false (α : Type) :=
               (f : false)

               meta def nat_has_false : has_false ℕ :=
               by apply_instance
            */
            if (!is_rec(decl.get_info())) {
                if (auto cls_name = is_class(decl.get_type())) {
                    m_local_instances = local_instances(local_instance(*cls_name, decl.mk_ref()), m_local_instances);
                }
            }
        });
}

void type_context_old::init_core(transparency_mode m) {
    m_transparency_mode           = m;
    m_smart_unfolding             = m_cache->get_smart_unfolding();
    init_local_instances();
}

type_context_old::type_context_old(environment const & env, options const & o, metavar_context const & mctx,
                                   local_context const & lctx, transparency_mode m):
    m_env(env),
    m_mctx(mctx), m_lctx(lctx),
    m_dummy_cache(o),
    m_cache(&m_dummy_cache) {
    init_core(m);
}

type_context_old::type_context_old(environment const & env, metavar_context const & mctx,
                           local_context const & lctx, abstract_context_cache & cache, transparency_mode m):
    m_env(env),
    m_mctx(mctx), m_lctx(lctx),
    m_cache(&cache) {
    init_core(m);
}

type_context_old::type_context_old(type_context_old && src):
    m_env(std::move(src.m_env)),
    m_mctx(std::move(src.m_mctx)),
    m_lctx(std::move(src.m_lctx)),
    m_dummy_cache(src.get_options()),
    m_cache(src.m_cache == &src.m_dummy_cache ? &m_dummy_cache : src.m_cache),
    m_local_instances(src.m_local_instances),
    m_transparency_mode(src.m_transparency_mode),
    m_unifier_cfg(src.m_unifier_cfg),
    m_zeta(src.m_zeta),
    m_smart_unfolding(src.m_smart_unfolding) {
    lean_assert(!src.m_tmp_data);
    lean_assert(!src.m_used_assignment);
    lean_assert(!src.m_in_is_def_eq);
    lean_assert(src.m_is_def_eq_depth == 0);
    lean_assert(src.m_scopes.empty());
    lean_assert(src.m_update_left);
    lean_assert(src.m_update_right);
    lean_assert(src.m_unfold_depth == 0);
    lean_assert(src.m_postponed.empty());
    lean_assert(src.m_full_postponed);
    lean_assert(!src.m_transparency_pred);
}

type_context_old::~type_context_old() {
}

void type_context_old::set_env(environment const & env) {
    m_env    = env;
}

void type_context_old::update_local_instances(expr const & new_local, expr const & new_type) {
    if (auto c_name = is_class(new_type)) {
        m_local_instances = local_instances(local_instance(*c_name, new_local), m_local_instances);
    }
}

expr type_context_old::push_local(name const & pp_name, expr const & type, binder_info bi) {
    expr local = m_lctx.mk_local_decl(pp_name, type, bi);
    update_local_instances(local, type);
    return local;
}

expr type_context_old::push_let(name const & ppn, expr const & type, expr const & value) {
    expr local = m_lctx.mk_local_decl(ppn, type, value);
    update_local_instances(local, type);
    return local;
}

void type_context_old::pop_local() {
    if (m_local_instances) {
        optional<local_decl> decl = m_lctx.find_last_local_decl();
        if (decl && decl->get_name() == local_name(head(m_local_instances).get_local())) {
            m_local_instances = tail(m_local_instances);
        }
    }
    m_lctx.pop_local_decl();
}

static local_decl get_local_with_smallest_idx(local_context const & lctx, buffer<expr> const & ls) {
    lean_assert(!ls.empty());
    lean_assert(std::all_of(ls.begin(), ls.end(), [&](expr const & l) { return (bool)lctx.find_local_decl(l); })); // NOLINT
    local_decl r = lctx.get_local_decl(ls[0]);
    for (unsigned i = 1; i < ls.size(); i++) {
        local_decl curr = lctx.get_local_decl(ls[i]);
        if (curr.get_idx() < r.get_idx())
            r     = curr;
    }
    return r;
}

/*
Return true iff d is in to_revert[0] ... to_revert[num - 1]
Moreover, if must_sort == false, d is at to_revert[i] and there is j > i s.t. d depends_on to_revert[j], then
   1- Set must_sort = true IF preserve_to_revert_order is false
   2- If preserve_to_revert_order is true, then we get an assertion violation in debug mode,
      and an unreachable code exception in release mode.
*/
static bool process_to_revert(metavar_context const & mctx, buffer<expr> & to_revert, unsigned num,
                              local_decl const & d, bool preserve_to_revert_order, bool & must_sort) {
    for (unsigned i = 0; i < num; i++) {
        if (local_name(to_revert[i]) == d.get_name()) {
            if (!must_sort &&
                depends_on(d, mctx, to_revert.size() - i - 1, to_revert.data() + i + 1)) {
                /* to_revert[i] depends on to_revert[j] for j > i.

                   This can happen when
                   1) User provided a bad order to revert

                     example (n : nat) (h : n < 5) : ... :=
                     begin
                       revert h n
                       ...
                     end

                   2) There is an "in between" dependency.

                     constant p {n m : nat} : n < m → Prop
                     example (n : nat) (h1 : n < 5) (h2 : p h1) : ... :=
                     begin
                       revert n h2
                       ...
                     end

                     h1 depends on n and h2 depends on h1.
                */
                if (preserve_to_revert_order) {
                    /* We use preserve_to_revert_order at induction and subst tactics.

                       For subst, we claim this exception should never be thrown.
                       Reason: given (x : A) (h : x = t), subst h fails if t depends directly
                       or indirectly on x, and to_revert contains x and h initially.

                       For induction, we have a similar situation.
                       The checks performed at induction guarantee this code is not reachable.
                       TODO(Leo): double check this case carefully.
                    */
                    lean_assert(false);
                    lean_unreachable();
                } else {
                    /* Since we do not requre the order to preserved,
                       we just sort the content of to_revert, after we collect all dependencies */
                    must_sort = true;
                }
            }
            return true;
        }
    }
    return false;
}

pair<local_context, expr> type_context_old::revert_core(buffer<expr> & to_revert, local_context const & ctx,
                                                        expr const & type, bool preserve_to_revert_order) {
    unsigned num   = to_revert.size();
    if (num == 0)
        return mk_pair(ctx, type);
    local_decl d0     = get_local_with_smallest_idx(ctx, to_revert);
    bool must_sort    = false;
    process_to_revert(m_mctx, to_revert, num, d0, preserve_to_revert_order, must_sort);
    unsigned num_processed = 1;
    ctx.for_each_after(d0, [&](local_decl const & d) {
            /* Check if d is in initial to_revert */
            if (num_processed < num && process_to_revert(m_mctx, to_revert, num, d, preserve_to_revert_order, must_sort)) {
                num_processed++;
                return;
            }
            /* We may still need to revert d if it depends on locals already in reverted.
               We don't need to follow the value of local definitions (x := v) here because
               we are using for_each_after. */
            if (depends_on(d, m_mctx, to_revert)) {
                if (is_rec(d.get_info())) {
                    /* We should not revert auxiliary declarations added by the equation compiler.
                       See discussion at issue #1258 at github. */
                    sstream out;
                    out << "failed to revert ";
                    for (unsigned i = 0; i < num; i++) {
                        if (i > 0) out << " ";
                        out << "'" << to_revert[i] << "'";
                    }
                    out << ", '" << d.get_user_name() << "' "
                        << "depends on " << (num == 1 ? "it" : "them")
                        << ", and '" << d.get_user_name() << "' is an auxiliary declaration "
                        << "introduced by the equation compiler (possible solution: "
                        << "use tactic 'clear' to remove '" << d.get_user_name() << "' "
                        << "from the local context)";
                    throw exception(out);
                }
                to_revert.push_back(d.mk_ref());
            }
        });
    if (must_sort) {
        std::sort(to_revert.begin(), to_revert.end(), [&](expr const & l1, expr const & l2) {
                return ctx.get_local_decl(l1).get_idx() < ctx.get_local_decl(l2).get_idx();
            });
    }
    local_context new_ctx = ctx.remove(to_revert);
    return mk_pair(new_ctx, mk_pi(ctx, to_revert, type));
}

expr type_context_old::revert_core(buffer<expr> & to_revert, expr const & mvar, bool preserve_to_revert_order) {
    lean_assert(is_metavar_decl_ref(mvar));
    metavar_decl const & d = m_mctx.get_metavar_decl(mvar);
    pair<local_context, expr> p = revert_core(to_revert, d.get_context(), d.get_type(), preserve_to_revert_order);
    /* Remark: we use copy_tag to make sure any position information
       associated wtih mvar is inherited by the new meta-variable. */
    return mk_metavar_decl(p.first, p.second);
}

expr type_context_old::revert(buffer<expr> & to_revert, expr const & mvar, bool preserve_to_revert_order) {
    lean_assert(is_metavar_decl_ref(mvar));
    lean_assert(std::all_of(to_revert.begin(), to_revert.end(), [&](expr const & l) {
                return static_cast<bool>(m_mctx.find_metavar_decl(mvar)->get_context().find_local_decl(l)); }));
    local_context lctx = m_mctx.get_metavar_decl(mvar).get_context();
    expr new_mvar = revert_core(to_revert, mvar, preserve_to_revert_order);
    expr r = new_mvar;
    for (expr const & a : to_revert) {
        if (!lctx.get_local_decl(a).get_value()) {
            // 'a' is not a let-decl
            r = mk_app(r, a);
        }
    }
    m_mctx.assign(mvar, r);
    return r;
}

/* For every metavariable `?m` occurring at `e`, revert all locals in `?m` that are in `locals` (or depend on them) and obtain `?m1`.
   `?m` is replaced with `?m1 x_1 ... x_n` where `x_1 ... x_n` are the reverted locals. */
expr type_context_old::elim_mvar_deps(expr const & e, unsigned num, expr const * locals) {
    if (num == 0)
        return e;
    expr new_e = instantiate_mvars(e);
    if (!has_expr_metavar(new_e))
        return new_e;
    lean_trace(name({"type_context", "mvar_deps"}), tout() << "elim_mvar_deps:\n" << new_e << "\n";);
    return replace(new_e, [&](expr const & m, unsigned) {
            if (!has_expr_metavar(m)) {
                return some_expr(m);
            } else if (is_metavar_decl_ref(m)) {
                if (optional<expr> const & v = m_mctx.get_assignment(m)) {
                    /* We don't need to visit v, since this assignment
                       was created by this procedure. */
                    return v;
                } else {
                    metavar_decl const & d     = m_mctx.get_metavar_decl(m);
                    local_context const & lctx = d.get_context();
                    buffer<expr> to_revert;
                    for (unsigned i = 0; i < num; i++) {
                        if (optional<local_decl> decl = lctx.find_local_decl(locals[i])) {
                            to_revert.push_back(locals[i]);
                        }
                    }
                    if (to_revert.empty())
                        return some_expr(m);
                    bool preserve_to_revert_order = false;
                    expr new_m = revert(to_revert, m, preserve_to_revert_order);
                    lean_trace(name({"type_context", "mvar_deps"}), tout() << m << " ==> " << new_m << "\n";);
                    return some_expr(new_m);
                }
            }
            return none_expr();
        });
}

expr type_context_old::mk_binding(bool is_pi, local_context const & lctx, unsigned num_locals, expr const * locals, expr const & e) {
    buffer<local_decl>     decls;
    buffer<expr>           types;
    buffer<optional<expr>> values;
    for (unsigned i = 0; i < num_locals; i++) {
        local_decl decl = lctx.get_local_decl(locals[i]);
        decls.push_back(decl);
        types.push_back(abstract(elim_mvar_deps(decl.get_type(), i, locals), i, locals));
        if (auto v = decl.get_value())
            values.push_back(some_expr(abstract(elim_mvar_deps(*v, i, locals), i, locals)));
        else
            values.push_back(none_expr());
    }
    expr new_e = abstract(elim_mvar_deps(e, num_locals, locals), num_locals, locals);
    lean_assert(types.size() == values.size());
    unsigned i = types.size();
    while (i > 0) {
        --i;
        if (values[i]) {
            new_e = mk_let(decls[i].get_user_name(), types[i], *values[i], new_e);
        } else if (is_pi) {
            new_e = ::lean::mk_pi(decls[i].get_user_name(), types[i], new_e, decls[i].get_info());
        } else {
            new_e = ::lean::mk_lambda(decls[i].get_user_name(), types[i], new_e, decls[i].get_info());
        }
    }
    return new_e;
}

expr type_context_old::mk_lambda(local_context const & lctx, buffer<expr> const & locals, expr const & e) {
    return mk_binding(false, lctx, locals.size(), locals.data(), e);
}

expr type_context_old::mk_pi(local_context const & lctx, buffer<expr> const & locals, expr const & e) {
    return mk_binding(true, lctx, locals.size(), locals.data(), e);
}

expr type_context_old::mk_lambda(local_context const & lctx, expr const & local, expr const & e) {
    return mk_binding(false, lctx, 1, &local, e);
}

expr type_context_old::mk_pi(local_context const & lctx, expr const & local, expr const & e) {
    return mk_binding(true, lctx, 1, &local, e);
}

expr type_context_old::mk_lambda(local_context const & lctx, std::initializer_list<expr> const & locals, expr const & e) {
    return mk_binding(false, lctx, locals.size(), locals.begin(), e);
}

expr type_context_old::mk_pi(local_context const & lctx, std::initializer_list<expr> const & locals, expr const & e) {
    return mk_binding(true, lctx, locals.size(), locals.begin(), e);
}

expr type_context_old::mk_lambda(buffer<expr> const & locals, expr const & e) {
    return mk_lambda(m_lctx, locals, e);
}

expr type_context_old::mk_pi(buffer<expr> const & locals, expr const & e) {
    return mk_pi(m_lctx, locals, e);
}

expr type_context_old::mk_lambda(expr const & local, expr const & e) {
    return mk_lambda(m_lctx, local, e);
}

expr type_context_old::mk_pi(expr const & local, expr const & e) {
    return mk_pi(m_lctx, local, e);
}

expr type_context_old::mk_lambda(std::initializer_list<expr> const & locals, expr const & e) {
    return mk_lambda(m_lctx, locals, e);
}

expr type_context_old::mk_pi(std::initializer_list<expr> const & locals, expr const & e) {
    return mk_pi(m_lctx, locals, e);
}

/* ---------------------
   Normalization
   -------------------- */

optional<constant_info> type_context_old::get_decl(transparency_mode m, name const & n) {
    if (m_transparency_pred) {
        if ((*m_transparency_pred)(n)) {
            return env().find(n);
        } else {
            return none_constant_info();
        }
    } else {
        return m_cache->get_decl(*this, m, n);
    }
}

optional<constant_info> type_context_old::get_decl(name const & n) {
    return get_decl(m_transparency_mode, n);
}

name mk_smart_unfolding_name_for(name const & n) {
    return name(n, "_sunfold");
}

static bool is_smart_unfolding_target(environment const & env, name const & fn_name) {
    if (is_aux_match(fn_name)) {
        // We don't use `_match` auxiliary definitions anymore.
        // Remark: this file will be deleted.
        lean_unreachable();
    }
    bool r = static_cast<bool>(env.find(mk_smart_unfolding_name_for(fn_name)));
    return r;
}

static expr ext_unfold_fn(environment const & env, expr const & fn) {
    lean_assert(is_constant(fn));
    if (optional<constant_info> meta_info = env.find(mk_smart_unfolding_name_for(const_name(fn)))) {
        return instantiate_value_lparams(*meta_info, const_levels(fn));
    } else if (optional<constant_info> info = env.find(const_name(fn))) {
        return instantiate_value_lparams(*info, const_levels(fn));
    } else {
        lean_unreachable();
    }
}

/* Unfold \c e if it is a constant */
optional<expr> type_context_old::unfold_definition_core(expr const & e) {
    if (is_constant(e)) {
        if (auto d = get_decl(const_name(e))) {
            if (length(const_levels(e)) == d->get_num_lparams())
                return some_expr(instantiate_value_lparams(*d, const_levels(e)));
        }
    }
    return none_expr();
}

/* (@id_rhs T f a_1 ... a_n) ==> (f a_1 ... a_n) */
static optional<expr> extract_id_rhs(expr const & e) {
    if (is_app_of(e, get_id_rhs_name())) {
        /* found id_rhs */
        buffer<expr> e_args;
        get_app_args(e, e_args);
        if (e_args.size() < 2) return none_expr();
        expr r = mk_app(e_args[1], e_args.size() - 2, e_args.begin() + 2);
        return some_expr(r);
    } else {
        return none_expr();
    }
}

/* Unfold head(e) if it is a constant */
optional<expr> type_context_old::unfold_definition(expr const & e) {
    flet<unsigned> inc_depth(m_unfold_depth, m_unfold_depth+1);
    if (is_app(e)) {
        expr f0 = get_app_fn(e);
        if (!is_constant(f0))
            return none_expr();
        optional<constant_info> info = get_decl(const_name(f0));
        if (!info || length(const_levels(f0)) != info->get_num_lparams())
            return none_expr();
        if (m_smart_unfolding && is_smart_unfolding_target(env(), const_name(f0))) {
            expr it = e;
            while (true) {
                lean_trace(name({"type_context", "smart_unfolding"}), tout() << "[" << m_unfold_depth << "] " << it << "\n";);
                expr const & it_fn = get_app_fn(it);
                expr new_fn        = ext_unfold_fn(env(), it_fn);
                buffer<expr> args;
                get_app_rev_args(it, args);
                expr new_it        = apply_beta(new_fn, args.size(), args.data());
                lean_trace(name({"type_context", "smart_unfolding"}), tout() << "before whnf_core [" << m_unfold_depth << "] " << new_it << "\n";);
                /* whnf_core + unstuck loop */
                while (true) {
                    new_it             = whnf_core(new_it, true, true);
                    lean_trace(name({"type_context", "smart_unfolding"}), tout() << "after whnf_core [" << m_unfold_depth << "] " << new_it << "\n";);
                    if (is_stuck(new_it)) {
                        expr new_new_it = try_to_unstuck_using_complete_instance(new_it);
                        if (!is_eqp(new_new_it, new_it)) {
                            new_it = new_new_it;
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                if (optional<expr> r = extract_id_rhs(new_it)) {
                    lean_trace(name({"type_context", "smart_unfolding"}), tout() << "result [" << m_unfold_depth << "]: " << *r << "\n";);
                    return r;
                } else {
                    expr const & new_it_fn = get_app_fn(new_it);
                    if (!is_constant(new_it_fn)) {
                        lean_trace(name({"type_context", "smart_unfolding"}), tout() << "fail 1 [" << m_unfold_depth << "]\n";);
                        return none_expr();
                    }
                    optional<constant_info> new_it_info = env().find(const_name(new_it_fn));
                    if (!new_it_info || !new_it_info->has_value() || length(const_levels(new_it_fn)) != new_it_info->get_num_lparams()) {
                        lean_trace(name({"type_context", "smart_unfolding"}), tout() << "fail 2 [" << m_unfold_depth << "] " << whnf_core(new_it, true, true) << "\n";);
                        return none_expr();
                    }
                    it = new_it;
                }
            }
        } else {
            /* TODO(Leo): should we block unfolding of constants defined using well founded recursion? */
            lean_trace(name({"type_context", "smart_unfolding"}), tout() << "using simple unfolding [" << m_unfold_depth << "]\n" << e << "\n";);
            expr f = instantiate_value_lparams(*info, const_levels(f0));
            buffer<expr> args;
            get_app_rev_args(e, args);
            expr r = apply_beta(f, args.size(), args.data());
            if (optional<expr> new_r = extract_id_rhs(r)) {
                return new_r;
            } else {
                return some_expr(r);
            }
        }
    } else if (auto r = unfold_definition_core(e)) {
        if (optional<expr> new_r = extract_id_rhs(*r))
            return new_r;
        else
            return r;
    } else {
        return none_expr();
    }
}

optional<projection_info> type_context_old::is_projection(expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return optional<projection_info>();
    optional<projection_info> info = m_cache->get_proj_info(*this, const_name(f));
    if (!info)
        return info;
    if (get_app_num_args(e) <= info->get_nparams())
        return optional<projection_info>();
    return info;
}

optional<expr> type_context_old::reduce_projection_core(optional<projection_info> const & info, expr const & e) {
    buffer<expr> args;
    get_app_args(e, args);
    lean_assert(args.size() > info->get_nparams());
    unsigned mkidx  = info->get_nparams();
    expr const & mk = args[mkidx];
    expr new_mk     = whnf(mk);
    expr const & new_mk_fn = get_app_fn(new_mk);
    if (!is_constant(new_mk_fn) || const_name(new_mk_fn) != info->get_constructor())
        return none_expr();
    buffer<expr> mk_args;
    get_app_args(new_mk, mk_args);
    unsigned i = info->get_nparams() + info->get_i();
    if (i >= mk_args.size())
        none_expr();
    expr r = mk_args[i];
    r = mk_app(r, args.size() - mkidx - 1, args.data() + mkidx + 1);
    return some_expr(r);
}

optional<expr> type_context_old::reduce_projection(expr const & e) {
    optional<projection_info> info = is_projection(e);
    if (!info)
        return none_expr();
    return reduce_projection_core(info, e);
}

optional<expr> type_context_old::reduce_proj(expr const & e) {
    if (!proj_idx(e).is_small())
        return none_expr();
    unsigned idx = proj_idx(e).get_small_value();
    expr c = whnf(proj_expr(e));
    buffer<expr> args;
    expr const & mk = get_app_args(c, args);
    if (!is_constant(mk))
        return none_expr();
    constant_info mk_info = env().get(const_name(mk));
    if (!mk_info.is_constructor())
        return none_expr();
    unsigned nparams = mk_info.to_constructor_val().get_nparams();
    if (nparams + idx < args.size())
        return some_expr(args[nparams + idx]);
    else
        return none_expr();
}

optional<expr> type_context_old::reduce_aux_recursor(expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    if (m_cache->get_aux_recursor(*this, const_name(f))) {
        flet<bool> no_smart_unfolding(m_smart_unfolding, false);
        optional<expr> r = unfold_definition(e);
        /* Remark:

           (brec_on ...) unfolds to a term of the form (pprod.fst (rec ...))

           The method `whnf_core` has a flag that disables projection-reduction.
           This flag is necessary, for example, when solving constraints such as `(pprod.fst ?m) =?= (pprod.fst (1, 2))`

           When projection-reduction is disabled, we observed a negative performance impact on
           constraints containing `brec_on` that come from the equation compiler.
           For example, consider the following definition

           ```
           def nasty_size : list nat → nat
           | []      := 1000000
           | (a::as) := nasty_size as + 1000000
           ```

           We will get a constraint of the form
           ```
           (list.brec_on [] ...) =?= bit0 ...
           ```
           The is_def_eq method reduces this constraint using whnf_core with projection-reduction disabled. So,
           we obtain
           ```
           pprod.fst ... =?= bit0 ...
           ```
           This constraint is then handled by is_def_eq_delta, which decides to unfold `bit0` which is a poor decision.
           The key problem here is that we morally did not reduce `brec_on`.
           Thus, we fix the issue by using reduce_projection if the auxiliary recursor is a brec_on.
           This fix is a little bit hackish and non modular because `brec_on` auxiliary recursors are defined in
           a completely different module, and type_context should not be aware of them.
        */
        if (r && const_name(f).get_string() == g_brec_on) {
            if (auto r2 = reduce_projection(*r))
                return r2;
        }
        return r;
    } else {
        return none_expr();
    }
}

bool type_context_old::use_zeta() const {
    return m_zeta;
}

optional<expr> type_context_old::reduce_recursor(expr const & e) {
    if (env().is_quot_initialized()) {
        if (optional<expr> r = quot_reduce_rec(e, [&](expr const & e) { return whnf(e); })) {
            return r;
        }
    }
    if (optional<expr> r = inductive_reduce_rec(env(), e,
                                                [&](expr const & e) { return whnf(e); },
                                                [&](expr const & e) { return infer(e); },
                                                [&](expr const & e1, expr const & e2) { return is_def_eq(e1, e2); })) {
        return r;
    }
    return none_expr();
}

/*
  Apply beta-reduction, zeta-reduction (i.e., unfold let local-decls), iota-reduction,
  expand let-expressions, expand assigned meta-variables.

  This method does *not* apply delta-reduction at the head.
  Reason: we want to perform these reductions lazily at is_def_eq.

  Remark: this method delta-reduce (transparent) aux-recursors (e.g., cases_on, rec_on) IF
  `aux_rec_reduce == true`

  Remark: if proj_reduce is false, then projection reduction is not performed.
*/
expr type_context_old::whnf_core(expr const & e0, bool proj_reduce, bool aux_rec_reduce) {
    expr e = e0;
    while (true) { switch (e.kind()) {
    case expr_kind::BVar:  case expr_kind::Sort:
    case expr_kind::Pi:    case expr_kind::Lambda:
    case expr_kind::Const: case expr_kind::Lit:
        /* Remark: we do not unfold Constants eagerly in this method */
        return e;
    case expr_kind::FVar:
        if (use_zeta() && is_local_decl_ref(e)) {
            if (auto d = m_lctx.find_local_decl(e)) {
                if (auto v = d->get_value()) {
                    /* zeta-reduction */
                    e = *v;
                    continue;
                }
            }
        }
        return e;
    case expr_kind::MVar:
        if (is_regular_mvar(e)) {
            if (m_mctx.is_assigned(e)) {
                m_used_assignment = true;
                e = m_mctx.instantiate_mvars(e);
                continue;
            }
        } else if (m_tmp_data && is_idx_metavar(e)) {
            lean_assert(in_tmp_mode());
            unsigned idx = to_meta_idx(e);
            if (idx < m_tmp_data->m_eassignment.size()) {
                if (auto v = m_tmp_data->m_eassignment[idx]) {
                    m_used_assignment = true;
                    e = *v;
                    continue;
                }
            }
        }
        return e;
    case expr_kind::Let:
        check_system("whnf");
        if (use_zeta()) {
            e = ::lean::instantiate(let_body(e), let_value(e));
            continue;
        } else {
            return e;
        }
    case expr_kind::App: {
        check_system("whnf");
        buffer<expr> args;
        expr f0 = get_app_rev_args(e, args);
        expr f  = whnf_core(f0, proj_reduce, aux_rec_reduce);
        if (is_lambda(f)) {
            /* beta-reduction */
            unsigned m = 1;
            unsigned num_args = args.size();
            while (is_lambda(binding_body(f)) && m < num_args) {
                f = binding_body(f);
                m++;
            }
            lean_assert(m <= num_args);
            e = mk_rev_app(::lean::instantiate(binding_body(f), m, args.data() + (num_args - m)),
                    num_args - m, args.data());
            continue;
        } else if (f == f0) {
            if (optional<expr> r = reduce_recursor(e)) {
                e = *r;
                continue;
            }

            if (proj_reduce) {
                if (auto r = reduce_projection(e)) {
                    e = *r;
                    continue;
                }
            }

            if (aux_rec_reduce) {
                if (optional<expr> r = reduce_aux_recursor(e)) {
                    e = *r;
                    continue;
                }
            }

            return e;
        } else {
            e = mk_rev_app(f, args.size(), args.data());
            continue;
        }
    }
    case expr_kind::Proj:
        if (auto r = reduce_proj(e)) {
            e = *r;
            continue;
        }
        return e;
    case expr_kind::MData:
        e = mdata_expr(e);
        continue;
    }}
}

expr type_context_old::whnf(expr const & e) {
    switch (e.kind()) {
    case expr_kind::BVar:     case expr_kind::Sort:
    case expr_kind::Pi:       case expr_kind::Lambda:
        return e;
    default:
        break;
    }
    if (auto r = m_cache->get_whnf(m_transparency_mode, e))
        return *r;
    reset_used_assignment reset(*this);
    unsigned postponed_sz = m_postponed.size();
    expr t = e;
    while (true) {
        expr t1 = whnf_core(t, true, true);
        if (auto next_t = unfold_definition(t1)) {
            t = *next_t;
        } else {
            if ((!in_tmp_mode() || !has_expr_metavar(t1)) && m_smart_unfolding &&
                !m_used_assignment && !is_stuck(t1) &&
                postponed_sz == m_postponed.size() && !m_transparency_pred) {
                m_cache->set_whnf(m_transparency_mode, e, t1);
            }
            return t1;
        }
    }
}

expr type_context_old::whnf_head_pred(expr const & e, std::function<bool(expr const &)> const & pred) { // NOLINT
    expr t = e;
    while (true) {
        /* We disable auxiliary recursor reduction at `whnf_core` to make sure `pred` can disable it. */
        expr t1 = whnf_core(t, true, false);
        if (!pred(t1)) {
            return t1;
        } else if (optional<expr> next_t = reduce_aux_recursor(t1)) {
            t = *next_t;
        } else if (optional<expr> next_t = unfold_definition(t1)) {
            t = *next_t;
        } else {
            return t1;
        }
    }
}

expr type_context_old::whnf_transparency_pred(expr const & e, std::function<bool(name const &)> const & pred) { // NOLINT
    flet<std::function<bool(name const &)> const *>set_trans_pred(m_transparency_pred, &pred); // NOLINT
    return whnf(e);
}

expr type_context_old::relaxed_whnf(expr const & e) {
    relaxed_scope scope(*this);
    return whnf(e);
}

optional<expr> type_context_old::is_stuck_projection(expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f)) return none_expr(); // it is not projection app
    optional<projection_info> info = m_cache->get_proj_info(*this, const_name(f));
    if (!info) return none_expr(); // it is not projection app
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() <= info->get_nparams()) return none_expr(); // partially applied projection
    unsigned mkidx  = info->get_nparams();
    expr mk         = args[mkidx];
    return is_stuck(mk);
}

optional<expr> type_context_old::is_stuck(expr const & e) {
    if (is_metavar_app(e)) {
        return some_expr(e);
    } else if (auto r = is_stuck_projection(e)) {
        return r;
    } else if (is_annotation(e)) {
        return is_stuck(get_annotation_arg(e));
    } else {
        if (env().is_quot_initialized()) {
            if (optional<expr> r = quot_is_stuck(e,
                                                 [&](expr const & e) { return whnf(e); },
                                                 [&](expr const & e) { return is_stuck(e); })) {
                return r;
            }
        }
        if (optional<expr> r = inductive_is_stuck(env(), e,
                                                  [&](expr const & e) { return whnf(e); },
                                                  [&](expr const & e) { return is_stuck(e); })) {
            return r;
        }
        return none_expr();
    }
}

expr type_context_old::try_to_pi(expr const & e) {
    expr new_e = whnf(e);
    if (is_pi(new_e))
        return new_e;
    else
        return e;
}

expr type_context_old::relaxed_try_to_pi(expr const & e) {
    relaxed_scope scope(*this);
    return try_to_pi(e);
}

/* ---------------
   Type inference
   --------------- */

expr type_context_old::infer(expr const & e) {
    relaxed_scope scope(*this);
    return infer_core(e);
}

static void throw_invalid_projection(expr const &) {
    throw exception("invalid projection");
}

expr type_context_old::infer_proj(expr const & e) {
    if (!proj_idx(e).is_small())
        throw_invalid_projection(e);
    expr type    = whnf(infer_core(proj_expr(e)));
    unsigned idx = proj_idx(e).get_small_value();
    buffer<expr> args;
    expr const & I = get_app_args(type, args);
    if (!is_constant(I))
        throw_invalid_projection(e);
    constant_info I_info = m_env.get(const_name(I));
    if (!I_info.is_inductive())
        throw_invalid_projection(e);
    inductive_val I_val = I_info.to_inductive_val();
    if (length(I_val.get_cnstrs()) != 1 || args.size() != I_val.get_nparams())
        throw_invalid_projection(e);

    constant_info c_info = m_env.get(head(I_val.get_cnstrs()));
    expr r = instantiate_type_lparams(c_info, const_levels(I));
    for (expr const & arg : args) {
        r = whnf(r);
        if (!is_pi(r)) throw_invalid_projection(e);
        r = instantiate(binding_body(r), arg);
    }
    for (unsigned i = 0; i < idx; i++) {
        r = whnf(r);
        if (!is_pi(r)) throw_invalid_projection(e);
        if (has_loose_bvars(binding_body(r)))
            r = instantiate(binding_body(r), mk_proj(const_name(I), i, proj_expr(e)));
        else
            r = binding_body(r);
    }
    r = whnf(r);
    if (!is_pi(r)) throw_invalid_projection(e);
    return binding_domain(r);
}

expr type_context_old::infer_core(expr const & e) {
    if (auto r = m_cache->get_infer(e))
        return *r;
    unsigned postponed_sz = m_postponed.size();
    reset_used_assignment reset(*this);

    expr r;
    switch (e.kind()) {
    case expr_kind::FVar:
        r = infer_local(e);
        break;
    case expr_kind::Lit:
        r = lit_type(e);
        break;
    case expr_kind::MVar:
        r = infer_metavar(e);
        break;
    case expr_kind::MData:
        r = infer_core(mdata_expr(e));
        break;
    case expr_kind::Proj:
        r = infer_proj(e);
        break;
    case expr_kind::BVar:
        throw exception("failed to infer type, unexpected bound variable occurrence");
    case expr_kind::Sort:
        r = mk_sort(mk_succ(sort_level(e)));
        break;
    case expr_kind::Const:
        r = infer_constant(e);
        break;
    case expr_kind::Lambda:
        r = infer_lambda(e);
        break;
    case expr_kind::Pi:
        r = infer_pi(e);
        break;
    case expr_kind::App:
        r = infer_app(e);
        break;
    case expr_kind::Let:
        r = infer_let(e);
        break;
    }

    if ((!in_tmp_mode() || (!has_expr_metavar(e) && !has_expr_metavar(r))) &&
        !m_used_assignment && postponed_sz == m_postponed.size())
        m_cache->set_infer(e, r);

    return r;
}

expr type_context_old::infer_local(expr const & e) {
    lean_assert(is_local(e));
    if (is_local_decl_ref(e)) {
        optional<local_decl> d = m_lctx.find_local_decl(e);
        if (!d) {
            throw generic_exception(e, [=](formatter const & fmt) {
                    return format("infer type failed, unknown variable") + pp_indent_expr(fmt, e);
                });
        }
        lean_assert(d);
        return d->get_type();
    } else {
        /* Remark: depending on how we re-organize the parser, we may be able
           to remove this branch. */
        return local_type(e);
    }
}

static void throw_unknown_metavar(expr const & e) {
    throw generic_exception(e, [=](formatter const & fmt) {
            return format("infer type failed, unknown metavariable") + pp_indent_expr(fmt, e);
        });
}

expr type_context_old::infer_metavar(expr const & e) {
    if (is_metavar_decl_ref(e)) {
        auto d = m_mctx.find_metavar_decl(e);
        if (!d) throw_unknown_metavar(e);
        return d->get_type();
    } else {
        /* tmp metavariables should only occur in tmp_mode.
           The following assertion was commented because the pretty printer may violate it. */
        // lean_assert(!is_idx_metavar(e) || in_tmp_mode());
        return mvar_type(e);
    }
}

expr type_context_old::infer_constant(expr const & e) {
    constant_info info = env().get(const_name(e));
    auto const & ps = info.get_lparams();
    auto const & ls = const_levels(e);
    if (length(ps) != length(ls)) {
        throw generic_exception(e, [=](formatter const & fmt) {
                auto new_fmt = fmt.update_option_if_undef(get_pp_universes_name(), true);
                return format("infer type failed, incorrect number of universe levels") + pp_indent_expr(new_fmt, e);
            });
    }
    return instantiate_type_lparams(info, ls);
}

expr type_context_old::infer_lambda(expr e) {
    buffer<expr> es, ds;
    tmp_locals ls(*this);
    while (is_lambda(e)) {
        es.push_back(e);
        ds.push_back(binding_domain(e));
        expr d = instantiate_rev(binding_domain(e), ls.size(), ls.data());
        expr l = ls.push_local(binding_name(e), d, binding_info(e));
        e = binding_body(e);
    }
    check_system("infer_type");
    expr t = infer_core(instantiate_rev(e, ls.size(), ls.data()));
    expr r = abstract(t, ls.size(), ls.data());
    unsigned i = es.size();
    while (i > 0) {
        --i;
        r = ::lean::mk_pi(binding_name(es[i]), ds[i], r, binding_info(es[i]));
    }
    return r;
}

optional<level> type_context_old::get_level_core(expr const & A) {
    lean_assert(m_transparency_mode == transparency_mode::All);
    expr A_type = whnf(infer_core(A));
    while (true) {
        if (is_sort(A_type)) {
            return some_level(sort_level(A_type));
        } else if (is_mvar(A_type)) {
            if (auto v = get_assignment(A_type)) {
                A_type = *v;
            } else if (is_regular_mvar(A_type)) {
                /* It is safe to assign A_type if it is a regular metavariable
                   and we are not in tmp mode.
                   We are not restricting A_type interpretations because of unification
                   constraints, but by explicit typing constraints.
                   Remark: This assignment can be undone during backtracking. */
                level r = m_mctx.mk_univ_metavar_decl();
                assign(A_type, mk_sort(r));
                return some_level(r);
            } else if (is_tmp_mvar(A_type) && in_tmp_mode()) {
                /* The condition `in_tmp_mode()` may seem unnecessary, but we
                   include it since `type_context_old` often has to process
                   ill-formed expressions produced by error recovery. */
                level r = mk_tmp_univ_mvar();
                assign(A_type, mk_sort(r));
                return some_level(r);
            } else {
                return none_level();
            }
        } else {
            return none_level();
        }
    }
}

level type_context_old::get_level(expr const & A) {
    if (auto r = get_level_core(A)) {
        return *r;
    } else {
        throw generic_exception(A, [=](formatter const & fmt) {
                return format("infer type failed, sort expected") + pp_indent_expr(fmt, A);
            });
    }
}

expr type_context_old::infer_pi(expr e) {
    tmp_locals ls(*this);
    buffer<level> us;
    while (is_pi(e)) {
        expr d  = instantiate_rev(binding_domain(e), ls.size(), ls.data());
        us.push_back(get_level(d));
        expr l  = ls.push_local(binding_name(e), d, binding_info(e));
        e = binding_body(e);
    }
    e = instantiate_rev(e, ls.size(), ls.data());
    level r = get_level(e);
    unsigned i = ls.size();
    while (i > 0) {
        --i;
        r = mk_imax(us[i], r);
    }
    return mk_sort(r);
}

expr type_context_old::infer_app(expr const & e) {
    check_system("infer_type");
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    expr f_type    = infer_core(f);
    unsigned j     = 0;
    unsigned nargs = args.size();
    for (unsigned i = 0; i < nargs; i++) {
        if (is_pi(f_type)) {
            f_type = binding_body(f_type);
        } else {
            lean_assert(m_transparency_mode == transparency_mode::All);
            f_type = whnf(instantiate_rev(f_type, i-j, args.data()+j));
            if (!is_pi(f_type)) {
                throw generic_exception(e, [=](formatter const & fmt) {
                        return format("infer type failed, ") + pp_function_expected(fmt, e, f, f_type);
                    });
            }
            f_type = binding_body(f_type);
            j = i;
        }
    }
    return instantiate_rev(f_type, nargs-j, args.data()+j);
}

expr type_context_old::infer_let(expr e) {
    /*
      We may also infer the type of a let-expression by using
      tmp_locals, push_let, and they closing the resulting type with
      let-expressions.
      It is unclear which option is the best / more efficient.
      The following implementation doesn't need the extra step,
      but it relies on the cache to avoid repeated work.
    */
    buffer<expr> vs;
    while (is_let(e)) {
        expr v = instantiate_rev(let_value(e), vs.size(), vs.data());
        vs.push_back(v);
        e = let_body(e);
    }
    check_system("infer_type");
    return infer_core(instantiate_rev(e, vs.size(), vs.data()));
}

expr type_context_old::check(expr const & e) {
    // TODO(Leo): infer doesn't really check anything
    return infer(e);
}

bool type_context_old::is_prop(expr const & e) {
    expr t = whnf(infer(e));
    return t == mk_Prop();
}

bool type_context_old::is_proof(expr const & e) {
    return is_prop(infer(e));
}

/* -------------------------------
   Temporary assignment mode support
   ------------------------------- */
void type_context_old::ensure_num_tmp_mvars(unsigned num_uvars, unsigned num_mvars) {
    lean_assert(in_tmp_mode());
    if (m_tmp_data->m_uassignment.size() < num_uvars)
        m_tmp_data->m_uassignment.resize(num_uvars, none_level());
    if (m_tmp_data->m_eassignment.size() < num_mvars)
        m_tmp_data->m_eassignment.resize(num_mvars, none_expr());
}

optional<level> type_context_old::get_tmp_uvar_assignment(unsigned idx) const {
    lean_assert(in_tmp_mode());
    lean_assert(idx < m_tmp_data->m_uassignment.size());
    return m_tmp_data->m_uassignment[idx];
}

optional<expr> type_context_old::get_tmp_mvar_assignment(unsigned idx) const {
    lean_assert(in_tmp_mode());
    lean_assert(idx < m_tmp_data->m_eassignment.size());
    return m_tmp_data->m_eassignment[idx];
}

optional<level> type_context_old::get_tmp_assignment(level const & l) const {
    lean_assert(is_idx_metauniv(l));
    return get_tmp_uvar_assignment(to_meta_idx(l));
}

optional<expr> type_context_old::get_tmp_assignment(expr const & e) const {
    lean_assert(is_idx_metavar(e));
    return get_tmp_mvar_assignment(to_meta_idx(e));
}

void type_context_old::assign_tmp(level const & u, level const & l) {
    lean_assert(in_tmp_mode());
    lean_assert(is_idx_metauniv(u));
    lean_assert(to_meta_idx(u) < m_tmp_data->m_uassignment.size());
    unsigned idx = to_meta_idx(u);
    if (!m_scopes.empty() && !m_tmp_data->m_uassignment[idx]) {
        m_tmp_data->m_trail.emplace_back(tmp_trail_kind::Level, idx);
    }
    m_tmp_data->m_uassignment[idx] = l;
}

void type_context_old::assign_tmp(expr const & m, expr const & v) {
    lean_assert(in_tmp_mode());
    lean_assert(is_idx_metavar(m));
    lean_assert(to_meta_idx(m) < m_tmp_data->m_eassignment.size());
    unsigned idx = to_meta_idx(m);
    lean_trace(name({"type_context", "tmp_vars"}),
               tout() << "assign ?x_" << idx << " := " << v << "\n";);
    if (!m_scopes.empty() && !m_tmp_data->m_eassignment[idx]) {
        m_tmp_data->m_trail.emplace_back(tmp_trail_kind::Expr, idx);
    }
    m_tmp_data->m_eassignment[to_meta_idx(m)] = v;
}

level type_context_old::mk_tmp_univ_mvar() {
    lean_assert(in_tmp_mode());
    unsigned idx = m_tmp_data->m_uassignment.size();
    m_tmp_data->m_uassignment.push_back(none_level());
    return mk_idx_metauniv(idx);
}

expr type_context_old::mk_tmp_mvar(expr const & type) {
    lean_assert(in_tmp_mode());
    unsigned idx = m_tmp_data->m_eassignment.size();
    m_tmp_data->m_eassignment.push_back(none_expr());
    return mk_idx_metavar(idx, type);
}

void type_context_old::resize_tmp_mvars(unsigned sz) {
    lean_assert(in_tmp_mode());
    m_tmp_data->m_eassignment.resize(sz, optional<expr>());
}

/* -----------------------------------
   Uniform interface to temporary & regular metavariables
   ----------------------------------- */
bool type_context_old::is_mvar(level const & l) const {
    return (in_tmp_mode() && is_idx_metauniv(l)) || is_metavar_decl_ref(l);
}

bool type_context_old::is_mvar(expr const & e) const {
    return (in_tmp_mode() && is_idx_metavar(e)) || is_metavar_decl_ref(e);
}

bool type_context_old::is_mode_mvar(level const & l) const {
    if (in_tmp_mode())
        return is_idx_metauniv(l);
    else
        return is_metavar_decl_ref(l);
}

bool type_context_old::is_mode_mvar(expr const & e) const {
    if (in_tmp_mode())
        return is_idx_metavar(e);
    else
        return is_metavar_decl_ref(e);
}

bool type_context_old::is_assigned(level const & l) const {
    const_cast<type_context_old*>(this)->m_used_assignment = true;
    if (in_tmp_mode() && is_idx_metauniv(l))
        return static_cast<bool>(get_tmp_assignment(l));
    else
        return m_mctx.is_assigned(l);
}

bool type_context_old::is_assigned(expr const & e) const {
    const_cast<type_context_old*>(this)->m_used_assignment = true;
    if (in_tmp_mode() && is_idx_metavar(e))
        return static_cast<bool>(get_tmp_assignment(e));
    else
        return m_mctx.is_assigned(e);
}

optional<level> type_context_old::get_assignment(level const & l) const {
    const_cast<type_context_old*>(this)->m_used_assignment = true;
    if (in_tmp_mode() && is_idx_metauniv(l))
        return get_tmp_assignment(l);
    else
        return m_mctx.get_assignment(l);
}

optional<expr> type_context_old::get_assignment(expr const & e) const {
    const_cast<type_context_old*>(this)->m_used_assignment = true;
    if (in_tmp_mode() && is_idx_metavar(e))
        return get_tmp_assignment(e);
    else
        return m_mctx.get_assignment(e);
}

void type_context_old::assign(level const & u, level const & l) {
    m_used_assignment = true;
    if (in_tmp_mode() && is_idx_metauniv(u))
        assign_tmp(u, l);
    else
        m_mctx.assign(u, l);
}

void type_context_old::assign(expr const & m, expr const & v) {
    m_used_assignment = true;
    if (in_tmp_mode() && is_idx_metavar(m))
        assign_tmp(m, v);
    else
        m_mctx.assign(m, v);
}

level type_context_old::mk_fresh_univ_metavar() {
    if (in_tmp_mode())
        return mk_tmp_univ_mvar();
    else
        return mk_univ_metavar_decl();
}

level type_context_old::instantiate_mvars(level const & l) {
    return ::lean::instantiate_mvars(*this, l);
}

expr type_context_old::instantiate_mvars(expr const & e) {
    return ::lean::instantiate_mvars(*this, e);
}

/* -----------------------------------
   Backtracking
   ----------------------------------- */

void type_context_old::push_scope() {
    if (in_tmp_mode()) {
        m_scopes.emplace_back(m_mctx, m_tmp_data->m_uassignment.size(), m_tmp_data->m_eassignment.size(), m_tmp_data->m_trail.size());
    } else {
        m_scopes.emplace_back(m_mctx, 0, 0, 0);
    }
}

void type_context_old::pop_scope() {
    lean_assert(!m_scopes.empty());
    scope_data const & s = m_scopes.back();
    m_mctx = s.m_mctx;
    if (in_tmp_mode()) {
        unsigned old_sz = s.m_tmp_trail_sz;
        while (m_tmp_data->m_trail.size() > old_sz) {
            auto const & t = m_tmp_data->m_trail.back();
            if (t.first == tmp_trail_kind::Level) {
                m_tmp_data->m_uassignment[t.second] = none_level();
            } else {
                lean_trace(name({"type_context", "tmp_vars"}),
                           tout() << "unassign ?x_" << t.second << " := " << *(m_tmp_data->m_eassignment[t.second]) << "\n";);
                m_tmp_data->m_eassignment[t.second] = none_expr();
            }
            m_tmp_data->m_trail.pop_back();
        }
        lean_assert(old_sz == m_tmp_data->m_trail.size());
        m_tmp_data->m_uassignment.shrink(s.m_tmp_uassignment_sz);
        m_tmp_data->m_eassignment.shrink(s.m_tmp_eassignment_sz);
    }
    m_scopes.pop_back();
}

void type_context_old::commit_scope() {
    lean_assert(!m_scopes.empty());
    m_scopes.pop_back();
}

/* -----------------------------------
   Unification / definitional equality
   ----------------------------------- */

static bool is_max_like(level const & l) {
    return is_max(l) || is_imax(l);
}

/** \brief Return true iff \c rhs is of the form <tt> max(l_1 ... m ... l_k) </tt>,
    such that l_i's do not contain m.
    If the result is true, then all l_i's are stored in rest. */
static bool generalized_check_meta(level const & m, level const & rhs, bool & found_m, buffer<level> & rest) {
    lean_assert(is_mvar(m));
    if (is_max(rhs)) {
        return
            generalized_check_meta(m, max_lhs(rhs), found_m, rest) &&
            generalized_check_meta(m, max_rhs(rhs), found_m, rest);
    } else if (m == rhs) {
        found_m = true;
        return true;
    } else if (occurs(m, rhs)) {
        return false;
    } else {
        rest.push_back(rhs);
        return true;
    }
}

/* Return true iff rhs is of the form max(lhs, v)

   Remark a constraint of the form ?u =?= max ?u v is solved by
   creating a fresh metavariable ?w and assigning
            ?u := max v ?w
*/
bool type_context_old::solve_u_eq_max_u_v(level const & lhs, level const & rhs) {
    lean_assert(is_mvar(lhs));
    lean_assert(occurs(lhs, rhs));
    buffer<level> rest;
    bool found_lhs = false;
    if (generalized_check_meta(lhs, rhs, found_lhs, rest)) {
        lean_assert(found_lhs);
        // rhs is of the form max(rest, lhs)
        // Solution is lhs := max(rest, ?u) where ?u is fresh metavariable
        level r = mk_fresh_univ_metavar();
        rest.push_back(r);
        unsigned i = rest.size();
        while (i > 0) {
            --i;
            r = mk_max(rest[i], r);
        }
        r = normalize(r);
        assign(lhs, r);
        return true;
    } else {
        return false;
    }
}

lbool type_context_old::is_def_eq_core(level const & l1, level const & l2, bool partial) {
    if (is_equivalent(l1, l2))
        return l_true;

    lean_trace(name({"type_context", "univ_is_def_eq_detail"}),
               tout() << "[" << m_is_def_eq_depth << "]: " << l1 << " =?= " << l2 << "\n";);

    flet<unsigned> inc_depth(m_is_def_eq_depth, m_is_def_eq_depth+1);

    level new_l1 = instantiate_mvars(l1);
    level new_l2 = instantiate_mvars(l2);

    if (l1 != new_l1 || l2 != new_l2)
        return is_def_eq_core(new_l1, new_l2, partial);

    if (m_update_left && is_mode_mvar(l1)) {
        lean_assert(!is_assigned(l1));
        if (!occurs(l1, l2)) {
            assign(l1, l2);
            return l_true;
        } else if (solve_u_eq_max_u_v(l1, l2)) {
            return l_true;
        }
    }

    if (m_update_right && is_mode_mvar(l2)) {
        lean_assert(!is_assigned(l2));
        if (!occurs(l2, l1)) {
            assign(l2, l1);
            return l_true;
        } else if (solve_u_eq_max_u_v(l2, l1)) {
            return l_true;
        }
    }

    if (l1.kind() != l2.kind() && (is_succ(l1) || is_succ(l2))) {
        if (optional<level> pred_l1 = dec_level(l1))
        if (optional<level> pred_l2 = dec_level(l2))
            return is_def_eq_core(*pred_l1, *pred_l2, partial);
    }

    if (partial && (is_max_like(l1) || is_max_like(l2)))
        return l_undef;

    if (l1.kind() != l2.kind())
        return l_false;

    switch (l1.kind()) {
    case level_kind::Max:
        lean_assert(!partial);
        return
            to_lbool(is_def_eq_core(max_lhs(l1), max_lhs(l2), partial) == l_true &&
                     is_def_eq_core(max_rhs(l1), max_rhs(l2), partial) == l_true);
    case level_kind::IMax:
        lean_assert(!partial);
        return
            to_lbool(is_def_eq_core(imax_lhs(l1), imax_lhs(l2), partial) == l_true &&
                     is_def_eq_core(imax_rhs(l1), imax_rhs(l2), partial) == l_true);
    case level_kind::Succ:
        return is_def_eq_core(succ_of(l1), succ_of(l2), partial);
    case level_kind::Param:
    case level_kind::MVar:
        /* This can happen, for example, when we are in tmp_mode, but l1 and l2 are not tmp universe metavariables. */
        return l_false;
    case level_kind::Zero:
        lean_unreachable();
    }
    lean_unreachable();
}

lbool type_context_old::partial_is_def_eq(level const & l1, level const & l2) {
    return is_def_eq_core(l1, l2, true);
}

bool type_context_old::full_is_def_eq(level const & l1, level const & l2) {
    lbool r = is_def_eq_core(l1, l2, false);
    lean_assert(r != l_undef);
    return r == l_true;
}

bool type_context_old::is_def_eq(level const & l1, level const & l2) {
    lbool success = partial_is_def_eq(l1, l2);
    if (success == l_undef) {
        m_postponed.emplace_back(l1, l2);
        lean_trace(name({"type_context", "univ_is_def_eq"}),
                   tout() << l1 << " =?= " << l2 << " ... postponed\n";);
        return true;
    } else {
        lean_trace(name({"type_context", "univ_is_def_eq"}),
                   tout() << l1 << " =?= " << l2 << " ... " << (success == l_true ? "success" : "failed") << "\n";);
        return success == l_true;
    }
}

bool type_context_old::is_def_eq(levels const & ls1, levels const & ls2) {
    if (is_nil(ls1) && is_nil(ls2)) {
        return true;
    } else if (!is_nil(ls1) && !is_nil(ls2)) {
        return
            is_def_eq(head(ls1), head(ls2)) &&
            is_def_eq(tail(ls1), tail(ls2));
    } else {
        return false;
    }
}

bool type_context_old::process_postponed(scope const & s) {
    unsigned sz = s.m_postponed_sz;
    lean_assert(m_postponed.size() >= sz);
    if (m_postponed.size() == sz)
        return true;
    buffer<pair<level, level>> b1, b2;
    b1.append(m_postponed.size() - sz, m_postponed.data() + sz);
    buffer<pair<level, level>> * curr, * next;
    curr = &b1;
    next = &b2;
    while (true) {
        for (auto p : *curr) {
            auto r = partial_is_def_eq(p.first, p.second);
            if (r == l_undef) {
                next->push_back(p);
            } else if (r == l_false) {
                lean_trace(name({"type_context", "univ_is_def_eq_detail"}),
                           tout() << "failed postponed: " << p.first << " =?= " << p.second << "\n";);
                return false;
            } else {
                lean_trace(name({"type_context", "univ_is_def_eq_detail"}),
                           tout() << "solved postponed: " << p.first << " =?= " << p.second << "\n";);
            }
        }
        if (next->empty()) {
            return true; // all constraints have been processed
        } else if (next->size() < curr->size()) {
            // easy constraints have been processed in this iteration
            curr->clear();
            std::swap(next, curr);
            lean_assert(next->empty());
        } else if (m_full_postponed) {
            // use full (and approximate) is_def_eq to process the first constraint
            // in next.
            auto p = (*next)[0];
            if (!full_is_def_eq(p.first, p.second)) {
                lean_trace(name({"type_context", "univ_is_def_eq_detail"}),
                           tout() << "failed (full) postponed: " << p.first << " =?= " << p.second << "\n";);
                return false;
            }
            lean_trace(name({"type_context", "univ_is_def_eq_detail"}),
                       tout() << "solved postponed: " << p.first << " =?= " << p.second << "\n";);
            if (next->size() == 1)
                return true; // the last constraint has been solved.
            curr->clear();
            curr->append(next->size() - 1, next->data() + 1);
            next->clear();
        } else {
            lean_assert(!m_full_postponed);
            /* Skip remaining universe constraints. */
            return true;
        }
    }
}

/** \brief Return some definition \c d iff \c e is a target for delta-reduction,
    and the given definition is the one to be expanded. */
optional<constant_info> type_context_old::is_delta(expr const & e) {
    expr const & f = get_app_fn(e);
    if (is_constant(f)) {
        return get_decl(const_name(f));
    } else {
        return none_constant_info();
    }
}

/* If \c e is a let local-decl, then unfold it, otherwise return e. */
expr type_context_old::try_zeta(expr const & e) {
    if (!is_local_decl_ref(e))
        return e;
    if (auto d = m_lctx.find_local_decl(e)) {
        if (auto v = d->get_value())
            return *v;
    }
    return e;
}

expr type_context_old::expand_let_decls(expr const & e) {
    return replace(e, [&](expr const & e, unsigned) {
            if (is_local_decl_ref(e)) {
                if (auto d = m_lctx.find_local_decl(e)) {
                    if (auto v = d->get_value())
                        return some_expr(*v);
                }
            }
            return none_expr();
        });
}

/*
We declare metavariables with respect to a local context.
We use the notation (`?M@C`) to denote a metavariable `?M` that was defined at local context `C`.
Remark: for temporary metavariables, the variable m_tmp_mvar_lctx stores their context.

The following method process the unification constraint

       ?M@C a_1 ... a_n =?= t

We say the unification constraint is a pattern IFF

    1) `a_1 ... a_n` are pairwise distinct local constants that are ​*not*​ references to let-decls.
    2) `a_1 ... a_n` have ​*not*​ been defined in `C`
    3) `t` only contains local constants in `C` and/or `{a_1, ..., a_n}`
    4) For every metavariable `?M'@C'` occurring in `t`, `C'` is a subset of `C`
    5) `?M` does not occur in `t`

Claim: we don't have to check local declaration definitions. That is,
if `t` contains a reference to `x : A := v`, we don't need to check `v`.
Reason: The reference to `x` is a local constant, and it must be in `C` (by 1 and 3).
If `x` is in `C`, then any metavariable occurring in `v` must have been defined in a strict subset of `C`.
So, condition 4 and 5 are satisfied.

If the conditions above have been satisfied, then the
solution for the unification constrain is

   ?M := fun a_1 ... a_n, t

Now, we consider some workarounds/approximations.

 A1) Suppose `t` contains a reference to `x : A := v` and `x` is not in `C` (failed condition 3)
     (precise) solution: unfold `x` in `t`.

 A2) Suppose some `a_i` is in `C` (failed condition 2)
     (approximated) solution (when fo_unif_approx() predicate returns true) :
     ignore condition and also use

        ?M := fun a_1 ... a_n, t

   Here is an example where this approximation fails:
   Given `C` containing `a : nat`, consider the following two constraints
         ?M@C a =?= a
         ?M@C b =?= a

   If we use the approximation in the first constraint, we get
         ?M := fun x, x
   when we apply this solution to the second one we get a failure.

   IMPORTANT: When applying this approximation we need to make sure the
   abstracted term `fun a_1 ... a_n, t` is type correct. The check
   can only be skipped in the pattern case described above. Consider
   the following example. Given the local context

      (α : Type) (a : α)

   we try to solve

     ?m α =?= @id α a

   If we use the approximation above we obtain:

     ?m := (fun α', @id α' a)

   which is a type incorrect term. `a` has type `α` but it is expected to have
   type `α'`.

   The problem occurs because the right hand side contains a local constant
   `a` that depends on the local constant `α` being abstracted. Note that
   this dependency cannot occur in patterns.

   Here is another example in the same local context

      ?m_1 α =?= id ?m_2

   If we use the approximation above we obtain:

      ?m_1 := (fun α'. id (?m_2' α'))

   where `?m_2'` is a new metavariable, and `?m_2 := ?m_2 α`

   Now, suppose we assign `?m_2'`.

     ?m_2 := fun α, @id α a

   Then, we have

      ?m_1 := (fun α'. id (@id α' a))

   which is again type incorrect.

   We can address the issue on the first example by type checking
   the term after abstraction. This is not a significant performance
   bottleneck because this case doesn't happen very often in practice
   (262 times when compiling corelib on Jan 2018). The second example
   is trickier, but it also occurs less frequently (8 times when compiling
   corelib on Jan 2018, and all occurrences were in init/category when
   we definy monads and auxiliary combinators for them).
   We considered three options for the addressing the issue on the second example:

    a) For each metavariable that may contain a local constant
       that depends on a term being abstracted, we create a fresh metavariable
       with a smaller local context. In the example above, when we perform
       the assignment

         ?m_1 := (fun α'. id (?m_2' α'))

    b) If we find a metavariable with this kind of dependency, we just
       fail and fallback to first-order unification.

    c) If we find a metavariable on the term after abstraction, we just
       fail and fallback to first-order unification.

   The first two options are incomparable, each one of them can solve
   problems where the other fails. The third one is weaker than the second,
   but we didn't find any example in the corelib where the second option
   applies. The first and third options are also incomparable.

   So, we decide to use the third option since it is the simplest to implement,
   and all examples we have identified are in init/category.

 A3) `a_1 ... a_n` are not pairwise distinct (failed condition 1).
   We can approximate again, but the limitations are very similar to the previous one.

 A4) `t` contains a metavariable `?M'@C'` where `C'` is not a subset of `C`.
   (approximated) solution: restrict the context of `?M'`
   If `?M'` is assigned, the workaround is precise, and we just unfold `?M'`.

 A5) If some `a_i` is not a local constant,
     then we use first-order unification (if fo_unif_approx() is true)

       ?M a_1 ... a_i a_{i+1} ... a_{i+k} =?= f b_1 ... b_k

   reduces to

       ?M a_1 ... a_i =?= f
       a_{i+1}        =?= b_1
       ...
       a_{i+k}        =?= b_k


 A6) If (m =?= v) is of the form

        ?M a_1 ... a_n =?= ?M b_1 ... b_k

     then we use first-order unification (if fo_unif_approx() is true)
*/
bool type_context_old::process_assignment(expr const & m, expr const & v) {
    lean_trace(name({"type_context", "is_def_eq_detail"}),
               scope_trace_env scope(env(), *this);
               tout() << "process_assignment " << m << " := " << v << "\n";);
    buffer<expr> args;
    expr const & mvar = get_app_args(m, args);
    lean_assert(is_mvar(mvar));

    optional<metavar_decl> mvar_decl;
    if (!in_tmp_mode()) {
        mvar_decl = m_mctx.get_metavar_decl(mvar);
        if (!mvar_decl) return false;
    }
    buffer<expr> locals;
    bool use_fo     = false; /* if true, we use first-order unification */
    bool add_locals = true;  /* while true we copy args to locals */
    /* in_ctx_locals is a subset of the local constants in `locals`.
       See workaround A2.

       In principle, we only need one store one bit indicating
       whether there is a locals in `locals` that is the local context
       of the metavariable or not. This is all we need to implement
       option c) in the workaround A2.
       We store all occurrences because we may decide to implement options a) or b).
    */
    buffer<expr> in_ctx_locals;
    for (unsigned i = 0; i < args.size(); i++) {
        expr arg = args[i];
        /* try to instantiate */
        if (is_metavar_app(arg))
            arg = instantiate_mvars(arg);
        arg = try_zeta(arg); /* unfold let-constant if needed. */
        args[i] = arg;
        if (!is_local_decl_ref(arg)) {
            /* m is of the form (?M ... t ...) where t is not a local constant. */
            if (fo_unif_approx()) {
                /* workaround A5 */
                use_fo     = true;
                add_locals = false;
            } else {
                return false;
            }
        } else {
            if (std::any_of(locals.begin(), locals.end(),
                            [&](expr const & local) { return local_name(local) == local_name(arg); })) {
                /* m is of the form (?M ... l ... l ...) where l is a local constant. */
                if (quasi_pattern_unif_approx()) {
                    /* workaround A3 */
                    add_locals = false;
                } else if (fo_unif_approx()) {
                    use_fo     = true;
                    add_locals = false;
                } else {
                    return false;
                }
            }
            /* Make sure arg is not in the context of the metavariable mvar
               The code is slightly different for tmp mode because the metavariables
               do not store their local context. */
            if (in_tmp_mode()) {
                if (m_tmp_data->m_mvar_lctx.find_local_decl(arg)) {
                    /* m is of the form (?M@C ... l ...) where l is a local constant in C */
                    if (quasi_pattern_unif_approx()) {
                        if (add_locals)
                            in_ctx_locals.push_back(arg);
                    } else if (fo_unif_approx()) {
                        use_fo     = true;
                        add_locals = false;
                    } else {
                        return false;
                    }
                }
            } else {
                if (mvar_decl->get_context().find_local_decl(arg)) {
                    /* m is of the form (?M@C ... l ...) where l is a local constant in C. */
                    if (quasi_pattern_unif_approx()) {
                        if (add_locals)
                            in_ctx_locals.push_back(arg);
                    } else if (fo_unif_approx()) {
                        use_fo     = true;
                        add_locals = false;
                    } else {
                        return false;
                    }
                }
            }
        }
        if (add_locals)
            locals.push_back(arg);
    }

    expr new_v = instantiate_mvars(v); /* enforce A4 */

    if (fo_unif_approx() && !locals.empty() && get_app_fn(new_v) == mvar) {
        /* A6 */
        use_fo = true;
    }

    if (use_fo)
        return process_assignment_fo_approx(mvar, args, new_v);

    if (optional<expr> new_new_v = check_assignment(locals, in_ctx_locals, mvar, new_v))
        new_v = *new_new_v;
    else if (fo_unif_approx() && !args.empty())
        return process_assignment_fo_approx(mvar, args, new_v);
    else
        return false;

    if (args.empty()) {
        /* easy case */
    } else if (args.size() == locals.size()) {
        new_v = mk_lambda(locals, new_v);
    } else {
        /*
          This case is imprecise since it is not a higher order pattern.
          That the term \c m is of the form (?M t_1 ... t_n) and the t_i's are not pairwise
          distinct local constants.
        */
        tmp_locals new_ls(*this);
        expr mvar_type = infer(mvar);
        for (unsigned i = 0; i < args.size(); i++) {
            mvar_type = relaxed_whnf(mvar_type);
            if (!is_pi(mvar_type))
                return false;
            lean_assert(i <= locals.size());
            if (i == locals.size()) {
                expr new_l = new_ls.push_local(binding_name(mvar_type), binding_domain(mvar_type));
                locals.push_back(new_l);
            }
            lean_assert(i < locals.size());
            mvar_type = ::lean::instantiate(binding_body(mvar_type), locals[i]);
        }
        lean_assert(locals.size() == args.size());
        new_v = mk_lambda(locals, new_v);
    }

    if (!in_ctx_locals.empty()) {
        try {
            /* We need to type check new_v because abstraction using `mk_lambda` may have produced
               a type incorrect term. See discussion at A2.

               Remark: this test should not be a performance bottleneck. On Jan 2018, this check
               had to be performed only 262 times when compiling corelib, and 823 times when
               compiling mathlib. */
            ::lean::check(*this, new_v);
        } catch (exception &) {
            if (args.size() > 0)
                return process_assignment_fo_approx(mvar, args, new_v);
            else
                return false;
        }
    }

    /* check types */
    try {
        expr t1 = infer(mvar);
        expr t2 = infer(new_v);
        /* We use Semireducible to make sure we will not fail an unification step
                   ?m := t
           because we cannot establish that the types of ?m and t are definitionally equal
           due to the current transparency setting.
           This change is consistent with the general approach used in the rest of the code
           base where spurious typing errors due reducibility are avoided by using
           relaxed_is_def_eq. */
        relaxed_scope _(*this, transparency_mode::Semireducible);
        if (!is_def_eq_core(t1, t2)) {
            lean_trace(name({"type_context", "is_def_eq_detail"}),
                       scope_trace_env scope(env(), *this);
                       tout() << "Type mismatch when assigning " << mvar << " := " << new_v << "\n";
                       tout() << ">> " << t1 << " =?= " << t2 << "\n";);
            return false;
        }
    } catch (exception &) {
        return false;
    }

    assign(mvar, new_v);
    lean_trace(name({"type_context", "is_def_eq_detail"}),
               scope_trace_env scope(env(), *this);
               tout() << "assign: " << mvar << " := " << new_v << "\n";);
    return true;
}

/* Basic step for applying first-order unification. See: workaround A5 at \c process_assignment.

   Remark: this method is trying to solve the unification constraint:

      mvar args[0] ... args[args.size()-1] =?= v
*/
bool type_context_old::process_assignment_fo_approx_core(expr const & mvar, buffer<expr> const & args, expr const & v) {
    lean_assert(is_mvar(mvar));
    buffer<expr> v_args;
    expr v_fn = get_app_args(v, v_args);
    if (v_args.empty()) {
        /*
          ?M a_1 ... a_k =?= t,  where t is not an application
        */
        return false;
    }
    expr new_mvar = mvar;
    unsigned i = 0;
    unsigned j = 0;
    if (args.size() > v_args.size()) {
        /*
          ?M a_1 ... a_i a_{i+1} ... a_{i+k} =?= f b_1 ... b_k

          reduces to

          ?M a_1 ... a_i =?= f
          a_{i+1}        =?= b_1
          ...
          a_{i+k}        =?= b_k
        */
        new_mvar = mk_app(mvar, args.size() - v_args.size(), args.data());
        i        = args.size() - v_args.size();
    } else if (args.size() < v_args.size()) {
        /*
          ?M a_1 ... a_k =?= f b_1 ... b_i b_{i+1} ... b_{i+k}

          reduces to

          ?M  =?= f b_1 ... b_i
          a_1 =?= b_{i+1}
          ...
          a_k =?= b_{i+k}
        */
        v_fn = mk_app(v_fn, v_args.size() - args.size(), v_args.data());
        j        = v_args.size() - args.size();
    } else {
        /*
          ?M a_1 ... a_k =?= f b_1 ... b_k

          reduces to
          ?M  =?= f
          a_1 =?= b_1
          ...
          a_k =?= b_k
        */
        lean_assert(v_args.size() == args.size());
    }
    /* We try to unify arguments before we try to unify the functions.
       This heuristic is consistently used in the is_def_eq procedure.
       See is_def_eq_args invocations.
       The motivation is the following: the universe constraints in
       the arguments propagate to the function. */
    for (; j < v_args.size(); i++, j++) {
        lean_assert(i < args.size());
        if (!is_def_eq_core(args[i], v_args[j]))
            return false;
    }
    if (!is_def_eq_core(new_mvar, v_fn))
        return false;
    lean_assert(i == args.size());
    lean_assert(j == v_args.size());
    return true;
}

/* Auxiliary method for applying first-order unification. See: workaround A5 at \c process_assignment.

   Remark: this method is trying to solve the unification constraint:

      mvar args[0] ... args[args.size()-1] =?= v

   It is uses process_assignment_fo_approx_core, if it fails, it tries to unfold `v`.

   We have added support for unfolding here because we want to be able to solve unification problems such as

      ?m unit =?= itactic

   where `itactic` is defined as

      meta def itactic := tactic unit

*/
bool type_context_old::process_assignment_fo_approx(expr const & mvar, buffer<expr> const & args, expr const & v) {
    expr curr_v = v;
    while (true) {
        {
            scope s(*this);
            if (process_assignment_fo_approx_core(mvar, args, curr_v)) {
                s.commit();
                return true;
            }
        }
        if (optional<expr> next_v = unfold_definition(curr_v)) {
            curr_v = *next_v;
        } else {
            return false;
        }
    }
}

struct check_assignment_failed {};

struct check_assignment_fn : public replace_visitor {
    type_context_old &         m_ctx;
    buffer<expr> const &   m_locals;
    buffer<expr> const &   m_in_ctx_locals;
    expr const &           m_mvar;
    optional<metavar_decl> m_mvar_decl;
    expr                   m_value;

    check_assignment_fn(type_context_old & ctx, buffer<expr> const & locals, buffer<expr> const & in_ctx_locals, expr const & mvar):
        m_ctx(ctx), m_locals(locals), m_in_ctx_locals(in_ctx_locals), m_mvar(mvar) {
        if (!m_ctx.in_tmp_mode()) {
            m_mvar_decl = m_ctx.m_mctx.get_metavar_decl(mvar);
            lean_assert(m_mvar_decl);
        }
    }

    expr visit_local(expr const & e) override {
        if (!is_local_decl_ref(e)) return e;

        bool in_ctx;
        if (m_ctx.in_tmp_mode()) {
            in_ctx = static_cast<bool>(m_ctx.m_tmp_data->m_mvar_lctx.find_local_decl(e));
        } else {
            in_ctx = static_cast<bool>(m_mvar_decl->get_context().find_local_decl(e));
        }

        if (!in_ctx) {
            if (auto decl = m_ctx.m_lctx.find_local_decl(e)) {
                if (auto v = decl->get_value()) {
                    /* expand let-decl value */
                    return visit(*v);
                }
            }
            if (std::all_of(m_locals.begin(), m_locals.end(), [&](expr const & a) {
                        return local_name(a) != local_name(e); })) {
                lean_trace(name({"type_context", "is_def_eq_detail"}),
                           scope_trace_env scope(m_ctx.env(), m_ctx);
                           tout() << "failed to assign " << m_mvar << " to\n" << m_value << "\n" <<
                           "value contains local declaration " << e <<
                           " which is not in the scope of the metavariable\n";);
                throw check_assignment_failed();
            }
        }
        return e;
    }

    /** Return true iff ctx1 is a subset of ctx2 */
    bool is_subset_of(local_context const & ctx1, local_context const & ctx2) {
        return !ctx1.find_if([&](local_decl const & d1) { // NOLINT
                name const & n1 = d1.get_name();
                if (ctx2.find_local_decl(n1)) return false;
                return true;
            });
    }

    expr visit_meta(expr const & e) override {
        if (auto v = m_ctx.get_assignment(e)) return visit(*v);

        if (m_mvar == e) {
            /* mvar occurs in m_value */
            lean_trace(name({"type_context", "is_def_eq_detail"}),
                       scope_trace_env scope(m_ctx.env(), m_ctx);
                       tout() << "failed to assign " << m_mvar << " :=\n" << m_value << "\n" <<
                       "value contains the metavariable " << m_mvar << "\n";);
            throw check_assignment_failed();
        }

        if (!m_ctx.is_mode_mvar(e)) {
            if (!m_in_ctx_locals.empty()) {
                /*
                  This code is reachable if we are in tmp mode and `e` is regular metavariable.
                  We just fail, and this is ok because we usually do not use
                  approximate unification/matching in tmp mode.

                  Remark: this code was not reachable when compiling corelib on Jan 2018.
                */
                throw check_assignment_failed();
            }
            return replace_visitor::visit_meta(e);
        }

        if (m_ctx.in_tmp_mode()) {
            if (!m_in_ctx_locals.empty()) {
                /* In tmp mode, we (usually) do not use approximate unification/matching.
                   Moreover, m_in_ctx_locals is empty if we are not approximating

                   Remark: all temporary metavariables share the same local context.
                   Then, if a local in `m_in_ctx_locals` is in the local context of `mvar`,
                   then it will also be in the local context of `e`. */
                throw check_assignment_failed();
            }

            /* Recall that in tmp_mode all metavariables have the same local context.
               So, we don't need to check anything.
               In regular mode, we need to check condition 4

               For every metavariable `?M'@C'` occurring in `t`, `C'` is a subset of `C` */
            return e;
        }

        /* unassigned metavariable in regular mode */

        optional<metavar_decl> e_decl = m_ctx.m_mctx.find_metavar_decl(e);
        if (!e_decl) {
            lean_trace(name({"type_context", "is_def_eq_detail"}),
                       scope_trace_env scope(m_ctx.env(), m_ctx);
                       tout() << "failed to assign " << m_mvar << " :=\n" << m_value << "\n" <<
                       "value contains \"foreign\" metavariable " << e << "\n";);
            throw check_assignment_failed();
        }

        local_context mvar_lctx = m_mvar_decl->get_context();
        local_context e_lctx    = e_decl->get_context();

        if (!m_in_ctx_locals.empty()) {
            /* We are using option c) described at workaround A2. */
            throw check_assignment_failed();
        }

        if (is_subset_of(e_lctx, mvar_lctx))
            return e;

        if (m_ctx.ctx_unif_approx() && mvar_lctx.is_subset_of(e_lctx)) {
            expr e_type = e_decl->get_type();
            if (mvar_lctx.well_formed(e_type)) {
                /* Restrict context of the ?M' */
                /* Remark: we use copy_tag to make sure any position information
                   associated wtih mvar is inherited by the new meta-variable. */
                expr aux_mvar = m_ctx.mk_metavar_decl(mvar_lctx, e_type);
                if (m_ctx.process_assignment(e, aux_mvar)) {
                    return aux_mvar;
                } else {
                    /* Local context restriction failed */
                    throw check_assignment_failed();
                }
            } else {
                /* e_type uses local_decl's that are not in mvar_lctx */
                lean_trace(name({"type_context", "is_def_eq_detail"}),
                           scope_trace_env scope(m_ctx.env(), m_ctx);
                           tout() << "failed to assign " << m_mvar << " :=\n" << m_value << "\n"
                           << "value contains metavariable " << e << ", and its local context "
                           << "is not a subset of the one in the metavariable being assigned. "
                           << "The local context for " << e << " cannot be restricted because "
                           << "its type depends on local constants that are not in the local "
                           << "context for " << m_mvar << "\n";);
                throw check_assignment_failed();
            }
        } else {
            /* The two local contexts are incomparable OR
               approximate mode is not enabled. */
            lean_trace(name({"type_context", "is_def_eq_detail"}),
                       scope_trace_env scope(m_ctx.env(), m_ctx);
                       tout() << "failed to assign " << m_mvar << " :=\n" << m_value << "\n"
                       << "value contains metavariable " << e;
                       if (!m_ctx.ctx_unif_approx()) {
                           tout() << " that was declared in a local context that is not a "
                                  << "subset of the one in the metavariable being assigned, "
                                  << "and local context restriction is disabled\n";
                       } else {
                           tout() << ", but the two local contexts used to declare these metavariables "
                                  << " are incomparable\n";
                       });
            throw check_assignment_failed();
        }
    }

    expr operator()(expr const & v) {
        if (!has_expr_metavar(v) && !has_local(v)) {
            return v;
        } else {
            m_value = v;
            return visit(v);
        }
    }
};

/* Auxiliary method for process_assignment */
optional<expr> type_context_old::check_assignment(buffer<expr> const & locals, buffer<expr> const & in_ctx_locals, expr const & mvar, expr v) {
    try {
        return some_expr(check_assignment_fn(*this, locals, in_ctx_locals, mvar)(v));
    } catch (check_assignment_failed &) {
        return none_expr();
    }
}

bool type_context_old::is_def_eq_binding(expr e1, expr e2) {
    lean_assert(e1.kind() == e2.kind());
    lean_assert(is_binding(e1));
    expr_kind k = e1.kind();
    tmp_locals subst(*this);
    do {
        optional<expr> var_e1_type;
        if (binding_domain(e1) != binding_domain(e2)) {
            var_e1_type = instantiate_rev(binding_domain(e1), subst.size(), subst.data());
            expr var_e2_type = instantiate_rev(binding_domain(e2), subst.size(), subst.data());
            if (!is_def_eq_core(*var_e1_type, var_e2_type))
                return false;
        }
        if (has_loose_bvars(binding_body(e1)) || has_loose_bvars(binding_body(e2))) {
            // local is used inside t or s
            if (!var_e1_type)
                var_e1_type = instantiate_rev(binding_domain(e1), subst.size(), subst.data());
            subst.push_local(binding_name(e1), *var_e1_type);
        } else {
            expr const & dont_care = mk_Prop();
            subst.push_local(binding_name(e1), dont_care);
        }
        e1 = binding_body(e1);
        e2 = binding_body(e2);
    } while (e1.kind() == k && e2.kind() == k);
    return is_def_eq_core(instantiate_rev(e1, subst.size(), subst.data()),
                          instantiate_rev(e2, subst.size(), subst.data()));
}

optional<expr> type_context_old::mk_class_instance_at(local_context const & lctx, expr const & type) {
    context_cacheless tmp_cache(*m_cache, true);
    type_context_old tmp_ctx(env(), m_mctx, lctx, tmp_cache, m_transparency_mode);
    auto r = tmp_ctx.mk_class_instance(type);
    if (r)
        m_mctx = tmp_ctx.mctx();
    return r;
}

/* Temporary hack until we can create type context objects efficiently */
bool type_context_old::is_def_eq_at(local_context const & lctx, expr const & a, expr const & b) {
    context_cacheless tmp_cache(*m_cache, true);
    type_context_old tmp_ctx(env(), m_mctx, lctx, tmp_cache, m_transparency_mode);
    bool r = tmp_ctx.is_def_eq(a, b);
    m_mctx = tmp_ctx.mctx();
    return r;
}

/** \brief Create a nested type class instance of the given type, and assign it to metavariable \c m.
    Return true iff the instance was successfully created.
    \remark This method is used to resolve nested type class resolution problems. */
bool type_context_old::mk_nested_instance(expr const & m, expr const & m_type) {
    lean_assert(is_mvar(m));
    /* IMPORTANT: when mk_nested_instance is invoked we must make sure that
       we use the local context where 'm' was declared. */
    optional<expr> inst;
    if (in_tmp_mode()) {
        /* We don't need to create a temporary type context since all tmp metavars
           share the same local_context */
        inst = mk_class_instance(m_type);
    } else {
        optional<metavar_decl> mdecl = m_mctx.find_metavar_decl(m);
        if (!mdecl) return false;
        inst = mk_class_instance_at(mdecl->get_context(), m_type);
    }
    if (inst) {
        assign(m, *inst);
        return true;
    } else {
        return false;
    }
}

expr type_context_old::complete_instance(expr const & e) {
    if (!has_expr_metavar(e)) return e;

    if (is_app(e)) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        fun_info finfo = get_fun_info(*this, fn, args.size());
        unsigned i = 0;
        bool modified = false;
        for (param_info const & pinfo : finfo.get_params_info()) {
            lean_assert(i < args.size());
            expr arg     = args[i];
            expr new_arg = arg;
            /* Remove annotations */
            while (is_annotation(new_arg)) {
                new_arg = get_annotation_arg(new_arg);
            }
            if (is_mode_mvar(new_arg) && pinfo.is_inst_implicit() && !is_assigned(new_arg)) {
                /* If new_arg is an unassigned metavariable that in an instance-implicit slot,
                   then try to synthesize it */
                expr const & m = new_arg;
                expr m_type    = instantiate_mvars(infer(m));
                if (!has_expr_metavar(m_type) && is_class(m_type)) {
                    if (mk_nested_instance(m, m_type)) {
                        new_arg = instantiate_mvars(new_arg);
                    }
                }
            } else {
                new_arg = complete_instance(new_arg);
            }
            if (new_arg != arg) modified = true;
            args[i] = new_arg;
            i++;
        }
        if (!modified)
            return e;
        else
            return mk_app(fn, args);
    }
    return e;
}

/* If `e` is of the form `(fun x_1 ... x_n, f x_1 ... x_n)` and `f` does not contain `x_1`, ..., `x_n`,
   then return `some(f)`. Otherwise, return `none` */
static optional<expr> is_eta_expanded(expr const & e) {
    if (!is_lambda(e))
        return none_expr();
    expr it    = e;
    unsigned n = 0;
    while (is_lambda(it)) {
        it = binding_body(it);
        n++;
    }
    for (unsigned i = 0; i < n; i++) {
        if (!is_app(it))
            return none_expr();
        expr const & a = app_arg(it);
        if (!is_bvar(a) || bvar_idx(a) != i)
            return none_expr();
        it = app_fn(it);
    }
    if (!has_loose_bvars(it))
        return some_expr(it);
    else
        return none_expr();
}

/*
If `e` is an unassigned metavariable, then return `some(e)`.
If `e` is of the form `fun (x_1 ... x_n), ?m x_1 ... x_n)`, and `?m` is unassigned, then return `some(?m)`.
Otherwise, return `none`.

We use this method to implement `is_def_eq_args`.
*/
optional<expr> type_context_old::is_eta_unassigned_mvar(expr const & e) {
    if (is_mode_mvar(e) && !is_assigned(e))
        return some_expr(e);
    if (auto r = is_eta_expanded(e))
        if (is_mode_mvar(*r) && !is_assigned(*r))
            return r;
    return none_expr();
}

bool type_context_old::is_def_eq_args(expr const & e1, expr const & e2) {
    lean_assert(is_app(e1) && is_app(e2));
    buffer<expr> args1, args2;
    expr const & fn = get_app_args(e1, args1);
    get_app_args(e2, args2);
    if (args1.size() != args2.size())
        return false;
    fun_info finfo = get_fun_info(*this, fn, args1.size());
    unsigned i = 0;
    buffer<pair<unsigned, bool>> postponed;
    /* First pass: unify explicit arguments, *and* easy cases

       Here, we say a case is easy if it is of the form

          ?m =?= t
          or
          t  =?= ?m

          where ?m is unassigned.

       These easy cases are not just an optimization. When
       ?m is a function, by assigning it to t, we make sure
       a unification constraint (in the explicit part)

                ?m t =?= f s

       is not higher-order.

       We also handle the eta-expanded cases:

           fun x_1 ... x_n, ?m x_1 ... x_n =?= t
           t =?= fun x_1 ... x_n, ?m x_1 ... x_n

       This is important because type inference often produces
       eta-expanded terms, and without this extra case, we could
       introduce counter intuitive behavior.
    */
    for (param_info const & pinfo : finfo.get_params_info()) {
        if (pinfo.is_inst_implicit() || pinfo.is_implicit()) {
            if (is_eta_unassigned_mvar(args1[i]) || is_eta_unassigned_mvar(args2[i])) {
                if (!is_def_eq_core(args1[i], args2[i]))
                    return false;
            } else {
                postponed.emplace_back(i, pinfo.is_inst_implicit());
            }
        } else if (!is_def_eq_core(args1[i], args2[i])) {
            return false;
        }
        i++;
    }
    for (; i < args1.size(); i++) {
        if (!is_def_eq_core(args1[i], args2[i]))
            return false;
    }
    /* Second pass: unify implicit arguments.
       In the second pass, we make sure we are unfolding at least semireducible (default setting) definitions. */
    {
        transparency_scope scope(*this, ensure_semireducible_mode(m_transparency_mode));
        for (pair<unsigned, bool> const & p : postponed) {
            unsigned i = p.first;
            if (p.second) {
                args1[i] = complete_instance(args1[i]);
                args2[i] = complete_instance(args2[i]);
            }
            if (!is_def_eq_core(args1[i], args2[i]))
                return false;
        }
    }
    return true;
}

/** \brief Try to solve e1 := (lambda x : A, t) =?= e2 by eta-expanding e2.

    \remark eta-reduction is not a good alternative (even in a system without cumulativity like Lean).
    Example:
         (lambda x : A, f ?M) =?= f
    The lhs cannot be eta-reduced because ?M is a meta-variable. */
bool type_context_old::is_def_eq_eta(expr const & e1, expr const & e2) {
    if (is_lambda(e1) && !is_lambda(e2)) {
        expr e2_type = relaxed_whnf(infer(e2));
        if (is_pi(e2_type)) {
            // e2_type may not be a Pi because it is a stuck term.
            // We are ignoring this case and just failing.
            expr new_e2 = ::lean::mk_lambda(binding_name(e2_type), binding_domain(e2_type),
                                            mk_app(e2, mk_bvar(0)), binding_info(e2_type));
            scope s(*this);
            if (is_def_eq_core(e1, new_e2) && process_postponed(s)) {
                s.commit();
                return true;
            }
        }
    }
    return false;
}

bool type_context_old::is_def_eq_proof_irrel(expr const & e1, expr const & e2) {
    expr e1_type = infer(e1);
    expr e2_type = infer(e2);
    if (is_prop(e1_type) || is_prop(e2_type)) {
        scope s(*this);
        if (is_def_eq_core(e1_type, e2_type) && process_postponed(s)) {
            s.commit();
            return true;
        }
    }
    return false;
}

static bool mvar_has_user_facing_name(expr const &) {
    return false;
}

lbool type_context_old::quick_is_def_eq(expr const & e1, expr const & e2) {
    if (e1 == e2)
        return l_true;
    if (is_cached_equiv(e1, e2))
        return l_true;
    if (is_annotation(e1))
        return to_lbool(is_def_eq_core(get_annotation_arg(e1), e2));
    if (is_annotation(e2))
        return to_lbool(is_def_eq_core(e1, get_annotation_arg(e2)));
    expr const & f1 = get_app_fn(e1);
    expr const & f2 = get_app_fn(e2);

    if (is_mvar(f1) && is_assigned(f1)) {
        return to_lbool(is_def_eq_core(instantiate_mvars(e1), e2));
    } else if (is_mvar(f2) && is_assigned(f2)) {
        return to_lbool(is_def_eq_core(e1, instantiate_mvars(e2)));
    }

    if ((is_metavar_decl_ref(f1) && m_mctx.is_delayed_assigned(f1)) ||
        (is_metavar_decl_ref(f2) && m_mctx.is_delayed_assigned(f2))) {
        return l_false;
    }

    if (is_mode_mvar(f1)) {
        lean_assert(!is_assigned(f1));
        if (optional<expr> ee2 = is_eta_expanded(e2)) {
            if (e1 == *ee2)
                return l_true; /* ?m =?= (fun x_1 ... x_n, ?m x_1 ... x_n) */
        }
        if (m_update_left && !is_mode_mvar(f2)) {
            return to_lbool(process_assignment(e1, e2));
        } else if (m_update_left && in_tmp_mode()) {
            return to_lbool(process_assignment(e1, e2));
        } else if (m_update_left) {
            optional<metavar_decl> m1_decl = m_mctx.find_metavar_decl(f1);
            optional<metavar_decl> m2_decl = m_mctx.find_metavar_decl(f2);
            if (m1_decl && m2_decl) {
                if (m2_decl->get_context().is_subset_of(m1_decl->get_context())) {
                    /* Remark:
                       It is easier to solve the assignment
                          ?m2 := ?m1 a_1 ... a_n
                       than
                          ?m1 a_1 ... a_n := ?m2

                       Reason: the first one is precise. For example,
                       consider the following constraint:

                          ?m1 ?m =?= ?m2
                    */
                    if (!is_app(e1) && is_app(e2)) {
                        /* ?m1 := ?m2 a_1 ... a_n */
                        return to_lbool(process_assignment(e1, e2));
                    } else if (m1_decl->get_context().is_subset_of(m2_decl->get_context())) {
                        lean_assert(is_app(e1) || !is_app(e2));
                        if (m_update_right &&
                            ((is_app(e1) && !is_app(e2)) || /* ?m2 := ?m1 a_1 ... a_n */
                             (!mvar_has_user_facing_name(f2) && mvar_has_user_facing_name(f1)))) { /* ?m2 does not have a user facing name, but ?m1 has */
                            /* Remark: the second case (?m2 has user facing name but ?m1 doesn't) is particularly for
                               the equation preprocessor. See issue #1801. */
                            swap_update_flags_scope scope(*this);
                            /* We need to swap `m_update_left` and `m_update_right` because `process_assignment` uses `is_def_eq` */
                            return to_lbool(process_assignment(e2, e1));
                        } else {
                            return to_lbool(process_assignment(e1, e2));
                        }
                    } else {
                        lean_assert(m2_decl->get_context().is_subset_of(m1_decl->get_context()));
                        lean_assert(!m1_decl->get_context().is_subset_of(m2_decl->get_context()));
                        return to_lbool(process_assignment(e1, e2));
                    }
                } else {
                    lean_assert(!m2_decl->get_context().is_subset_of(m1_decl->get_context()));
                    if (m_update_right) {
                        swap_update_flags_scope scope(*this);
                        /* We need to swap `m_update_left` and `m_update_right` because `process_assignment` uses `is_def_eq` */
                        return to_lbool(process_assignment(e2, e1));
                    } else {
                        return l_false;
                    }
                }
            } else {
                return l_false;
            }
        } else {
            return l_false;
        }
    }

    if (is_mode_mvar(f2)) {
        lean_assert(!is_assigned(f2));
        if (optional<expr> ee1 = is_eta_expanded(e1)) {
            if (e2 == *ee1)
                return l_true; /* (fun x_1 ... x_n, ?m x_1 ... x_n) =?= ?m */
        }
        if (m_update_right) {
            swap_update_flags_scope scope(*this);
            /* We need to swap `m_update_left` and `m_update_right` because `process_assignment` uses `is_def_eq` */
            return to_lbool(process_assignment(e2, e1));
        } else {
            return l_false;
        }
    }

    if (e1.kind() == e2.kind()) {
        switch (e1.kind()) {
        case expr_kind::Lambda: case expr_kind::Pi:
            return to_lbool(is_def_eq_binding(e1, e2));
        case expr_kind::Sort:
            return to_lbool(is_def_eq(sort_level(e1), sort_level(e2)));
        case expr_kind::MData:
            return to_lbool(is_def_eq_core(mdata_expr(e1), mdata_expr(e2)));
        case expr_kind::Lit:
            return to_lbool(lit_value(e1) == lit_value(e2));
        case expr_kind::MVar:  case expr_kind::BVar:
        case expr_kind::FVar:  case expr_kind::App:
        case expr_kind::Const: case expr_kind::Proj:
        case expr_kind::Let:
            // We do not handle these cases in this method.
            break;
        }
    }
    return l_undef; // This is not an "easy case"
}

static bool same_head_symbol(expr const & t, expr const & s) {
    expr const & f_t = get_app_fn(t);
    expr const & f_s = get_app_fn(s);
    return is_constant(f_t) && is_constant(f_s) && const_name(f_t) == const_name(f_s);
}

expr type_context_old::try_to_unstuck_using_complete_instance(expr const & e) {
    lean_assert(is_stuck(e));
    /* This method tries to unstuck terms such as:

          @has_add.add nat ?m a b

          @nat.rec C cz cs (has_zero.zero nat ?m)

       by instantiating metavariables using type classes synthesis.

       In principle, we could simply invoke complete_instance(e).
       However, we use a small optimization to avoid visiting unnecessary terms.
       For a recursor application such as

          @nat.rec C cz cs (has_zero.zero nat ?m)

       It is sufficient to invoke complete_instance at the major premise

          @nat.rec C cz cs (has_zero.zero nat ?m)

       We believe this is an useful optimization since the major premise is usually
       much smaller than the whole term.

       The optimization is only relevant for modules that generate many
       is_def_eq queries that return false (e.g., simplifier).
       Reason: this method is invoked by on_is_def_eq_failure.

       Remark: on_is_def_eq_failure uses this method to allow us to solve constraints such as

          nat.succ n  =?=  @has_add.add nat ?m n 1

    */
    if (!is_app(e))
        return e; /* do nothing */
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (!is_constant(fn))
        return e; /* do nothing */
    constant_info info = env().get(const_name(fn));
    if (info.is_recursor()) {
        unsigned major_idx = info.to_recursor_val().get_major_idx();
        /* This is an optimization for recursor/eliminator applications.
           In this case, we only need to instantiate metavariables in the major premise */
        if (major_idx < args.size()) {
            expr major     = args[major_idx];
            expr new_major = complete_instance(major);
            if (new_major != major) {
                args[major_idx] = new_major;
                return mk_app(fn, args);
            }
        }
        return e;
    } else {
        /* For projections and other builtin constants that compute in the kernel, we
           do not have any special optimization, we just invoke complete_instance */
        return complete_instance(e);
    }
}

bool type_context_old::on_is_def_eq_failure(expr const & e1, expr const & e2) {
    lean_trace(name({"type_context", "is_def_eq_detail"}),
               scope_trace_env scope(env(), *this);
               tout() << "on failure: " << e1 << " =?= " << e2 << "\n";);

    if (is_stuck(e1)) {
        expr new_e1 = try_to_unstuck_using_complete_instance(e1);
        if (new_e1 != e1) {
            lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "synthesized instances on left\n";);
            return is_def_eq_core(new_e1, e2);
        }
    }

    if (is_stuck(e2)) {
        expr new_e2 = try_to_unstuck_using_complete_instance(e2);
        if (new_e2 != e2) {
            lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "synthesized instances on right\n";);
            return is_def_eq_core(e1, new_e2);
        }
    }

    return false;
}

/* If e is a numeral, then return it. Otherwise return none. */
static optional<mpz> eval_num(expr const & e) {
    check_system("eval_num");
    if (is_constant(e, get_nat_zero_name())) {
        return some(mpz(0));
    } else if (is_app_of(e, get_has_zero_zero_name(), 2)) {
        return some(mpz(0));
    } else if (is_app_of(e, get_has_one_one_name(), 2)) {
        return some(mpz(1));
    } else if (auto a = is_bit0(e)) {
        if (auto r1 = eval_num(*a))
            return some(mpz(2) * *r1);
        else
            return optional<mpz>();
    } else if (auto a = is_bit1(e)) {
        if (auto r1 = eval_num(*a))
            return some(mpz(2) * *r1 + 1);
        else
            return optional<mpz>();
    } else if (is_app_of(e, get_nat_succ_name(), 1)) {
        if (auto r1 = eval_num(app_arg(e)))
            return some(*r1 + 1);
        else
            return optional<mpz>();
    } else if (is_app_of(e, get_has_add_add_name(), 4)) {
        auto r1 = eval_num(app_arg(app_fn(e)));
        if (!r1) return optional<mpz>();
        auto r2 = eval_num(app_arg(e));
        if (!r2) return optional<mpz>();
        return some(*r1 + *r2);
    } else if (is_app_of(e, get_has_sub_sub_name(), 4)) {
        auto r1 = eval_num(app_arg(app_fn(e)));
        if (!r1) return optional<mpz>();
        auto r2 = eval_num(app_arg(e));
        if (!r2) return optional<mpz>();
        return some(*r2 > *r1 ? mpz(0) : *r1 - *r2);
    } else {
        return optional<mpz>();
    }
}

/* If e is a (small) numeral, then return it. Otherwise return none. */
optional<unsigned> type_context_old::to_small_num(expr const & e) {
    if (optional<mpz> r = eval_num(e)) {
        if (r->is_unsigned_int()) {
            unsigned r1 = r->get_unsigned_int();
            if (r1 <= m_cache->get_nat_offset_cnstr_threshold())
                return optional<unsigned>(r1);
        }
    }
    return optional<unsigned>();
}

/* If \c t is of the form (s + k) where k is a numeral, then return k. Otherwise, return none. */
optional<unsigned> type_context_old::is_offset_term (expr const & t) {
    if (is_app_of(t, get_has_add_add_name(), 4) &&
        /* We do not consider (s + k) to be an offset term when has_add.add is marked as irreducible */
        get_reducible_status(env(), get_has_add_add_name()) != reducible_status::Irreducible) {
        expr const & k = app_arg(t);
        return to_small_num(k);
    } else {
        unsigned k = 0;
        expr it = t;
        while (is_app_of(it, get_nat_succ_name(), 1)) {
            k++;
            it = app_arg(it);
        }
        if (k > 0 && k <= m_cache->get_nat_offset_cnstr_threshold())
            return optional<unsigned>(k);
        else
            return optional<unsigned>();
    }
}

/* Return true iff t is of the form (t' + k) where k is a numeral */
static expr get_offset_term(expr const & t) {
    if (is_app_of(t, get_has_add_add_name(), 4)) {
        return app_arg(app_fn(t));
    } else {
        lean_assert(is_app_of(t, get_nat_succ_name(), 1));
        expr it = t;
        while (is_app_of(it, get_nat_succ_name(), 1)) {
            it = app_arg(it);
        }
        return it;
    }
}

/* Return true iff t is of the form (@add _ nat_has_add a b)
   \pre is_offset_term(t) */
static bool uses_nat_has_add_instance_or_succ(type_context_old & ctx, expr const & t) {
    if (is_app_of(t, get_nat_succ_name(), 1)) {
        return true;
    } else if (is_app_of(t, get_has_add_add_name(), 4)) {
        expr inst = app_arg(app_fn(app_fn(t)));
        if (is_constant(inst, get_nat_has_add_name()))
            return true;
        if (is_metavar(inst)) {
            inst = ctx.instantiate_mvars(inst);
            return is_constant(inst, get_nat_has_add_name());
        } else {
            return false;
        }
    } else {
        return false;
    }
}

/* Given an offset term t, update its offset. There are two cases
   1) t is of the form (s + k')    ==> result is (s + k)
   2) t is of the form (succ^k' s) ==> result is (succ^k s) */
static expr update_offset(expr const & t, unsigned k) {
    lean_assert(k > 0);
    if (is_app_of(t, get_nat_succ_name(), 1)) {
        expr r = get_offset_term(t);
        expr succ = mk_constant(get_nat_succ_name());
        for (unsigned i = 0; i < k; i++)
            r = mk_app(succ, r);
        return r;
    } else {
        lean_assert(is_app_of(t, get_has_add_add_name(), 4));
        return mk_app(app_fn(app_fn(t)), get_offset_term(t), to_nat_expr(mpz(k)));
    }
}

/* Solve unification constraints of the form

       t' + k_1 =?= s' + k_2

   where k_1 and k_2 are numerals, and type is nat */
lbool type_context_old::try_offset_eq_offset(expr const & t, expr const & s) {
    optional<unsigned> k1 = is_offset_term(t);
    if (!k1) return l_undef;
    optional<unsigned> k2 = is_offset_term(s);
    if (!k2) return l_undef;

    if (!uses_nat_has_add_instance_or_succ(*this, t) && !uses_nat_has_add_instance_or_succ(*this, s))
        return l_undef;

    if (*k1 == *k2) {
        return to_lbool(is_def_eq_core(get_offset_term(t), get_offset_term(s)));
    } else if (*k1 > *k2) {
        return to_lbool(is_def_eq_core(update_offset(t, *k1 - *k2), get_offset_term(s)));
    } else {
        lean_assert(*k2 > *k1);
        return to_lbool(is_def_eq_core(get_offset_term(t), update_offset(s, *k2 - *k1)));
    }
}

/* Solve unification constraints of the form

       t' + k_1 =?= k_2

   where k_1 and k_2 are numerals, and type is nat */
lbool type_context_old::try_offset_eq_numeral(expr const & t, expr const & s) {
    optional<unsigned> k1 = is_offset_term(t);
    if (!k1) return l_undef;
    optional<unsigned> k2 = to_small_num(s);
    if (!k2) return l_undef;

    if (!uses_nat_has_add_instance_or_succ(*this, t))
        return l_undef;

    if (*k2 >= *k1) {
        return to_lbool(is_def_eq_core(get_offset_term(t), to_nat_expr(mpz(*k2 - *k1))));
    } else {
        lean_assert(*k2 < *k1);
        return l_false;
    }
}

/* Solve unification constraints of the form

       k_1 =?= k_2

   where k_1 and k_2 are numerals, and type is nat.

   If t and s are encoding distinct big numerals, we return l_false.
   If t and s are encoding the same samll numeral, we return l_true.
   Otherwise, we return l_undef.
*/
lbool type_context_old::try_numeral_eq_numeral(expr const & t, expr const & s) {
    optional<mpz> n1 = eval_num(t);
    if (!n1) return l_undef;
    optional<mpz> n2 = eval_num(s);
    if (!n2) return l_undef;
    if (!is_nat_type(whnf(infer(t))))
        return l_undef;
    if (*n1 != *n2)
        return l_false;
    else if (to_small_num(t) && to_small_num(s))
        return l_true;
    else
        return l_undef;
}

/* Solve offset constraints. See discussion at issue #1226 */
lbool type_context_old::try_nat_offset_cnstrs(expr const & t, expr const & s) {
    /* We should not use this feature when transparency_mode is none.
       See issue #1295 */
    if (m_transparency_mode == transparency_mode::None) return l_undef;
    lbool r;
    r = try_offset_eq_offset(t, s);
    if (r != l_undef) return r;
    r = try_offset_eq_numeral(t, s);
    if (r != l_undef) return r;
    {
        swap_update_flags_scope scope(*this);
        r = try_offset_eq_numeral(s, t);
        if (r != l_undef) return r;
    }
    return try_numeral_eq_numeral(t, s);
}

lbool type_context_old::is_def_eq_delta(expr const & t, expr const & s) {
    optional<constant_info> t_info = is_delta(t);
    optional<constant_info> s_info = is_delta(s);

    if (t_info && !s_info) {
        /* Only t can be delta reduced */
        lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold left: " << t_info->get_name() << "\n";);
        if (auto new_t = unfold_definition(t))
            return to_lbool(is_def_eq_core_core(*new_t, s));
        else
            return l_undef;
    } else if (!t_info && s_info) {
        /* Only s can be delta reduced */
        lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold right: " << s_info->get_name() << "\n";);
        if (auto new_s = unfold_definition(s))
            return to_lbool(is_def_eq_core_core(t, *new_s));
        else
            return l_undef;
    } else if (t_info && s_info) {
        /* Both can be delta reduced */
        if (is_eqp(*t_info, *s_info)) {
            /* Same constant */
            if (is_app(t) && is_app(s)) {
                bool has_postponed = !m_postponed.empty();
                if (!is_cached_failure(t, s)) {
                    /* Heuristic: try so solve (f a =?= f b) by solving (a =?= b) */
                    scope S(*this);
                    if (is_def_eq_args(t, s) &&
                        is_def_eq(const_levels(get_app_fn(t)), const_levels(get_app_fn(s))) &&
                        process_postponed(S)) {
                        S.commit();
                        return l_true;
                    } else if (!has_postponed && !has_expr_metavar(t) && !has_expr_metavar(s)) {
                        cache_failure(t, s);
                    }
                }
                /* Heuristic failed, then unfold both of them */
                lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold left&right: " << t_info->get_name() << "\n";);
                auto new_t = unfold_definition(t);
                auto new_s = unfold_definition(s);
                if (new_s && new_t)
                    return to_lbool(is_def_eq_core_core(*new_t, *new_s));
                else if (new_t)
                    return to_lbool(is_def_eq_core_core(*new_t, s));
                else if (new_s)
                    return to_lbool(is_def_eq_core_core(t, *new_s));
                else
                    return l_undef;
            } else if (!is_app(t) && !is_app(s)) {
                /* Unify c.{l_1, ..., l_k} =?= c.{l_1', ..., l_k'}

                   Remark: we ignore the case where c contains unused universe parameters. */
                return to_lbool(is_def_eq(const_levels(t), const_levels(s)));
            } else {
                return l_false;
            }
        } else {
            if (is_at_least_semireducible(m_transparency_mode)) {
                /* Consider the following two cases

                   If t_n is reducible (or an instance) and s_n is not ==> reduce t_n
                   If s_n is reducible (or an instance) and t_n is not ==> reduce s_n

                   Remark: this can only happen if transparency_mode
                   is Semireducible or All
                */
                auto rt_info = get_decl(transparency_mode::Instances, t_info->get_name());
                auto rs_info = get_decl(transparency_mode::Instances, s_info->get_name());
                if (rt_info && !rs_info) {
                    lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold (reducible) left: " << t_info->get_name() << "\n";);
                    if (auto new_t = unfold_definition(t))
                        return to_lbool(is_def_eq_core_core(*new_t, s));
                } else if (!rt_info && rs_info) {
                    lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold (reducible) right: " << s_info->get_name() << "\n";);
                    if (auto new_s = unfold_definition(s))
                        return to_lbool(is_def_eq_core_core(t, *new_s));
                }
            }

            /* If we haven't reduced t nor s, and they do not contain metavariables,
               then we try to use the definitional height to decide which one we will unfold
               (i.e., we mimic the behavior of the kernel type checker. */
            if (!has_expr_metavar(t) && !has_expr_metavar(s)) {
                int c = compare(t_info->get_hints(), s_info->get_hints());
                if (c < 0) {
                    if (auto new_t = unfold_definition(t))
                        return to_lbool(is_def_eq_core_core(*new_t, s));
                } else if (c > 0) {
                    if (auto new_s = unfold_definition(s))
                        return to_lbool(is_def_eq_core_core(t, *new_s));
                }
            }

            auto new_t = unfold_definition(t);
            if (new_t && same_head_symbol(*new_t, s))
                return to_lbool(is_def_eq_core_core(*new_t, s));
            auto new_s = unfold_definition(s);
            if (new_s && same_head_symbol(*new_s, t))
                return to_lbool(is_def_eq_core_core(t, *new_s));
            if (new_t && new_s)
                return to_lbool(is_def_eq_core_core(*new_t, *new_s));
            if (new_t)
                return to_lbool(is_def_eq_core_core(*new_t, s));
            if (new_s)
                return to_lbool(is_def_eq_core_core(t, *new_s));
        }
    }
    return l_undef;
}

lbool type_context_old::is_def_eq_proj(expr t, expr s) {
    optional<projection_info> t_proj = is_projection(t);
    optional<projection_info> s_proj = is_projection(s);
    if (t_proj && !s_proj) {
        if (auto t_n = reduce_projection_core(t_proj, t)) {
            return to_lbool(is_def_eq_core_core(*t_n, s));
        }
    } else if (!t_proj && s_proj) {
        if (auto s_n = reduce_projection_core(s_proj, s))
            return to_lbool(is_def_eq_core_core(t, *s_n));
    } else if (t_proj && s_proj) {
        if (t_proj->get_constructor() == s_proj->get_constructor()) {
            t = instantiate_mvars(t);
            s = instantiate_mvars(s);
            if (has_expr_metavar(t) || has_expr_metavar(s)) {
                /* If is the same projection, and at least one of them contain unassigned metavariables,
                   then we try to unify arguments.

                   Remark: this case is usually a bad idea if both
                   projections can be reduced. However, some
                   lemmas at init/algebra/order.lean cannot
                   be elaborated without it.

                   A potential workaround (hack): if both structures
                   can be reduced, then we do it only if the structure
                   has only one field.
                */
                scope S(*this);
                if (is_def_eq_core(get_app_fn(t), get_app_fn(s)) &&
                    is_def_eq_args(t, s) &&
                    process_postponed(S)) {
                    S.commit();
                    return l_true;
                }
            }
        }
        auto t_n = reduce_projection_core(t_proj, t);
        auto s_n = reduce_projection_core(s_proj, s);
        if (t_n && s_n) {
            /* Both projections can be reduced */
            return to_lbool(is_def_eq_core_core(*t_n, *s_n));
        } else if (t_n) {
            return to_lbool(is_def_eq_core_core(*t_n, s));
        } else if (s_n) {
            return to_lbool(is_def_eq_core_core(t, *s_n));
        }
    }
    return l_undef;
}

bool type_context_old::is_def_eq_core_core(expr t, expr s) {
    lbool r = quick_is_def_eq(t, s);
    if (r != l_undef) return r == l_true;

    flet<unsigned> inc_depth(m_is_def_eq_depth, m_is_def_eq_depth+1);
    lean_trace(name({"type_context", "is_def_eq_detail"}),
               scope_trace_env scope(env(), *this);
               tout() << "[" << m_is_def_eq_depth << "]: " << t << " =?= " << s << "\n";);

    /* Apply beta/zeta/iota reduction to t and s */
    {
        /* We do not reduce projections here. */
        expr t_n = whnf_core(t, false, true);
        expr s_n = whnf_core(s, false, true);

        if (!is_eqp(t_n, t) || !is_eqp(s_n, s)) {
            lean_trace(name({"type_context", "is_def_eq_detail"}),
                       scope_trace_env scope(env(), *this);
                       tout() << "after whnf_core: " << t_n << " =?= " << s_n << "\n";);
            r = quick_is_def_eq(t_n, s_n);
            if (r != l_undef) return r == l_true;
        }
        t = t_n;
        s = s_n;
    }

    r = try_nat_offset_cnstrs(t, s);
    if (r != l_undef) return r == l_true;

    check_system("is_def_eq");

    r = is_def_eq_delta(t, s);
    if (r != l_undef) return r == l_true;

    if (is_constant(t) && is_constant(s) && const_name(t) == const_name(s)) {
        return is_def_eq(const_levels(t), const_levels(s));
    }

    if (is_local(t) && is_local(s) && local_name(t) == local_name(s))
        return true;

    r = is_def_eq_proj(t, s);
    if (r != l_undef) return r == l_true;

    if (is_app(t) && is_app(s)) {
        scope S(*this);
        if (is_def_eq_core(get_app_fn(t), get_app_fn(s)) &&
            is_def_eq_args(t, s) &&
            process_postponed(S)) {
            S.commit();
            return true;
        }
    }

    if (is_def_eq_eta(t, s))
        return true;
    if (is_def_eq_eta(s, t))
        return true;
    if (is_def_eq_proof_irrel(t, s))
        return true;
    return on_is_def_eq_failure(t, s);
}

bool type_context_old::is_def_eq_core(expr const & t, expr const & s) {
    unsigned postponed_sz = m_postponed.size();
    bool r = is_def_eq_core_core(t, s);
    if (r && postponed_sz == m_postponed.size()) {
        cache_equiv(t, s);
    }
    return r;
}

bool type_context_old::is_def_eq(expr const & t, expr const & s) {
    scope S(*this);
    flet<bool> in_is_def_eq(m_in_is_def_eq, true);
    bool success = is_def_eq_core(t, s);
    lean_trace(name({"type_context", "is_def_eq"}),
               scope_trace_env scope(env(), *this);
               tout() << t << " =?= " << s << " ... "
               << (success ? "success" : "failed") << " " << (approximate() ? " (approximate mode)" : "") << "\n";);
    if (success && process_postponed(S)) {
        S.commit();
        return true;
    } else {
        return false;
    }
}

bool type_context_old::relaxed_is_def_eq(expr const & e1, expr const & e2) {
    relaxed_scope scope(*this);
    return is_def_eq(e1, e2);
}

/* -------------
   Type classes
   ------------- */

/** \brief If the constant \c e is a class, return its name */
optional<name> type_context_old::constant_is_class(expr const & e) {
    name const & cls_name = const_name(e);
    if (lean::is_class(env(), cls_name)) {
        return optional<name>(cls_name);
    } else {
        return optional<name>();
    }
}

optional<name> type_context_old::is_full_class(expr type) {
    expr new_type = whnf(type);
    if (is_pi(new_type)) {
        type = new_type;
        tmp_locals locals(*this);
        return is_full_class(::lean::instantiate(binding_body(type), locals.push_local_from_binding(type)));
    } else {
        // TODO(Leo): this can be improved using whnf_pred
        expr f = get_app_fn(type);
        if (is_constant(f)) {
            if (auto r = constant_is_class(f))
                return r;
        }
        f = get_app_fn(new_type);
        if (!is_constant(f))
            return optional<name>();
        return constant_is_class(f);
    }
}

/** \brief Partial/Quick test for is_class. Result
    l_true:   \c type is a class, and the name of the class is stored in \c result.
    l_false:  \c type is not a class.
    l_undef:  procedure did not establish whether \c type is a class or not. */
lbool type_context_old::is_quick_class(expr const & type, name & result) {
    expr const * it = &type;
    while (true) {
        switch (it->kind()) {
        case expr_kind::BVar: case expr_kind::Sort:   case expr_kind::FVar:
        case expr_kind::MVar: case expr_kind::Lambda: case expr_kind::Lit:
            return l_false;
        case expr_kind::Let:
            return l_undef;
        case expr_kind::Proj:
            return l_undef;
        case expr_kind::MData:
            it = &mdata_expr(*it);
            break;
        case expr_kind::Const:
            if (auto r = constant_is_class(*it)) {
                result = *r;
                return l_true;
            } else if (!get_decl(const_name(*it))) {
                return l_false;
            } else {
                return l_undef;
            }
        case expr_kind::App: {
            expr const & f = get_app_fn(*it);
            if (is_constant(f)) {
                if (auto r = constant_is_class(f)) {
                    result = *r;
                    return l_true;
                } else if (!get_decl(const_name(f))) {
                    return l_false;
                } else {
                    return l_undef;
                }
            } else if (is_lambda(f)) {
                return l_undef;
            } else {
                return l_false;
            }
        }
        case expr_kind::Pi:
            it = &binding_body(*it);
            break;
        }
    }
}

/** \brief Return true iff \c type is a class or Pi that produces a class. */
optional<name> type_context_old::is_class(expr const & type) {
    name result;
    switch (is_quick_class(type, result)) {
    case l_true:  return optional<name>(result);
    case l_false: return optional<name>();
    case l_undef: break;
    }
    return is_full_class(type);
}

[[ noreturn ]] static void throw_class_exception(expr const & m, char const * msg) { throw class_exception(m, msg); }

struct instance_synthesizer {
    struct stack_entry {
        expr     m_mvar;
        unsigned m_depth;
        stack_entry(expr const & m, unsigned d):
            m_mvar(m), m_depth(d) {}
    };

    struct state {
        list<stack_entry>  m_stack; // stack of meta-variables that need to be synthesized;
    };

    struct choice {
        list<expr>         m_local_instances;
        names         m_instances;
        state              m_state;
    };

    type_context_old &        m_ctx;
    expr                  m_main_mvar;
    state                 m_state;    // active state
    buffer<choice>        m_choices;
    bool                  m_displayed_trace_header;
    transparency_mode     m_old_transparency_mode;
    bool                  m_old_zeta;

    instance_synthesizer(type_context_old & ctx):
        m_ctx(ctx),
        m_displayed_trace_header(false),
        m_old_transparency_mode(m_ctx.m_transparency_mode),
        m_old_zeta(m_ctx.m_zeta) {
        lean_assert(m_ctx.in_tmp_mode());
        m_ctx.m_transparency_mode = transparency_mode::Instances;
        m_ctx.m_zeta              = true;
    }

    ~instance_synthesizer() {
        for (unsigned i = 0; i < m_choices.size(); i++) {
            m_ctx.pop_scope();
        }
        m_ctx.m_transparency_mode = m_old_transparency_mode;
        m_ctx.m_zeta              = m_old_zeta;
    }

    environment const & env() const { return m_ctx.env(); }

    void push_scope() {
        lean_trace(name({"type_context", "tmp_vars"}), tout() << "push_scope, trail_sz: " << m_ctx.m_tmp_data->m_trail.size() << "\n";);
        m_ctx.push_scope();
    }

    void pop_scope() {
        lean_trace(name({"type_context", "tmp_vars"}), tout() << "pop_scope, trail_sz: " << m_ctx.m_tmp_data->m_trail.size() << "\n";);
        m_ctx.pop_scope();
    }

    bool is_done() const {
        return empty(m_state.m_stack);
    }

    void trace(unsigned depth, expr const & mvar, expr const & mvar_type, expr const & r) {
        auto out = tout();
        if (!m_displayed_trace_header && m_choices.size() == 1) {
            out << tclass("class_instances");
            out << " class-instance resolution trace" << endl;
            m_displayed_trace_header = true;
        }
        out << tclass("class_instances") << "(" << depth << ") ";
        out << mvar << " : " << m_ctx.instantiate_mvars(mvar_type) << " := " << r << endl;
    }

    /* Try to synthesize e.m_mvar using instance inst : inst_type. */
    bool try_instance(stack_entry const & e, expr const & inst, expr const & inst_type) {
        try {
            type_context_old::tmp_locals locals(m_ctx);
            expr const & mvar = e.m_mvar;
            expr mvar_type    = m_ctx.infer(mvar);
            while (true) {
                expr new_mvar_type = m_ctx.relaxed_whnf(mvar_type);
                if (!is_pi(new_mvar_type))
                    break;
                mvar_type   = new_mvar_type;
                expr local  = locals.push_local_from_binding(mvar_type);
                mvar_type   = instantiate(binding_body(mvar_type), local);
            }
            expr type  = inst_type;
            expr r     = inst;
            buffer<expr> new_inst_mvars;
            while (true) {
                expr new_type = m_ctx.relaxed_whnf(type);
                if (!is_pi(new_type))
                    break;
                type          = new_type;
                expr new_mvar = m_ctx.mk_tmp_mvar(locals.mk_pi(binding_domain(type)));
                if (is_inst_implicit(binding_info(type))) {
                    new_inst_mvars.push_back(new_mvar);
                }
                expr new_arg = mk_app(new_mvar, locals.as_buffer());
                r    = mk_app(r, new_arg);
                type = instantiate(binding_body(type), new_arg);
            }
            lean_trace_plain("class_instances",
                             scope_trace_env scope(m_ctx.env(), m_ctx);
                             trace(e.m_depth, mk_app(mvar, locals.as_buffer()), mvar_type, r););
            if (!m_ctx.is_def_eq(mvar_type, type)) {
                lean_trace_plain("class_instances", tout() << "failed is_def_eq\n";);
                return false;
            }
            r = locals.mk_lambda(r);
            m_ctx.assign(mvar, r);
            // copy new_inst_mvars to stack
            unsigned i = new_inst_mvars.size();
            while (i > 0) {
                --i;
                m_state.m_stack = cons(stack_entry(new_inst_mvars[i], e.m_depth+1), m_state.m_stack);
            }
            return true;
        } catch (exception & ex) {
            lean_trace_plain("class_instances", tout() << "exception: " << ex.what() << "\n";);
            return false;
        }
    }

    bool try_instance(stack_entry const & e, name const & inst_name) {
        if (auto decl = env().find(inst_name)) {
            buffer<level> ls_buffer;
            unsigned num_lparams = decl->get_num_lparams();
            for (unsigned i = 0; i < num_lparams; i++)
                ls_buffer.push_back(m_ctx.mk_tmp_univ_mvar());
            levels ls(ls_buffer);
            expr inst_cnst = mk_constant(inst_name, ls);
            expr inst_type = instantiate_type_lparams(*decl, ls);
            return try_instance(e, inst_cnst, inst_type);
        } else {
            return false;
        }
    }

    list<expr> get_local_instances(name const & cname) {
        buffer<expr> selected;
        for (local_instance const & li : m_ctx.m_local_instances) {
            if (li.get_class_name() == cname)
                selected.push_back(li.get_local());
        }
        return to_list(selected);
    }

    bool mk_choice_point(expr const & mvar) {
        lean_assert(is_metavar(mvar));
        if (m_choices.size() > m_ctx.m_cache->get_class_instance_max_depth()) {
            throw_class_exception(m_ctx.infer(m_main_mvar),
                                  "maximum class-instance resolution depth has been reached "
                                  "(the limit can be increased by setting option 'class.instance_max_depth') "
                                  "(the class-instance resolution trace can be visualized "
                                  "by setting option 'trace.class_instances')");
        }
        // Remark: we initially tried to reject branches where mvar_type contained unassigned metavariables.
        // The idea was to make the procedure easier to understand.
        // However, it turns out this is too restrictive. The group_theory folder contains the following instance.
        //     nsubg_setoid : Π {A : Type} [s : group A] (N : set A) [is_nsubg : @is_normal_subgroup A s N], setoid A
        // When it is used, it creates a subproblem for
        //    is_nsubg : @is_normal_subgroup A s ?N
        // where ?N is not known. Actually, we can only find the value for ?N by constructing the instance is_nsubg.
        expr mvar_ty       = m_ctx.instantiate_mvars(mvar_type(mvar));
        m_choices.push_back(choice());
        push_scope();
        choice & r = m_choices.back();
        auto cname = m_ctx.is_class(mvar_ty);
        if (!cname)
            return false;
        r.m_local_instances = get_local_instances(*cname);
        r.m_instances = get_class_instances(env(), *cname);
        if (empty(r.m_local_instances) && empty(r.m_instances))
            return false;
        r.m_state = m_state;
        return true;
    }

    bool process_next_alt_core(stack_entry const & e, list<expr> & insts) {
        while (!empty(insts)) {
            expr inst       = head(insts);
            insts           = tail(insts);
            expr inst_type  = m_ctx.infer(inst);
            if (try_instance(e, inst, inst_type))
                return true;
        }
        return false;
    }

    bool process_next_alt_core(stack_entry const & e, names & inst_names) {
        while (!empty(inst_names)) {
            name inst_name    = head(inst_names);
            inst_names        = tail(inst_names);
            if (try_instance(e, inst_name))
                return true;
        }
        return false;
    }

    bool process_next_alt(stack_entry const & e) {
        lean_assert(m_choices.size() > 0);
        lean_assert(!m_choices.empty());
        buffer<choice> & cs = m_choices;
        list<expr> locals = cs.back().m_local_instances;
        if (process_next_alt_core(e, locals)) {
            cs.back().m_local_instances = locals;
            return true;
        }
        cs.back().m_local_instances = list<expr>();
        names insts = cs.back().m_instances;
        if (process_next_alt_core(e, insts)) {
            cs.back().m_instances = insts;
            return true;
        }
        cs.back().m_instances = names();
        return false;
    }

    bool process_next_mvar() {
        lean_assert(!is_done());
        stack_entry e = head(m_state.m_stack);
        if (!mk_choice_point(e.m_mvar))
            return false;
        m_state.m_stack = tail(m_state.m_stack);
        return process_next_alt(e);
    }

    bool backtrack() {
        if (m_choices.empty())
            return false;
        lean_assert(!m_choices.empty());
        while (true) {
            m_choices.pop_back();
            pop_scope();
            if (m_choices.empty())
                return false;
            pop_scope(); push_scope(); // restore assignment
            m_state         = m_choices.back().m_state;
            stack_entry e   = head(m_state.m_stack);
            m_state.m_stack = tail(m_state.m_stack);
            if (process_next_alt(e))
                return true;
        }
    }

    optional<expr> search() {
        while (!is_done()) {
            if (!process_next_mvar()) {
                if (!backtrack())
                    return none_expr();
            }
        }
        return some_expr(m_ctx.instantiate_mvars(m_main_mvar));
    }

    optional<expr> next_solution() {
        if (m_choices.empty())
            return none_expr();
        pop_scope(); push_scope(); // restore assignment
        m_state         = m_choices.back().m_state;
        stack_entry e   = head(m_state.m_stack);
        m_state.m_stack = tail(m_state.m_stack);
        if (process_next_alt(e))
            return search();
        else if (backtrack())
            return search();
        else
            return none_expr();
    }

    optional<expr> ensure_no_meta(optional<expr> r) {
        while (true) {
            if (!r) {
                return none_expr();
            }
            if (!has_expr_metavar(*r)) {
                if (has_idx_metavar(*r)) {
                    /* r has universe metavariables.
                       Try to instantiate them. */
                    r = m_ctx.instantiate_mvars(*r);
                }
                if (!has_idx_metavar(*r)) {
                    return r;
                }
            }
            lean_trace("class_instances",
                       scope_trace_env scope(m_ctx.env(), m_ctx);
                       tout() << "trying next solution, current solution has metavars\n" << *r << "\n";);
            r = next_solution();
        }
    }

    optional<expr> mk_class_instance_core(expr const & type) {
        /* We do not cache results when multiple instances have to be generated. */
        m_state          = state();
        m_main_mvar      = m_ctx.mk_tmp_mvar(type);
        m_state.m_stack  = to_list(stack_entry(m_main_mvar, 0));
        auto r = search();
        return ensure_no_meta(r);
    }

    optional<expr> main(expr const & type) {
        auto r = mk_class_instance_core(type);
        if (r) {
            for (unsigned i = 0; i < m_choices.size(); i++) {
                m_ctx.commit_scope();
            }
            m_choices.clear();
        }
        return r;
    }

    optional<expr> operator()(expr const & type) {
        flet<bool> scope_left(m_ctx.m_update_left, true);
        flet<bool> scope_right(m_ctx.m_update_right, true);
        time_task t("typeclass inference",
                    message_builder(environment(), get_global_ios(), "foo", pos_info(), message_severity::INFORMATION));
        if (is_trace_enabled() && !is_trace_class_enabled("class_instances")) {
            scope_trace_silent scope(true);
            return main(type);
        } else {
            lean_trace_init_bool("class_instances", get_pp_purify_metavars_name(), false);
            lean_trace_init_bool("class_instances", get_pp_implicit_name(), true);
            return main(type);
        }
    }
};

static bool depends_on_mvar(expr const & e, buffer<expr> const & mvars) {
    // TODO(Leo): improve performance if needed
    for (expr const & mvar : mvars) {
        if (occurs(mvar, e))
            return true;
    }
    return false;
}

/*
Type class parameters can be annotated with out_param annotations.

Given (C a_1 ... a_n), we replace a_i with a temporary metavariable ?x_i IF
- Case 1
   a_i is an out_param
OR
- Case 2
   a_i depends on a_j for j < i, and a_j was replaced with a temporary metavariable ?x_j.
   This case is needed to make sure the new C-application is type correct.
   It may be counterintuitive to some users.
   @kha and @leodemoura have discussed a different approach
   where a type class declaration is rejected IF
   it contains a regular parameter X that depends on an `out` parameter Y.
   If we reject this kind of declaration, then we don't need
   this extra case which may artificially treat regular parameters
   as `out` (**).

Then, we execute type class resolution as usual.
If it succeeds, and metavariables ?x_i have been assigned, we solve the unification
constraints ?x_i =?= a_i. If we succeed, we return the result. Otherwise, we fail.

We store the pairs (a_i, ?x_i) in the buffer expr_replacements.

Remark: when we still had inout params in type classes (versions <= 3.3),
@kha and @leodemoura have considered a different design
where nested metavariables occurring in a_i are replaced with
temporary metavariables. For example, suppose we have

```
class foo (α : out Type) := (a : α)
instance foo2 : foo (set ℕ) := ⟨{1}⟩
instance foo1 : foo ℕ := ⟨0⟩

#check foo.a (set _)
```

When we preprocesses `foo (set ?m)`, we obtain `foo ?x_0`. Then, we produce
the solution s with `?x_0 := nat`, which fails at `?x_0 =?= set ?m`.
To obtain the correct solution, we need to backtrack and try other instances.
Remark: backtracking is a nasty feature since it would be an indirect way
of influencing the result of the type class resolution procedure based on
(partial) information available in the `inout` parameter.

Alternatively, if we replace nested metavariables with temporary ones,
we would obtain `foo (set ?x_0)` after preprocessing `foo (set ?m)`,
and we would find the right instance.

This approach has been discarded because it is tricky to produce
a type correct. We don't have a simple trick like the case 2 above,
or a simple syntactic restriction (see ** comment above)
to prevent the type correctness issue. Here is a problematic scenario:

- Suppose we have `f (A : Type), A -> A -> A`, `a : ?m_1`, and `?m_2 : ?m_1`,
  and we want to process `bla (f ?m_1 a ?m_2)'`. The resulting term
  `bla (f ?x_1 a ?x_2)` where `?x_1 : Type`, `?x_2 : ?x_1` are fresh
  tmp metavars is type incorrect.

Another problem is that regular metavariables may be created in different contexts.
However, we assume all temporary metavars share the same local context (this is reasonable since they are temporary after all: that is, we create them in a local context; use them; and discard).
This may be an issue when mapping multiple regular metavariables to temporary metavariables.

Finally, there is a potential performance issue because we would have to traverse
terms searching for unassigned metavariables for implementing this translation.

For all these reasons, we have discarded this alternative design.
*/
expr type_context_old::preprocess_class(expr const & type,
                                    buffer<level_pair> & u_replacements,
                                    buffer<expr_pair> &  e_replacements) {
    if (!has_metavar(type)) {
        expr const & C = get_app_fn(type);
        if (is_constant(C) && !has_class_out_params(env(), const_name(C)))
            return type;
    }
    type_context_old::tmp_locals locals(*this);
    expr it = type;
    while (true) {
        expr new_it = relaxed_whnf(it);
        if (!is_pi(new_it))
            break;
        expr local  = locals.push_local_from_binding(new_it);
        it          = instantiate(binding_body(new_it), local);
    }
    buffer<expr> C_args;
    buffer<expr> new_mvars;
    expr C = get_app_args(it, C_args);
    if (!is_constant(C) || !constant_is_class(C))
        return type;
    buffer<level> C_levels;
    for (level const & l : const_levels(C)) {
        if (has_mvar(l)) {
            level new_uvar = mk_tmp_univ_mvar();
            u_replacements.emplace_back(l, new_uvar);
            C_levels.push_back(new_uvar);
        } else {
            C_levels.push_back(l);
        }
    }
    if (!u_replacements.empty())
        C = update_constant(C, levels(C_levels));
    expr it2 = infer(C);
    for (expr & C_arg : C_args) {
        it2  = relaxed_whnf(it2);
        if (!is_pi(it2))
            return type; /* failed */
        expr const & d = binding_domain(it2);
        if (/* Case 1 */
            is_class_out_param(d) ||
            /* Case 2 */
            depends_on_mvar(d, new_mvars)) {
            expr new_mvar = mk_tmp_mvar(locals.mk_pi(d));
            new_mvars.push_back(new_mvar);
            expr new_arg  = mk_app(new_mvar, locals.as_buffer());
            e_replacements.emplace_back(C_arg, new_arg);
            C_arg = new_arg;
        }
        it2 = instantiate(binding_body(it2), C_arg);
    }
    expr new_class = mk_app(C, C_args);
    return locals.mk_pi(new_class);
}

static void instantiate_replacements(type_context_old & ctx,
                                     buffer<level_pair> & u_replacements,
                                     buffer<expr_pair> &  e_replacements) {
    for (level_pair & p : u_replacements) {
        p.second = ctx.instantiate_mvars(p.second);
    }
    for (expr_pair & p : e_replacements) {
        p.second = ctx.instantiate_mvars(p.second);
    }
}

optional<expr> type_context_old::mk_class_instance(expr const & type_0) {
    expr type = instantiate_mvars(type_0);
    scope S(*this);
    fo_unif_approx_scope  as1(*this);
    ctx_unif_approx_scope as2(*this);
    optional<expr> result;
    buffer<level_pair> u_replacements;
    buffer<expr_pair>  e_replacements;
    if (in_tmp_mode()) {
        expr new_type = preprocess_class(type, u_replacements, e_replacements);
        result        = instance_synthesizer(*this)(new_type);
        if (result)
            instantiate_replacements(*this, u_replacements, e_replacements);
    } else {
        tmp_mode_scope s(*this);
        expr new_type = preprocess_class(type, u_replacements, e_replacements);
        result        = instance_synthesizer(*this)(new_type);
        if (result)
            instantiate_replacements(*this, u_replacements, e_replacements);
    }
    if (result) {
        for (level_pair & p : u_replacements) {
            /* If p.second still contains temporary universe metavariables,
               we fail since it is not safe to execute `is_def_eq` and
               have the temporary universe metavariable leak into p.first. */
            if (has_idx_metauniv(p.second))
                return none_expr();
            if (!is_def_eq(p.first, p.second)) {
                return none_expr();
            }
        }
        for (expr_pair & p : e_replacements) {
            /* If p.second still contains temporary universe metavariables,
               we fail since it is not safe to execute `is_def_eq` and
               have the temporary universe metavariable leak into p.first. */
            if (has_idx_metavar(p.second))
                return none_expr();
            if (!is_def_eq_core(p.first, p.second)) {
                return none_expr();
            }
        }
        S.commit();
    }
    return result;
}

optional<expr> type_context_old::mk_subsingleton_instance(expr const & type) {
    expr Type  = whnf(infer(type));
    if (!is_sort(Type)) {
        return none_expr();
    }
    level lvl    = sort_level(Type);
    expr subsingleton = mk_app(mk_constant(get_subsingleton_name(), {lvl}), type);
    optional<expr> r = mk_class_instance(subsingleton);
    return r;
}

/* -------------
   Auxiliary
   ------------- */

expr type_context_old::eta_expand(expr const & e) {
    tmp_locals locals(*this);
    expr it = e;
    while (is_lambda(it)) {
        expr d = instantiate_rev(binding_domain(it), locals.as_buffer().size(), locals.as_buffer().data());
        locals.push_local(binding_name(it), d, binding_info(it));
        it     = binding_body(it);
    }
    it = instantiate_rev(it, locals.as_buffer().size(), locals.as_buffer().data());
    expr it_type = relaxed_whnf(infer(it));
    if (!is_pi(it_type)) return e;
    buffer<expr> extra_args;
    while (is_pi(it_type)) {
        expr arg = locals.push_local_from_binding(it_type);
        extra_args.push_back(arg);
        it_type  = relaxed_whnf(instantiate(binding_body(it_type), arg));
    }
    expr r = mk_app(it, extra_args);
    return locals.mk_lambda(r);
}

/** \brief Helper class for pretty printing terms that contain local_decl_ref's and metavar_decl_ref's */
class pp_ctx {
    type_context_old m_ctx;
    formatter    m_fmt;
public:
    pp_ctx(environment const & env, options const & opts, metavar_context const & mctx, local_context const & lctx):
        m_ctx(env, opts, mctx, lctx),
        m_fmt(get_global_ios().get_formatter_factory()(env, opts, m_ctx)) {}
    format pp(expr const & e) {
        return m_fmt(m_ctx.instantiate_mvars(e));
    }
};

std::function<format(expr const &)>
mk_pp_ctx(environment const & env, options const & opts, metavar_context const & mctx, local_context const & lctx) {
    auto pp_fn = std::make_shared<pp_ctx>(env, opts, mctx, lctx);
    return [=](expr const & e) { // NOLINT
        metavar_context mctx_tmp(mctx);
        return pp_fn->pp(mctx_tmp.instantiate_mvars(e));
    };
}

std::function<format(expr const &)>
mk_pp_ctx(type_context_old const & ctx) {
    return mk_pp_ctx(ctx.env(), ctx.get_options(), ctx.mctx(), ctx.lctx());
}

void initialize_type_context() {
    register_trace_class("class_instances");
    register_trace_class(name({"type_context", "is_def_eq"}));
    register_trace_class(name({"type_context", "mvar_deps"}));
    register_trace_class(name({"type_context", "is_def_eq_detail"}));
    register_trace_class(name({"type_context", "univ_is_def_eq"}));
    register_trace_class(name({"type_context", "univ_is_def_eq_detail"}));
    register_trace_class(name({"type_context", "smart_unfolding"}));
    register_trace_class(name({"type_context", "tmp_vars"}));
    register_trace_class("type_context_cache");
}

void finalize_type_context() {
}
}
