/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/flet.h"
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/error_msgs.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/inductive/inductive.h"
#include "library/trace.h"
#include "library/class.h"
#include "library/pp_options.h"
#include "library/annotation.h"
#include "library/idx_metavar.h"
#include "library/reducible.h"
#include "library/constants.h"
#include "library/metavar_util.h"
#include "library/exception.h"
#include "library/type_context.h"
#include "library/locals.h"
#include "library/aux_recursors.h"
#include "library/attribute_manager.h"
#include "library/unification_hint.h"
#include "library/delayed_abstraction.h"
#include "library/fun_info.h"
#include "library/num.h"

#ifndef LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH
#define LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH 32
#endif

#ifndef LEAN_DEFAULT_NAT_OFFSET_CNSTR_THRESHOLD
#define LEAN_DEFAULT_NAT_OFFSET_CNSTR_THRESHOLD 256
#endif

namespace lean {
static name * g_class_instance_max_depth = nullptr;
static name * g_nat_offset_threshold     = nullptr;

unsigned get_class_instance_max_depth(options const & o) {
    return o.get_unsigned(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH);
}

unsigned get_nat_offset_cnstr_threshold(options const & o) {
    return o.get_unsigned(*g_nat_offset_threshold, LEAN_DEFAULT_NAT_OFFSET_CNSTR_THRESHOLD);
}

/* =====================
   type_context_cache
   ===================== */

type_context_cache::type_context_cache(environment const & env, options const & opts, bool use_bi):
    m_env(env),
    m_options(opts),
    m_proj_info(get_projection_info_map(env)),
    m_infer_cache(use_bi) {
    m_ci_max_depth               = get_class_instance_max_depth(opts);
    m_nat_offset_cnstr_threshold = get_nat_offset_cnstr_threshold(opts);
    lean_trace("type_context_cache", tout() << "type_context_cache constructed\n";);
}

bool type_context_cache::is_transparent(transparency_mode m, declaration const & d) {
    if (m == transparency_mode::None)
        return false;
    name const & n = d.get_name();
    if (m_proj_info.contains(n))
        return false;
    if (m == transparency_mode::All)
        return true;
    if (d.is_theorem())
        return false;
    auto s = get_reducible_status(m_env, d.get_name());
    if (m == transparency_mode::Reducible && s == reducible_status::Reducible)
        return true;
    if (m == transparency_mode::Semireducible && s != reducible_status::Irreducible)
        return true;
    return false;
}

optional<declaration> type_context_cache::is_transparent(transparency_mode m, name const & n) {
    auto & cache = m_transparency_cache[static_cast<unsigned>(m)];
    auto it = cache.find(n);
    if (it != cache.end()) {
        return it->second;
    }
    optional<declaration> r;
    if (auto d = m_env.find(n)) {
        if (d->is_definition() && is_transparent(m, *d)) {
            r = d;
        }
    }
    cache.insert(mk_pair(n, r));
    return r;
}

bool type_context_cache::should_unfold_macro(expr const &) {
    // TODO(Leo): add predicate
    return true;
}

bool type_context_cache::is_aux_recursor(name const & n) {
    auto it = m_aux_recursor_cache.find(n);
    if (it != m_aux_recursor_cache.end())
        return it->second;
    bool r = ::lean::is_aux_recursor(env(), n);
    m_aux_recursor_cache.insert(mk_pair(n, r));
    return r;
}

type_context_cache::scope_pos_info::scope_pos_info(type_context_cache & o, pos_info_provider const * pip,
                                                   expr const & pos_ref):
    m_owner(o),
    m_old_pip(m_owner.m_pip),
    m_old_pos(m_owner.m_ci_pos) {
    m_owner.m_pip = pip;
    if (pip)
        m_owner.m_ci_pos = pip->get_pos_info(pos_ref);
}

type_context_cache::scope_pos_info::~scope_pos_info() {
    m_owner.m_pip    = m_old_pip;
    m_owner.m_ci_pos = m_old_pos;
}

/* =====================
   type_context_cache_manager
   ===================== */

static type_context_cache_ptr mk_cache(environment const & env, options const & o, bool use_bi) {
    return std::make_shared<type_context_cache>(env, o, use_bi);
}

type_context_cache_ptr type_context_cache_manager::release() {
    type_context_cache_ptr c = m_cache_ptr;
    m_cache_ptr.reset();
    return c;
}

type_context_cache_ptr type_context_cache_manager::mk(environment const & env, options const & o) {
    if (!m_cache_ptr || get_class_instance_max_depth(o) != m_max_depth) return mk_cache(env, o, m_use_bi);
    if (is_eqp(env, m_env)) {
        m_cache_ptr->m_options = o;
        return release();
    }
    if (!env.is_descendant(m_env) ||
        get_reducibility_fingerprint(env) != m_reducibility_fingerprint ||
        get_instance_fingerprint(env) != m_instance_fingerprint) {
        lean_trace("type_context_cache",
                   bool c1 = (get_reducibility_fingerprint(env) == m_reducibility_fingerprint);
                   bool c2 = (get_instance_fingerprint(env) == m_instance_fingerprint);
                   tout() << "creating new cache, is_descendant: " << env.is_descendant(m_env)
                   << ", reducibility compatibility: " << c1 << ", instance compatibility: " << c2 << "\n";);
        return mk_cache(env, o, m_use_bi);
    }
    m_cache_ptr->m_options = o;
    m_cache_ptr->m_env     = env;
    return release();
}

void type_context_cache_manager::recycle(type_context_cache_ptr const & ptr) {
    m_max_depth = ptr->m_ci_max_depth;
    m_cache_ptr = ptr;
    if (!is_eqp(ptr->m_env, m_env)) {
        m_env = ptr->m_env;
        m_reducibility_fingerprint = get_reducibility_fingerprint(ptr->m_env);
        m_instance_fingerprint     = get_instance_fingerprint(ptr->m_env);
    }
    if (!ptr->m_instance_fingerprint) {
        ptr->m_instance_cache.clear();
        ptr->m_subsingleton_cache.clear();
    }
}

/* =====================
   type_context::tmp_locals
   ===================== */
type_context::tmp_locals::~tmp_locals() {
    for (unsigned i = 0; i < m_locals.size(); i++)
        m_ctx.pop_local();
}

bool type_context::tmp_locals::all_let_decls() const {
    for (expr const & l : m_locals) {
        if (optional<local_decl> d = m_ctx.m_lctx.get_local_decl(l)) {
            if (!d->get_value())
                return false;
        } else {
            lean_unreachable();
        }
    }
    return true;
}

/* =====================
   type_context
   ===================== */
MK_THREAD_LOCAL_GET_DEF(type_context_cache_manager, get_tcm);

void type_context::cache_failure(expr const & t, expr const & s) {
    if (t.hash() <= s.hash())
        get_failure_cache().insert(mk_pair(t, s));
    else
        get_failure_cache().insert(mk_pair(s, t));
}

bool type_context::is_cached_failure(expr const & t, expr const & s) {
    if (has_expr_metavar(t) || has_expr_metavar(s)) return false;
    type_context_cache::failure_cache const & fcache = get_failure_cache();
    if (t.hash() < s.hash()) {
        return fcache.find(mk_pair(t, s)) != fcache.end();
    } else if (t.hash() > s.hash()) {
        return fcache.find(mk_pair(s, t)) != fcache.end();
    } else {
        return
            fcache.find(mk_pair(t, s)) != fcache.end() ||
            fcache.find(mk_pair(s, t)) != fcache.end();
    }
}

void type_context::init_local_instances() {
    m_local_instances = list<pair<name, expr>>();
    m_lctx.for_each([&](local_decl const & decl) {
            if (auto cls_name = is_class(decl.get_type())) {
                m_local_instances = cons(mk_pair(*cls_name, decl.mk_ref()), m_local_instances);
            }
        });
}

void type_context::flush_instance_cache() {
    lean_trace("type_context_cache", tout() << "flushing instance cache\n";);
    m_cache->m_instance_fingerprint = optional<unsigned>();
    m_cache->m_local_instances      = list<pair<name, expr>>();
    m_cache->m_instance_cache.clear();
    m_cache->m_subsingleton_cache.clear();
}

void type_context::set_instance_fingerprint() {
    lean_assert(!m_lctx.get_instance_fingerprint());
    unsigned fingerprint = local_context::get_empty_instance_fingerprint();
    m_lctx.for_each([&](local_decl const & decl) {
            if (auto cls_name = is_class(decl.get_type())) {
                fingerprint = hash(fingerprint, hash(cls_name->hash(), decl.get_type().hash()));
            }
        });
    m_lctx.m_instance_fingerprint   = optional<unsigned>(fingerprint);
    m_cache->m_instance_fingerprint = optional<unsigned>(fingerprint);
    m_cache->m_local_instances      = m_local_instances;
    lean_trace("type_context_cache", tout() << "set_instance_fingerprint: " << fingerprint << "\n";);
}

void type_context::init_core(transparency_mode m) {
    m_used_assignment             = false;
    m_transparency_mode           = m;
    m_in_is_def_eq                = false;
    m_is_def_eq_depth             = 0;
    m_tmp_uassignment             = nullptr;
    m_tmp_eassignment             = nullptr;
    m_unfold_pred                 = nullptr;
    m_approximate                 = false;
    if (auto instance_fingerprint = m_lctx.get_instance_fingerprint()) {
        if (m_cache->m_instance_fingerprint == instance_fingerprint) {
            lean_trace("type_context_cache", tout() << "reusing instance cache, fingerprint: " << *instance_fingerprint << "\n";);
            m_local_instances = m_cache->m_local_instances;
        } else {
            lean_trace("type_context_cache", tout() << "incompatible fingerprints, flushing instance cache\n";);
            init_local_instances();
            flush_instance_cache();
            m_cache->m_instance_fingerprint = m_lctx.get_instance_fingerprint();
            m_cache->m_local_instances      = m_local_instances;
        }
    } else {
        init_local_instances();
        flush_instance_cache();
    }
    lean_assert(m_cache->m_instance_fingerprint == m_lctx.get_instance_fingerprint());
}

type_context::type_context(environment const & env, options const & o, metavar_context const & mctx,
                           local_context const & lctx, transparency_mode m):
    type_context(env, o, mctx, lctx, get_tcm(), m) {
}

type_context::type_context(environment const & env, options const & o, metavar_context const & mctx,
                           local_context const & lctx, type_context_cache_manager & manager, transparency_mode m):
    m_mctx(mctx), m_lctx(lctx),
    m_cache_manager(&manager),
    m_cache(manager.mk(env, o)) {
    init_core(m);
}

/** This constructor is only used internally during type class resolution. */
type_context::type_context(type_context_cache_ptr const & ptr, metavar_context const & mctx, local_context const & lctx,
                           transparency_mode m):
    m_mctx(mctx), m_lctx(lctx),
    m_cache_manager(nullptr),
    m_cache(ptr) {
    init_core(m);
}

type_context::~type_context() {
    if (m_cache_manager)
        m_cache_manager->recycle(m_cache);
}

void type_context::set_env(environment const & env) {
    lean_assert(m_cache->m_instance_fingerprint == m_lctx.get_instance_fingerprint());
    options o = m_cache->m_options;
    if (m_cache_manager) {
        m_cache_manager->recycle(m_cache);
        m_cache = m_cache_manager->mk(env, o);

    } else {
        m_cache = mk_cache(env, o, false);
    }
    if (m_lctx.get_instance_fingerprint()) {
        m_cache->m_instance_fingerprint = m_lctx.get_instance_fingerprint();
        m_cache->m_local_instances      = m_local_instances;
    }
    lean_assert(m_cache->m_instance_fingerprint == m_lctx.get_instance_fingerprint());
}

void type_context::update_local_instances(expr const & new_local, expr const & new_type) {
    if (!m_cache->m_instance_fingerprint) {
        if (auto c_name = is_class(new_type)) {
            m_local_instances = cons(mk_pair(*c_name, new_local), m_local_instances);
            flush_instance_cache();
        }
    }
}

expr type_context::push_local(name const & pp_name, expr const & type, binder_info const & bi) {
    expr local = m_lctx.mk_local_decl(pp_name, type, bi);
    update_local_instances(local, type);
    return local;
}

expr type_context::push_let(name const & ppn, expr const & type, expr const & value) {
    expr local = m_lctx.mk_local_decl(ppn, type, value);
    update_local_instances(local, type);
    return local;
}

void type_context::pop_local() {
    if (!m_cache->m_instance_fingerprint && m_local_instances) {
        local_decl decl = *m_lctx.get_last_local_decl();
        if (decl.get_name() == mlocal_name(head(m_local_instances).second)) {
            m_local_instances = tail(m_local_instances);
            flush_instance_cache();
        }
    }
    m_lctx.pop_local_decl();
}

pair<local_context, expr> type_context::revert_core(buffer<expr> & to_revert, local_context const & ctx,
                                                    expr const & type) {
    DEBUG_CODE({
            for (unsigned i = 0; i < to_revert.size(); i++) {
                lean_assert(is_local_decl_ref(to_revert[i]));
                optional<local_decl> decl = ctx.get_local_decl(to_revert[i]);
                lean_assert(decl);
                if (i > 1) {
                    optional<local_decl> prev_decl = ctx.get_local_decl(to_revert[i-1]);
                    lean_assert(prev_decl && prev_decl->get_idx() < decl->get_idx());
                }
            }
        });
    unsigned num   = to_revert.size();
    if (num == 0) {
        return mk_pair(ctx, type);
    }
    local_decl d0  = *ctx.get_local_decl(to_revert[0]);
    unsigned next_idx = 1;
    unsigned init_sz  = to_revert.size();
    ctx.for_each_after(d0, [&](local_decl const & d) {
            /* Check if d is in initial to_revert */
            for (unsigned i = next_idx; i < num; i++) {
                if (mlocal_name(to_revert[i]) == d.get_name()) {
                    next_idx++;
                    return;
                }
            }
            /* We may still need to revert d if it depends on locals already in reverted */
            if (depends_on(d, m_mctx, to_revert)) {
                if (d.get_info().is_rec()) {
                    /* We should not revert auxiliary declarations added by the equation compiler.
                       See discussion at issue #1258 at github. */
                    sstream out;
                    out << "failed to revert ";
                    for (unsigned i = 0; i < init_sz; i++) {
                        if (i > 0) out << " ";
                        out << "'" << to_revert[i] << "'";
                    }
                    out << ", '" << d.get_pp_name() << "' "
                        << "depends on " << (init_sz == 1 ? "it" : "them")
                        << ", and '" << d.get_pp_name() << "' is an auxiliary declaration "
                        << "introduced by the equation compiler (possible solution: "
                        << "use tactic 'clear' to remove '" << d.get_pp_name() << "' "
                        << "from the local context)\n";
                    throw exception(out);
                }
                to_revert.push_back(d.mk_ref());
            }
        });
    local_context new_ctx = ctx.remove(to_revert);
    return mk_pair(new_ctx, mk_pi(ctx, to_revert, type));
}

expr type_context::revert_core(buffer<expr> & to_revert, expr const & mvar) {
    lean_assert(is_metavar_decl_ref(mvar));
    metavar_decl const & d = *m_mctx.get_metavar_decl(mvar);
    auto p = revert_core(to_revert, d.get_context(), d.get_type());
    /* Remark: we use copy_tag to make sure any position information
       associated wtih mvar is inherited by the new meta-variable. */
    return copy_tag(mvar, m_mctx.mk_metavar_decl(p.first, p.second));
}

expr type_context::revert(buffer<expr> & to_revert, expr const & mvar) {
    lean_assert(is_metavar_decl_ref(mvar));
    lean_assert(std::all_of(to_revert.begin(), to_revert.end(), [&](expr const & l) {
                return static_cast<bool>(m_mctx.get_metavar_decl(mvar)->get_context().get_local_decl(l)); }));
    local_context lctx = m_mctx.get_metavar_decl(mvar)->get_context();
    expr new_mvar = revert_core(to_revert, mvar);
    expr r = new_mvar;
    for (expr const & a : to_revert) {
        if (!lctx.get_local_decl(a)->get_value()) {
            // 'a' is not a let-decl
            r = mk_app(r, a);
        }
    }
    m_mctx.assign(mvar, r);
    return r;
}

/* We use delayed_abstract_locals to make sure the variables being abstracted
   will be abstracted correctly when any unassigned metavar ?M occurring in \c e gets instantiated. */
expr type_context::abstract_locals(expr const & e, unsigned num_locals, expr const * locals) {
    lean_assert(std::all_of(locals, locals+num_locals, is_local_decl_ref));
    if (num_locals == 0)
        return e;
    if (in_tmp_mode()) {
        /* 1- Regular metavariables should not depend on temporary local constants that have been created in tmp mode.
           2- The tmp metavariables all share the same fixed local context. */
        return ::lean::abstract_locals(e, num_locals, locals);
    }
    expr new_e = instantiate_mvars(e);
    return delayed_abstract_locals(new_e, num_locals, locals);
}

expr type_context::mk_binding(bool is_pi, local_context const & lctx, unsigned num_locals, expr const * locals, expr const & e) {
    buffer<local_decl>     decls;
    buffer<expr>           types;
    buffer<optional<expr>> values;
    for (unsigned i = 0; i < num_locals; i++) {
        local_decl const & decl = *lctx.get_local_decl(locals[i]);
        decls.push_back(decl);
        types.push_back(abstract_locals(instantiate_mvars(decl.get_type()), i, locals));
        if (auto v = decl.get_value())
            values.push_back(some_expr(abstract_locals(instantiate_mvars(*v), i, locals)));
        else
            values.push_back(none_expr());
    }
    expr new_e = abstract_locals(instantiate_mvars(e), num_locals, locals);
    lean_assert(types.size() == values.size());
    unsigned i = types.size();
    while (i > 0) {
        --i;
        if (values[i]) {
            new_e = mk_let(decls[i].get_pp_name(), types[i], *values[i], new_e);
        } else if (is_pi) {
            new_e = ::lean::mk_pi(decls[i].get_pp_name(), types[i], new_e, decls[i].get_info());
        } else {
            new_e = ::lean::mk_lambda(decls[i].get_pp_name(), types[i], new_e, decls[i].get_info());
        }
    }
    return new_e;
}

expr type_context::mk_lambda(local_context const & lctx, buffer<expr> const & locals, expr const & e) {
    return mk_binding(false, lctx, locals.size(), locals.data(), e);
}

expr type_context::mk_pi(local_context const & lctx, buffer<expr> const & locals, expr const & e) {
    return mk_binding(true, lctx, locals.size(), locals.data(), e);
}

expr type_context::mk_lambda(local_context const & lctx, expr const & local, expr const & e) {
    return mk_binding(false, lctx, 1, &local, e);
}

expr type_context::mk_pi(local_context const & lctx, expr const & local, expr const & e) {
    return mk_binding(true, lctx, 1, &local, e);
}

expr type_context::mk_lambda(local_context const & lctx, std::initializer_list<expr> const & locals, expr const & e) {
    return mk_binding(false, lctx, locals.size(), locals.begin(), e);
}

expr type_context::mk_pi(local_context const & lctx, std::initializer_list<expr> const & locals, expr const & e) {
    return mk_binding(true, lctx, locals.size(), locals.begin(), e);
}

expr type_context::mk_lambda(buffer<expr> const & locals, expr const & e) {
    return mk_lambda(m_lctx, locals, e);
}

expr type_context::mk_pi(buffer<expr> const & locals, expr const & e) {
    return mk_pi(m_lctx, locals, e);
}

expr type_context::mk_lambda(expr const & local, expr const & e) {
    return mk_lambda(m_lctx, local, e);
}

expr type_context::mk_pi(expr const & local, expr const & e) {
    return mk_pi(m_lctx, local, e);
}

expr type_context::mk_lambda(std::initializer_list<expr> const & locals, expr const & e) {
    return mk_lambda(m_lctx, locals, e);
}

expr type_context::mk_pi(std::initializer_list<expr> const & locals, expr const & e) {
    return mk_pi(m_lctx, locals, e);
}

/* ---------------------
   Normalization
   -------------------- */

optional<declaration> type_context::is_transparent(transparency_mode m, name const & n) {
    return m_cache->is_transparent(m, n);
}

optional<declaration> type_context::is_transparent(name const & n) {
    return is_transparent(m_transparency_mode, n);
}

/* Unfold \c e if it is a constant */
optional<expr> type_context::unfold_definition_core(expr const & e) {
    if (is_constant(e)) {
        if (auto d = is_transparent(const_name(e))) {
            if (length(const_levels(e)) == d->get_num_univ_params())
                return some_expr(instantiate_value_univ_params(*d, const_levels(e)));
        }
    }
    return none_expr();
}

/* Unfold head(e) if it is a constant */
optional<expr> type_context::unfold_definition(expr const & e) {
    if (is_app(e)) {
        expr f0 = get_app_fn(e);
        if (auto f  = unfold_definition_core(f0)) {
            buffer<expr> args;
            get_app_rev_args(e, args);
            return some_expr(apply_beta(*f, args.size(), args.data()));
        } else {
            return none_expr();
        }
    } else {
        return unfold_definition_core(e);
    }
}

optional<expr> type_context::try_unfold_definition(expr const & e) {
    if (m_unfold_pred && !(*m_unfold_pred)(e))
        return none_expr();
    return unfold_definition(e);
}

optional<expr> type_context::reduce_projection(expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    projection_info const * info = m_cache->m_proj_info.find(const_name(f));
    if (!info)
        return none_expr();
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() <= info->m_nparams)
        return none_expr();
    unsigned mkidx  = info->m_nparams;
    expr const & mk = args[mkidx];
    expr new_mk     = whnf(mk);
    expr const & new_mk_fn = get_app_fn(new_mk);
    if (!is_constant(new_mk_fn) || const_name(new_mk_fn) != info->m_constructor)
        return none_expr();
    buffer<expr> mk_args;
    get_app_args(new_mk, mk_args);
    unsigned i = info->m_nparams + info->m_i;
    if (i >= mk_args.size())
        none_expr();
    expr r = mk_args[i];
    r = mk_app(r, args.size() - mkidx - 1, args.data() + mkidx + 1);
    return some_expr(r);
}

optional<expr> type_context::reduce_aux_recursor(expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    if (m_cache->is_aux_recursor(const_name(f)))
        return try_unfold_definition(e);
    else
        return none_expr();
}

bool type_context::should_unfold_macro(expr const & e) {
    /* If m_transparency_mode is set to ALL, then we unfold all
       macros. In this way, we make sure type inference does not fail.
       We also unfold macros when reducing inside of is_def_eq. */
    return
        m_transparency_mode == transparency_mode::All ||
        m_in_is_def_eq ||
        m_cache->should_unfold_macro(e);
}

optional<expr> type_context::expand_macro(expr const & e) {
    lean_assert(is_macro(e));
    if (should_unfold_macro(e)) {
        return macro_def(e).expand(e, *this);
    } else {
        return none_expr();
    }
}

bool type_context::use_zeta() const {
    return m_zeta;
}

/*
  Apply beta-reduction, zeta-reduction (i.e., unfold let local-decls), iota-reduction,
  unfold macros, expand let-expressions, expand assigned meta-variables.

  This method does *not* apply delta-reduction at the head.
  Reason: we want to perform these reductions lazily at is_def_eq.

  Remark: this method delta-reduce (transparent) aux-recursors (e.g., cases_on, rec_on).
*/
expr type_context::whnf_core(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var:      case expr_kind::Sort:
    case expr_kind::Pi:       case expr_kind::Lambda:
    case expr_kind::Constant:
        /* Remark: we do not unfold Constants eagerly in this method */
        return e;
    case expr_kind::Local:
        if (use_zeta() && is_local_decl_ref(e)) {
            if (auto d = m_lctx.get_local_decl(e)) {
                if (auto v = d->get_value()) {
                    /* zeta-reduction */
                    return whnf_core(*v);
                }
            }
        }
        return e;
    case expr_kind::Meta:
        if (is_metavar_decl_ref(e)) {
            if (m_mctx.is_assigned(e)) {
                m_used_assignment = true;
                return whnf_core(m_mctx.instantiate_mvars(e));
            }
        } else if (is_idx_metavar(e)) {
            lean_assert(in_tmp_mode());
            unsigned idx = to_meta_idx(e);
            if (idx < m_tmp_eassignment->size()) {
                if (auto v = (*m_tmp_eassignment)[idx]) {
                    m_used_assignment = true;
                    return whnf_core(*v);
                }
            }
        }
        return e;
    case expr_kind::Macro:
        if (auto m = expand_macro(e)) {
            check_system("whnf");
            return whnf_core(*m);
        } else {
            return e;
        }
    case expr_kind::Let:
        check_system("whnf");
        return use_zeta() ? whnf_core(::lean::instantiate(let_body(e), let_value(e))) : e;
    case expr_kind::App: {
        check_system("whnf");
        buffer<expr> args;
        expr f0 = get_app_rev_args(e, args);
        expr f  = whnf_core(f0);
        if (is_lambda(f)) {
            /* beta-reduction */
            unsigned m = 1;
            unsigned num_args = args.size();
            while (is_lambda(binding_body(f)) && m < num_args) {
                f = binding_body(f);
                m++;
            }
            lean_assert(m <= num_args);
            return whnf_core(mk_rev_app(::lean::instantiate(binding_body(f), m, args.data() + (num_args - m)),
                                        num_args - m, args.data()));
        } else if (f == f0) {
            if (auto r = norm_ext(e)) {
                /* mainly iota-reduction, it also applies HIT and quotient reduction rules */
                return whnf_core(*r);
            } else if (auto r = reduce_projection(e)) {
                return whnf_core(*r);
            } else if (auto r = reduce_aux_recursor(e)) {
                return whnf_core(*r);
            } else {
                return e;
            }
        } else {
            return whnf_core(mk_rev_app(f, args.size(), args.data()));
        }
    }}
    lean_unreachable();
}

expr type_context::whnf(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var:      case expr_kind::Sort:
    case expr_kind::Pi:       case expr_kind::Lambda:
        return e;
    default:
        break;
    }
    auto & cache = m_cache->m_whnf_cache[static_cast<unsigned>(m_transparency_mode)];
    auto it = cache.find(e);
    if (it != cache.end())
        return it->second;
    reset_used_assignment reset(*this);
    unsigned postponed_sz = m_postponed.size();
    expr t = e;
    while (true) {
        expr t1 = whnf_core(t);
        if (auto next_t = unfold_definition(t1)) {
            t = *next_t;
        } else {
            if (!m_used_assignment && !is_stuck(t1) && postponed_sz == m_postponed.size())
                cache.insert(mk_pair(e, t1));
            return t1;
        }
    }
}

expr type_context::whnf_pred(expr const & e, std::function<bool(expr const &)> const & pred) { // NOLINT
    flet<std::function<bool(expr const &)> const *>set_unfold_pred(m_unfold_pred, &pred); // NOLINT
    expr t = e;
    while (true) {
        expr t1 = whnf_core(t);
        if (auto next_t = try_unfold_definition(t1)) {
            t = *next_t;
        } else {
            return t1;
        }
    }
}

expr type_context::relaxed_whnf(expr const & e) {
    relaxed_scope scope(*this);
    return whnf(e);
}

optional<expr> type_context::is_stuck_projection(expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f)) return none_expr(); // it is not projection app
    projection_info const * info = m_cache->m_proj_info.find(const_name(f));
    if (!info) return none_expr(); // it is not projection app
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() <= info->m_nparams) return none_expr(); // partially applied projection
    unsigned mkidx  = info->m_nparams;
    expr mk         = args[mkidx];
    return is_stuck(mk);
}

optional<expr> type_context::is_stuck(expr const & e) {
    if (is_meta(e)) {
        return some_expr(e);
    } else if (auto r = is_stuck_projection(e)) {
        return r;
    } else if (is_annotation(e)) {
        return is_stuck(get_annotation_arg(e));
    } else {
        return env().norm_ext().is_stuck(e, *this);
    }
}

expr type_context::try_to_pi(expr const & e) {
    expr new_e = whnf(e);
    if (is_pi(new_e))
        return new_e;
    else
        return e;
}

expr type_context::relaxed_try_to_pi(expr const & e) {
    relaxed_scope scope(*this);
    return try_to_pi(e);
}

/* ---------------
   Type inference
   --------------- */

expr type_context::infer(expr const & e) {
    relaxed_scope scope(*this);
    return infer_core(e);
}

expr type_context::infer_core(expr const & e) {
    lean_assert(!is_var(e));
    lean_assert(closed(e));

    auto & cache = m_cache->m_infer_cache;
    unsigned postponed_sz = m_postponed.size();
    auto it = cache.find(e);
    if (it != cache.end())
        return it->second;

    reset_used_assignment reset(*this);

    expr r;
    switch (e.kind()) {
    case expr_kind::Local:
        r = infer_local(e);
        break;
    case expr_kind::Meta:
        r = infer_metavar(e);
        break;
    case expr_kind::Var:
        lean_unreachable();  // LCOV_EXCL_LINE
    case expr_kind::Sort:
        r = mk_sort(mk_succ(sort_level(e)));
        break;
    case expr_kind::Constant:
        r = infer_constant(e);
        break;
    case expr_kind::Macro:
        r = infer_macro(e);
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

    if (!m_used_assignment && postponed_sz == m_postponed.size())
        cache.insert(mk_pair(e, r));
    return r;
}

expr type_context::infer_local(expr const & e) {
    lean_assert(is_local(e));
    if (is_local_decl_ref(e)) {
        auto d = m_lctx.get_local_decl(e);
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
        return mlocal_type(e);
    }
}

static void throw_unknown_metavar(expr const & e) {
    throw generic_exception(e, [=](formatter const & fmt) {
            return format("infer type failed, unknown metavariable") + pp_indent_expr(fmt, e);
        });
}

expr type_context::infer_metavar(expr const & e) {
    if (is_metavar_decl_ref(e)) {
        auto d = m_mctx.get_metavar_decl(e);
        if (!d) throw_unknown_metavar(e);
        return d->get_type();
    } else {
        /* tmp metavariables should only occur in tmp_mode.
           The following assertion was commented because the pretty printer may violate it. */
        // lean_assert(!is_idx_metavar(e) || in_tmp_mode());
        return mlocal_type(e);
    }
}

expr type_context::infer_constant(expr const & e) {
    declaration d   = env().get(const_name(e));
    auto const & ps = d.get_univ_params();
    auto const & ls = const_levels(e);
    if (length(ps) != length(ls)) {
        throw generic_exception(e, [=](formatter const & fmt) {
                auto new_fmt = fmt.update_option_if_undef(get_pp_universes_name(), true);
                return format("infer type failed, incorrect number of universe levels") + pp_indent_expr(new_fmt, e);
            });
    }
    return instantiate_type_univ_params(d, ls);
}

expr type_context::infer_macro(expr const & e) {
    if (is_delayed_abstraction(e)) {
        expr const & mvar = get_delayed_abstraction_expr(e);
        if (!is_metavar_decl_ref(mvar)) {
            throw generic_exception(e, [=](formatter const & fmt) {
                    return format("unexpected occurrence of delayed abstraction macro") + pp_indent_expr(fmt, e)
                        + line() + format("term") + pp_indent_expr(fmt, mvar)
                        + line() + format("is not a metavariable in this context");
                });
        }
        buffer<name> ns;
        buffer<expr> es;
        get_delayed_abstraction_info(e, ns, es);
        auto d = m_mctx.get_metavar_decl(mvar);
        if (!d) throw_unknown_metavar(mvar);
        return push_delayed_abstraction(d->get_type(), ns, es);
    }
    auto def = macro_def(e);
    bool infer_only = true;
    return def.check_type(e, *this, infer_only);
}

expr type_context::infer_lambda(expr e) {
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
    expr r = abstract_locals(t, ls.size(), ls.data());
    unsigned i = es.size();
    while (i > 0) {
        --i;
        r = ::lean::mk_pi(binding_name(es[i]), ds[i], r, binding_info(es[i]));
    }
    return r;
}

optional<level> type_context::get_level_core(expr const & A) {
    lean_assert(m_transparency_mode == transparency_mode::All);
    expr A_type = whnf(infer_core(A));
    while (true) {
        if (is_sort(A_type)) {
            return some_level(sort_level(A_type));
        } else if (is_mvar(A_type)) {
            if (auto v = get_assignment(A_type)) {
                A_type = *v;
            } else if (!in_tmp_mode() && is_metavar_decl_ref(A_type)) {
                /* We should only assign A_type IF we are not in tmp mode. */
                level r = m_mctx.mk_univ_metavar_decl();
                assign(A_type, mk_sort(r));
                return some_level(r);
            } else if (in_tmp_mode() && is_idx_metavar(A_type)) {
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

level type_context::get_level(expr const & A) {
    if (auto r = get_level_core(A)) {
        return *r;
    } else {
        throw generic_exception(A, [=](formatter const & fmt) {
                return format("infer type failed, sort expected") + pp_indent_expr(fmt, A);
            });
    }
}

expr type_context::infer_pi(expr e) {
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

expr type_context::infer_app(expr const & e) {
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
                        return format("infer type failed, function expected at") + pp_indent_expr(fmt, e)
                            + line() + format("term") + pp_indent_expr(fmt, f)
                            + line() + format("has type") + pp_indent_expr(fmt, f_type);
                    });
            }
            f_type = binding_body(f_type);
            j = i;
        }
    }
    return instantiate_rev(f_type, nargs-j, args.data()+j);
}

expr type_context::infer_let(expr e) {
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

expr type_context::check(expr const & e) {
    // TODO(Leo): infer doesn't really check anything
    return infer(e);
}

bool type_context::is_prop(expr const & e) {
    expr t = whnf(infer(e));
    return t == mk_Prop();
}

bool type_context::is_proof(expr const & e) {
    return is_prop(infer(e));
}

/* -------------------------------
   Temporary assignment mode support
   ------------------------------- */
void type_context::set_tmp_mode(buffer<optional<level>> & tmp_uassignment, buffer<optional<expr>> & tmp_eassignment) {
    lean_assert(!in_tmp_mode());
    lean_assert(m_tmp_trail.empty());
    m_tmp_mvar_lctx = m_lctx;
    m_tmp_uassignment = &tmp_uassignment;
    m_tmp_eassignment = &tmp_eassignment;
}

void type_context::reset_tmp_mode() {
    lean_trace(name({"type_context", "tmp_vars"}), tout() << "clear tmp vars\n";);
    m_tmp_trail.clear();
    m_tmp_uassignment = nullptr;
    m_tmp_eassignment = nullptr;
}

void type_context::ensure_num_tmp_mvars(unsigned num_uvars, unsigned num_mvars) {
    lean_assert(in_tmp_mode());
    if (m_tmp_uassignment->size() < num_uvars)
        m_tmp_uassignment->resize(num_uvars, none_level());
    if (m_tmp_eassignment->size() < num_mvars)
        m_tmp_eassignment->resize(num_mvars, none_expr());
}

optional<level> type_context::get_tmp_uvar_assignment(unsigned idx) const {
    lean_assert(in_tmp_mode());
    lean_assert(idx < m_tmp_uassignment->size());
    return (*m_tmp_uassignment)[idx];
}

optional<expr> type_context::get_tmp_mvar_assignment(unsigned idx) const {
    lean_assert(in_tmp_mode());
    lean_assert(idx < m_tmp_eassignment->size());
    return (*m_tmp_eassignment)[idx];
}

optional<level> type_context::get_tmp_assignment(level const & l) const {
    lean_assert(is_idx_metauniv(l));
    return get_tmp_uvar_assignment(to_meta_idx(l));
}

optional<expr> type_context::get_tmp_assignment(expr const & e) const {
    lean_assert(is_idx_metavar(e));
    return get_tmp_mvar_assignment(to_meta_idx(e));
}

void type_context::assign_tmp(level const & u, level const & l) {
    lean_assert(in_tmp_mode());
    lean_assert(is_idx_metauniv(u));
    lean_assert(to_meta_idx(u) < m_tmp_uassignment->size());
    unsigned idx = to_meta_idx(u);
    if (!m_scopes.empty() && !(*m_tmp_uassignment)[idx]) {
        m_tmp_trail.emplace_back(tmp_trail_kind::Level, idx);
    }
    (*m_tmp_uassignment)[idx] = l;
}

void type_context::assign_tmp(expr const & m, expr const & v) {
    lean_assert(in_tmp_mode());
    lean_assert(is_idx_metavar(m));
    lean_assert(to_meta_idx(m) < m_tmp_eassignment->size());
    unsigned idx = to_meta_idx(m);
    lean_trace(name({"type_context", "tmp_vars"}),
               tout() << "assign ?x_" << idx << " := " << v << "\n";);
    if (!m_scopes.empty() && !(*m_tmp_eassignment)[idx]) {
        m_tmp_trail.emplace_back(tmp_trail_kind::Expr, idx);
    }
    (*m_tmp_eassignment)[to_meta_idx(m)] = v;
}

level type_context::mk_tmp_univ_mvar() {
    lean_assert(in_tmp_mode());
    unsigned idx = m_tmp_uassignment->size();
    m_tmp_uassignment->push_back(none_level());
    return mk_idx_metauniv(idx);
}

expr type_context::mk_tmp_mvar(expr const & type) {
    lean_assert(in_tmp_mode());
    unsigned idx = m_tmp_eassignment->size();
    m_tmp_eassignment->push_back(none_expr());
    return mk_idx_metavar(idx, type);
}

void type_context::clear_tmp_eassignment() {
    lean_assert(in_tmp_mode());
    m_tmp_eassignment->clear();
}

/* -----------------------------------
   Uniform interface to temporary & regular metavariables
   ----------------------------------- */
bool type_context::is_mvar_core(level const & l) const {
    return (in_tmp_mode() && is_idx_metauniv(l)) || is_metavar_decl_ref(l);
}

bool type_context::is_mvar_core(expr const & e) const {
    return (in_tmp_mode() && is_idx_metavar(e)) || is_metavar_decl_ref(e);
}

bool type_context::is_mvar(level const & l) const {
    if (in_tmp_mode())
        return is_idx_metauniv(l);
    else
        return is_metavar_decl_ref(l);
}

bool type_context::is_mvar(expr const & e) const {
    if (in_tmp_mode())
        return is_idx_metavar(e);
    else
        return is_metavar_decl_ref(e);
}

bool type_context::is_assigned(level const & l) const {
    const_cast<type_context*>(this)->m_used_assignment = true;
    if (in_tmp_mode() && is_idx_metauniv(l))
        return static_cast<bool>(get_tmp_assignment(l));
    else
        return m_mctx.is_assigned(l);
}

bool type_context::is_assigned(expr const & e) const {
    const_cast<type_context*>(this)->m_used_assignment = true;
    if (in_tmp_mode() && is_idx_metavar(e))
        return static_cast<bool>(get_tmp_assignment(e));
    else
        return m_mctx.is_assigned(e);
}

optional<level> type_context::get_assignment(level const & l) const {
    const_cast<type_context*>(this)->m_used_assignment = true;
    if (in_tmp_mode() && is_idx_metauniv(l))
        return get_tmp_assignment(l);
    else
        return m_mctx.get_assignment(l);
}

optional<expr> type_context::get_assignment(expr const & e) const {
    const_cast<type_context*>(this)->m_used_assignment = true;
    if (in_tmp_mode() && is_idx_metavar(e))
        return get_tmp_assignment(e);
    else
        return m_mctx.get_assignment(e);
}

void type_context::assign(level const & u, level const & l) {
    m_used_assignment = true;
    if (in_tmp_mode() && is_idx_metauniv(u))
        assign_tmp(u, l);
    else
        m_mctx.assign(u, l);
}

void type_context::assign(expr const & m, expr const & v) {
    m_used_assignment = true;
    if (in_tmp_mode() && is_idx_metavar(m))
        assign_tmp(m, v);
    else
        m_mctx.assign(m, v);
}

level type_context::instantiate_mvars(level const & l) {
    return ::lean::instantiate_mvars(*this, l);
}

expr type_context::instantiate_mvars(expr const & e) {
    return ::lean::instantiate_mvars(*this, e);
}

/* -----------------------------------
   Backtracking
   ----------------------------------- */

void type_context::push_scope() {
    if (in_tmp_mode()) {
        m_scopes.emplace_back(m_mctx, m_tmp_uassignment->size(), m_tmp_eassignment->size(), m_tmp_trail.size());
    } else {
        m_scopes.emplace_back(m_mctx, 0, 0, 0);
    }
}

void type_context::pop_scope() {
    lean_assert(!m_scopes.empty());
    scope_data const & s = m_scopes.back();
    m_mctx = s.m_mctx;
    if (in_tmp_mode()) {
        unsigned old_sz = s.m_tmp_trail_sz;
        while (m_tmp_trail.size() > old_sz) {
            auto const & t = m_tmp_trail.back();
            if (t.first == tmp_trail_kind::Level) {
                (*m_tmp_uassignment)[t.second] = none_level();
            } else {
                lean_trace(name({"type_context", "tmp_vars"}),
                           tout() << "unassign ?x_" << t.second << " := " << *((*m_tmp_eassignment)[t.second]) << "\n";);
                (*m_tmp_eassignment)[t.second] = none_expr();
            }
            m_tmp_trail.pop_back();
        }
        lean_assert(old_sz == m_tmp_trail.size());
        m_tmp_uassignment->shrink(s.m_tmp_uassignment_sz);
        m_tmp_eassignment->shrink(s.m_tmp_eassignment_sz);
    }
    m_scopes.pop_back();
}

void type_context::commit_scope() {
    lean_assert(!m_scopes.empty());
    m_scopes.pop_back();
}

/* -----------------------------------
   Unification / definitional equality
   ----------------------------------- */

static bool is_max_like(level const & l) {
    return is_max(l) || is_imax(l);
}

lbool type_context::is_def_eq_core(level const & l1, level const & l2, bool partial) {
    if (is_equivalent(l1, l2))
        return l_true;

    lean_trace(name({"type_context", "univ_is_def_eq_detail"}),
               tout() << "[" << m_is_def_eq_depth << "]: " << l1 << " =?= " << l2 << "\n";);

    flet<unsigned> inc_depth(m_is_def_eq_depth, m_is_def_eq_depth+1);

    level new_l1 = instantiate_mvars(l1);
    level new_l2 = instantiate_mvars(l2);

    if (l1 != new_l1 || l2 != new_l2)
        return is_def_eq_core(new_l1, new_l2, partial);

    if (is_mvar(l1)) {
        lean_assert(!is_assigned(l1));
        if (!occurs(l1, l2)) {
            assign(l1, l2);
            return l_true;
        }
    }

    if (is_mvar(l2)) {
        lean_assert(!is_assigned(l2));
        if (!occurs(l2, l1)) {
            assign(l2, l1);
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
    case level_kind::Global:
        return l_false;
    case level_kind::Meta:
        /* This can happen, for example, when we are in tmp_mode, but l1 and l2 are not tmp universe metavariables. */
        return l_false;
    case level_kind::Zero:
        lean_unreachable();
    }
    lean_unreachable();
}

lbool type_context::partial_is_def_eq(level const & l1, level const & l2) {
    return is_def_eq_core(l1, l2, true);
}

bool type_context::full_is_def_eq(level const & l1, level const & l2) {
    lbool r = is_def_eq_core(l1, l2, false);
    lean_assert(r != l_undef);
    return r == l_true;
}

bool type_context::is_def_eq(level const & l1, level const & l2) {
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

bool type_context::is_def_eq(levels const & ls1, levels const & ls2) {
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

bool type_context::process_postponed(scope const & s) {
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
optional<declaration> type_context::is_delta(expr const & e) {
    expr const & f = get_app_fn(e);
    if (is_constant(f)) {
        return is_transparent(const_name(f));
    } else {
        return none_declaration();
    }
}

bool type_context::approximate() {
    return in_tmp_mode() || m_approximate;
}

/* If \c e is a let local-decl, then unfold it, otherwise return e. */
expr type_context::try_zeta(expr const & e) {
    if (!is_local_decl_ref(e))
        return e;
    if (auto d = m_lctx.get_local_decl(e)) {
        if (auto v = d->get_value())
            return *v;
    }
    return e;
}

expr type_context::expand_let_decls(expr const & e) {
    return replace(e, [&](expr const & e, unsigned) {
            if (is_local_decl_ref(e)) {
                if (auto d = m_lctx.get_local_decl(e)) {
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
     (approximated) solution (when approximate() predicate returns true) :
     ignore condition and also use

        ?M := fun a_1 ... a_n, t

   Here is an example where this approximation fails:
   Given `C` containing `a : nat`, consider the following two constraints
         ?M@C a =?= a
         ?M@C b =?= a

   If we use the approximation in the first constraint, we get
         ?M := fun x, x
   when we apply this solution to the second one we get a failure.

 A3) `a_1 ... a_n` are not pairwise distinct (failed condition 1).
   We can approximate again, but the limitations are very similar to the previous one.

 A4) `t` contains a metavariable `?M'@C'` where `C'` is not a subset of `C`.
   (approximated) solution: restrict the context of `?M'`
   If `?M'` is assigned, the workaround is precise, and we just unfold `?M'`.

 A5) If some `a_i` is not a local constant,
     then we use first-order unification (if approximate() is true)

       ?M a_1 ... a_i a_{i+1} ... a_{i+k} =?= f b_1 ... b_k

   reduces to

       ?M a_1 ... a_i =?= f
       a_{i+1}        =?= b_1
       ...
       a_{i+k}        =?= b_k


 A6) If (m =?= v) is of the form

        ?M a_1 ... a_n =?= ?M b_1 ... b_k

     then we use first-order unification (if approximate() is true)
*/
bool type_context::process_assignment(expr const & m, expr const & v) {
    lean_trace(name({"type_context", "is_def_eq_detail"}),
               scope_trace_env scope(env(), *this);
               tout() << "process_assignment " << m << " := " << v << "\n";);
    buffer<expr> args;
    expr const & mvar = get_app_args(m, args);
    lean_assert(is_mvar(mvar));

    /* Check if constraint is of the form

             ?m a =?= f ?x

       and solve it using

             ?m =?= f
             a  =?= ?x

       This is an approximate solution, but it is useful when solving unification constraints for
       expressions such as

            a ∈ []

       where ∈ has type, and (a : A)

           def mem {α : Type u} {γ : Type u → Type v} [has_mem α γ] : α → γ α → Prop :=

       without the approximation above, Lean will produce the more general solution

           @mem A (fun a, list (?m A)) ?s a (@nil (list (?m A)))

       since no other constraint is restricting ?m, type class resolution is not fired,
       and an error is produced.

       The approximation above produces a solution that is equivalent to (?m := (fun x, x))
       However, any ?m can be used.
    */
    if (approximate() && args.size() == 1 && is_app(v) &&
        is_mvar(app_arg(v)) && !is_assigned(app_arg(v))) {
        expr arg = args[0];
        if (is_meta(arg))
            arg = instantiate_mvars(arg);
        expr fn  = app_fn(v);
        if (is_meta(fn))
            fn  = instantiate_mvars(fn);
        if (is_local_decl_ref(arg) && (is_local(fn) || is_constant(fn))) {
            return
                is_def_eq_core(mvar, app_fn(v)) &&
                is_def_eq_core(app_arg(v), args[0]);
        }
    }

    optional<metavar_decl> mvar_decl;
    if (!in_tmp_mode()) {
        mvar_decl = m_mctx.get_metavar_decl(mvar);
        if (!mvar_decl) return false;
    }
    buffer<expr> locals;
    bool use_fo     = false; /* if true, we use first-order unification */
    bool add_locals = true;  /* while true we copy args to locals */
    for (unsigned i = 0; i < args.size(); i++) {
        expr arg = args[i];
        /* try to instantiate */
        if (is_meta(arg))
            arg = instantiate_mvars(arg);
        arg = try_zeta(arg); /* unfold let-constant if needed. */
        args[i] = arg;
        if (!is_local_decl_ref(arg)) {
            /* m is of the form (?M ... t ...) where t is not a local constant. */
            if (approximate()) {
                /* workaround A5 */
                use_fo     = true;
                add_locals = false;
            } else {
                return false;
            }
        } else {
            if (std::any_of(locals.begin(), locals.end(),
                            [&](expr const & local) { return mlocal_name(local) == mlocal_name(arg); })) {
                /* m is of the form (?M ... l ... l ...) where l is a local constant. */
                if (approximate()) {
                    /* workaround A3 */
                    add_locals = false;
                } else {
                    return false;
                }
            }
            /* Make sure arg is not in the context of the metavariable mvar
               The code is slightly different for tmp mode because the metavariables
               do not store their local context. */
            if (in_tmp_mode()) {
                if (m_tmp_mvar_lctx.get_local_decl(arg)) {
                    /* m is of the form (?M@C ... l ...) where l is a local constant in C */
                    if (!approximate())
                        return false;
                }
            } else {
                if (mvar_decl->get_context().get_local_decl(arg)) {
                    /* m is of the form (?M@C ... l ...) where l is a local constant in C. */
                    if (!approximate())
                        return false;
                }
            }
        }
        if (add_locals)
            locals.push_back(arg);
    }

    expr new_v = instantiate_mvars(v); /* enforce A4 */

    if (approximate() && !locals.empty() && get_app_fn(new_v) == mvar) {
        /* A6 */
        use_fo = true;
    }

    if (use_fo) {
        /* Use first-order unification.
           Workaround A5. */
        buffer<expr> new_v_args;
        expr new_v_fn = get_app_args(new_v, new_v_args);
        if (new_v_args.empty()) {
            /*
                ?M a_1 ... a_k =?= t,  where t is not an application
            */
            return false;
        }
        expr new_mvar = mvar;
        unsigned i = 0;
        unsigned j = 0;
        if (args.size() > new_v_args.size()) {
            /*
               ?M a_1 ... a_i a_{i+1} ... a_{i+k} =?= f b_1 ... b_k

               reduces to

               ?M a_1 ... a_i =?= f
               a_{i+1}        =?= b_1
               ...
               a_{i+k}        =?= b_k
            */
            new_mvar = mk_app(mvar, args.size() - new_v_args.size(), args.data());
            i        = args.size() - new_v_args.size();
        } else if (args.size() < new_v_args.size()) {
            /*
               ?M a_1 ... a_k =?= f b_1 ... b_i b_{i+1} ... b_{i+k}

               reduces to

               ?M  =?= f b_1 ... b_i
               a_1 =?= b_{i+1}
               ...
               a_k =?= b_{i+k}
            */
            new_v_fn = mk_app(new_v_fn, new_v_args.size() - args.size(), new_v_args.data());
            j        = new_v_args.size() - args.size();
        } else {
            /*
               ?M a_1 ... a_k =?= f b_1 ... b_k

               reduces to
               ?M  =?= f
               a_1 =?= b_1
               ...
               a_k =?= b_k
            */
            lean_assert(new_v_args.size() == args.size());
        }
        /* We try to unify arguments before we try to unify the functions.
           This heuristic is consistently used in the is_def_eq procedure.
           See is_def_eq_args invocations.
           The motivation is the following: the universe constraints in
           the arguments propagate to the function. */
        for (; j < new_v_args.size(); i++, j++) {
            lean_assert(i < args.size());
            if (!is_def_eq_core(args[i], new_v_args[j]))
                return false;
        }
        if (!is_def_eq_core(new_mvar, new_v_fn))
            return false;
        lean_assert(i == args.size());
        lean_assert(j == new_v_args.size());
        return true;
    }

    if (optional<expr> new_new_v = check_assignment(locals, mvar, new_v))
        new_v = *new_new_v;
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

    /* check types */
    try {
        expr t1 = infer(mvar);
        expr t2 = infer(new_v);
        /* TODO(Leo): check whether using transparency_mode::All hurts performance.
           We use Semireducible to make sure we will not fail an unification step
                   ?m := t
           because we cannot establish that the types of ?m and t are definitionally equal
           due to the current transparency setting.
           This change is consistent with the general approach used in the rest of the code
           base where spurious typing errors due reducibility are avoided by using
           relaxed_is_def_eq. */
        relaxed_scope _(*this);
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

struct check_assignment_failed {};

struct check_assignment_fn : public replace_visitor {
    type_context &         m_ctx;
    buffer<expr> const &   m_locals;
    expr const &           m_mvar;
    optional<metavar_decl> m_mvar_decl;
    expr                   m_value;

    check_assignment_fn(type_context & ctx, buffer<expr> const & locals, expr const & mvar):
        m_ctx(ctx), m_locals(locals), m_mvar(mvar) {
        if (!m_ctx.in_tmp_mode()) {
            m_mvar_decl = m_ctx.m_mctx.get_metavar_decl(mvar);
            lean_assert(m_mvar_decl);
        }
    }

    expr visit_local(expr const & e) override {
        if (!is_local_decl_ref(e)) return e;

        bool in_ctx;
        if (m_ctx.in_tmp_mode()) {
            in_ctx = static_cast<bool>(m_ctx.m_tmp_mvar_lctx.get_local_decl(e));
        } else {
            in_ctx = static_cast<bool>(m_mvar_decl->get_context().get_local_decl(e));
        }

        if (!in_ctx) {
            if (auto decl = m_ctx.m_lctx.get_local_decl(e)) {
                if (auto v = decl->get_value()) {
                    /* expand let-decl value */
                    return visit(*v);
                }
            }
            if (std::all_of(m_locals.begin(), m_locals.end(), [&](expr const & a) {
                        return mlocal_name(a) != mlocal_name(e); })) {
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

    /** Return true iff ctx1 - delayed_locals is a subset of ctx2 */
    bool is_subset_of(local_context const & ctx1, local_context const & ctx2, buffer<name> const & delayed_locals) {
        return !ctx1.find_if([&](local_decl const & d1) { // NOLINT
                name const & n1 = d1.get_name();
                if (ctx2.get_local_decl(n1)) return false;
                bool is_delayed = std::find(delayed_locals.begin(), delayed_locals.end(), n1) != delayed_locals.end();
                return !is_delayed;
            });
    }

    expr visit_meta_core(expr const & e, buffer<name> const & delayed_locals) {
        if (!m_ctx.is_mvar(e)) return replace_visitor::visit_meta(e);
        if (auto v = m_ctx.get_assignment(e)) return visit(*v);

        if (m_mvar == e) {
            /* mvar occurs in m_value */
            lean_trace(name({"type_context", "is_def_eq_detail"}),
                       scope_trace_env scope(m_ctx.env(), m_ctx);
                       tout() << "failed to assign " << m_mvar << " :=\n" << m_value << "\n" <<
                       "value contains the metavariable " << m_mvar << "\n";);
            throw check_assignment_failed();
        }

        if (m_ctx.in_tmp_mode()) {
            /* Recall that in tmp_mode all metavariables have the same local context.
               So, we don't need to check anything.
               In regular mode, we need to check condition 4

               For every metavariable `?M'@C'` occurring in `t`, `C'` is a subset of `C` */
            return e;
        }

        /* unassigned metavariable in regular mode */

        optional<metavar_decl> e_decl = m_ctx.m_mctx.get_metavar_decl(e);
        if (!e_decl) {
            lean_trace(name({"type_context", "is_def_eq_detail"}),
                       scope_trace_env scope(m_ctx.env(), m_ctx);
                       tout() << "failed to assign " << m_mvar << " :=\n" << m_value << "\n" <<
                       "value contains \"foreign\" metavariable " << e << "\n";);
            throw check_assignment_failed();
        }

        local_context mvar_lctx = m_mvar_decl->get_context();
        local_context e_lctx    = e_decl->get_context();
        if (is_subset_of(e_lctx, mvar_lctx, delayed_locals))
            return e;

        if (m_ctx.approximate() && mvar_lctx.is_subset_of(e_lctx)) {
            expr e_type = e_decl->get_type();
            if (mvar_lctx.well_formed(e_type)) {
                /* Restrict context of the ?M' */
                /* Remark: we use copy_tag to make sure any position information
                   associated wtih mvar is inherited by the new meta-variable. */
                expr aux_mvar = copy_tag(e, m_ctx.mk_metavar_decl(mvar_lctx, e_type));
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
                       if (!m_ctx.approximate()) {
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

    expr visit_meta(expr const & e) override {
        buffer<name> tmp;
        return visit_meta_core(e, tmp);
    }

    expr visit_macro(expr const & e) override {
        if (is_delayed_abstraction(e)) {
            expr const & a = get_delayed_abstraction_expr(e);
            if (is_metavar(a)) {
                buffer<name> ns;
                buffer<expr> vs;
                get_delayed_abstraction_info(e, ns, vs);
                expr new_mvar = visit_meta_core(a, ns);
                for (expr & v : vs)
                    v = visit(v);
                return mk_delayed_abstraction(new_mvar, ns, vs);
            } else {
                return visit(push_delayed_abstraction(e));
            }
        } else {
            return replace_visitor::visit_macro(e);
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
optional<expr> type_context::check_assignment(buffer<expr> const & locals, expr const & mvar, expr v) {
    try {
        return some_expr(check_assignment_fn(*this, locals, mvar)(v));
    } catch (check_assignment_failed &) {
        return none_expr();
    }
}

bool type_context::is_def_eq_binding(expr e1, expr e2) {
    lean_assert(e1.kind() == e2.kind());
    lean_assert(is_binding(e1));
    expr_kind k = e1.kind();
    tmp_locals subst(*this);
    do {
        optional<expr> var_e1_type;
        if (binding_domain(e1) != binding_domain(e2)) {
            var_e1_type = instantiate_rev(binding_domain(e1), subst.size(), subst.data());
            expr var_e2_type = instantiate_rev(binding_domain(e2), subst.size(), subst.data());
            if (!is_def_eq_core(var_e2_type, *var_e1_type))
                return false;
        }
        if (!closed(binding_body(e1)) || !closed(binding_body(e2))) {
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

optional<expr> type_context::mk_class_instance_at(local_context const & lctx, expr const & type) {
    lean_assert(m_cache->m_instance_fingerprint == m_lctx.get_instance_fingerprint());

    type_context tmp_ctx(m_cache, m_mctx, lctx, m_transparency_mode);
    auto r = tmp_ctx.mk_class_instance(type);
    if (r) m_mctx = tmp_ctx.mctx();

    if (!lctx.get_instance_fingerprint() ||
        lctx.get_instance_fingerprint() != m_lctx.get_instance_fingerprint()) {
        /* The local instances in lctx may be different from the ones in m_lctx */
        flush_instance_cache();
        m_cache->m_instance_fingerprint = m_lctx.get_instance_fingerprint();
        m_cache->m_local_instances      = m_local_instances;
    }

    lean_assert(m_cache->m_instance_fingerprint == m_lctx.get_instance_fingerprint());
    return r;
}

/** \brief Create a nested type class instance of the given type, and assign it to metavariable \c m.
    Return true iff the instance was successfully created.
    \remark This method is used to resolve nested type class resolution problems. */
bool type_context::mk_nested_instance(expr const & m, expr const & m_type) {
    lean_assert(is_mvar(m));
    /* IMPORTANT: when mk_nested_instance is invoked we must make sure that
       we use the local context where 'm' was declared. */
    optional<expr> inst;
    if (in_tmp_mode()) {
        /* We don't need to create a temporary type context since all tmp metavars
           share the same local_context */
        inst = mk_class_instance(m_type);
    } else {
        optional<metavar_decl> mdecl = m_mctx.get_metavar_decl(m);
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

expr type_context::complete_instance(expr const & e) {
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
            if (is_mvar(new_arg) && pinfo.is_inst_implicit() && !is_assigned(new_arg)) {
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

bool type_context::is_def_eq_args(expr const & e1, expr const & e2) {
    lean_assert(is_app(e1) && is_app(e2));
    buffer<expr> args1, args2;
    expr const & fn = get_app_args(e1, args1);
    get_app_args(e2, args2);
    if (args1.size() != args2.size())
        return false;
    fun_info finfo = get_fun_info(*this, fn, args1.size());
    unsigned i = 0;
    for (param_info const & pinfo : finfo.get_params_info()) {
        if (pinfo.is_inst_implicit()) {
            args1[i] = complete_instance(args1[i]);
            args2[i] = complete_instance(args2[i]);
        }
        if (!is_def_eq_core(args1[i], args2[i]))
            return false;
        i++;
    }
    for (; i < args1.size(); i++) {
        if (!is_def_eq_core(args1[i], args2[i]))
            return false;
    }
    return true;
}

/** \brief Try to solve e1 := (lambda x : A, t) =?= e2 by eta-expanding e2.

    \remark eta-reduction is not a good alternative (even in a system without cumulativity like Lean).
    Example:
         (lambda x : A, f ?M) =?= f
    The lhs cannot be eta-reduced because ?M is a meta-variable. */
bool type_context::is_def_eq_eta(expr const & e1, expr const & e2) {
    if (is_lambda(e1) && !is_lambda(e2)) {
        expr e2_type = relaxed_whnf(infer(e2));
        if (is_pi(e2_type)) {
            // e2_type may not be a Pi because it is a stuck term.
            // We are ignoring this case and just failing.
            expr new_e2 = ::lean::mk_lambda(binding_name(e2_type), binding_domain(e2_type),
                                            mk_app(e2, Var(0)), binding_info(e2_type));
            scope s(*this);
            if (is_def_eq_core(e1, new_e2) && process_postponed(s)) {
                s.commit();
                return true;
            }
        }
    }
    return false;
}

bool type_context::is_def_eq_proof_irrel(expr const & e1, expr const & e2) {
    expr e1_type = infer(e1);
    if (is_prop(e1_type)) {
        expr e2_type = infer(e2);
        scope s(*this);
        if (is_def_eq_core(e1_type, e2_type) && process_postponed(s)) {
            s.commit();
            return true;
        }
    }
    return false;
}

/*
   Given `e` of the form `[delayed t {x_1 := v_1, ..., x_n := v_n}] a_1 ... a_k`

   If `t` is not a metavariable, then we just "push" the delayed
   abstraction.

   If `t` is a metavariable ?m, then we first substitute the `x_i`s
   that are not in the local context of ?m, and we obtain

         `delayed ?m {y_1 := w_1, ..., y_m := w_m}`

   where each `y_i` is in the local context of ?m.

   Then, we "revert" the y_i's. The revert method returns
   a metavariable application (?m1 z_1 .... z_s) where
   `z`s include `y`s and their dependencies. Recall that the
   revert operation has assigned
          ?m := ?m1 z_1 ... z_s

   Then, we replace the `y`s with `w`s in (?m1 z_1 .... z_s)
   and return

        ?m1 z_1' .... z_s' a_1 ... a_k
*/
expr type_context::elim_delayed_abstraction(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    lean_assert(is_delayed_abstraction(f));
    expr new_f = push_delayed_abstraction(f);
    if (new_f != f)
        return mk_app(new_f, args);
    buffer<name> hns;
    buffer<expr> vs;
    get_delayed_abstraction_info(f, hns, vs);
    lean_assert(hns.size() == vs.size());
    expr mvar = get_delayed_abstraction_expr(f);
    lean_assert(is_metavar(mvar));
    local_context lctx = m_mctx.get_metavar_decl(mvar)->get_context();
    buffer<expr> to_revert;
    buffer<expr> replacements;
    unsigned i = hns.size();
    while (i > 0) {
        --i;
        name const & hn = hns[i];
        expr const & v  = vs[i];
        if (optional<local_decl> h = lctx.get_local_decl(hn)) {
            to_revert.push_back(h->mk_ref());
            replacements.push_back(v);
        } else {
            // replace hn with v at vs[0] ... vs[i-1]
            for (unsigned j = 0; j < i; j++) {
                vs[j] = instantiate(abstract_local(vs[j], hn), v);
            }
        }
    }
    expr new_fn;
    if (!to_revert.empty()) {
        std::reverse(to_revert.begin(), to_revert.end());
        std::reverse(replacements.begin(), replacements.end());
        buffer<expr> saved_to_revert; saved_to_revert.append(to_revert);
        expr new_meta = revert(to_revert, mvar);
        lean_assert(saved_to_revert.size() == replacements.size());
        new_fn        = replace_locals(new_meta, saved_to_revert, replacements);
    } else {
        new_fn = mvar;
    }
    expr r = mk_app(new_fn, args);
    lean_trace(name({"type_context", "is_def_eq_detail"}),
               scope_trace_env scope(env(), *this);
               tout() << "eliminated delayed abstraction:\n"
               << e << "\n====>\n" << r << "\n";);
    return r;
}

lbool type_context::quick_is_def_eq(expr const & e1, expr const & e2) {
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

    if (is_mvar(f1)) {
        if (is_assigned(f1)) {
            return to_lbool(is_def_eq_core(instantiate_mvars(e1), e2));
        } else if (!in_tmp_mode() && is_delayed_abstraction(f2)) {
            return to_lbool(is_def_eq_core(e1, elim_delayed_abstraction(e2)));
        } else if (!is_mvar(f2)) {
            return to_lbool(process_assignment(e1, e2));
        } else if (is_assigned(f2)) {
            return to_lbool(is_def_eq_core(e1, instantiate_mvars(e2)));
        } else if (in_tmp_mode()) {
            return to_lbool(process_assignment(e1, e2));
        } else {
            optional<metavar_decl> m1_decl = m_mctx.get_metavar_decl(f1);
            optional<metavar_decl> m2_decl = m_mctx.get_metavar_decl(f2);
            if (m1_decl && m2_decl) {
                if (m2_decl->get_context().is_subset_of(m1_decl->get_context())) {
                    if (!is_app(e1) || is_app(e2)) {
                        return to_lbool(process_assignment(e1, e2));
                    } else if (m1_decl->get_context().is_subset_of(m2_decl->get_context())) {
                        lean_assert(is_app(e1) && !is_app(e2));
                        /* It is easier to solve the assignment
                                 ?m2 := ?m1 a_1 ... a_n
                           than
                                 ?m1 a_1 ... a_n := ?m2
                           Reason: the first one is precise. For example,
                           consider the following constraint:

                                 ?m1 ?m =?= ?m2
                        */
                        return to_lbool(process_assignment(e2, e1));
                    } else {
                        return to_lbool(process_assignment(e1, e2));
                    }
                } else {
                    return to_lbool(process_assignment(e2, e1));
                }
            } else {
                return l_false;
            }
        }
    }

    if (is_mvar(f2)) {
        if (is_assigned(f2)) {
            return to_lbool(is_def_eq_core(e1, instantiate_mvars(e2)));
        } else if (!in_tmp_mode() && is_delayed_abstraction(f1)) {
            return to_lbool(is_def_eq_core(elim_delayed_abstraction(e1), e2));
        } else {
            return to_lbool(process_assignment(e2, e1));
        }
    }

    if (!in_tmp_mode()) {
        if (is_delayed_abstraction(f1))
            return to_lbool(is_def_eq_core(elim_delayed_abstraction(e1), e2));
        if (is_delayed_abstraction(f2))
            return to_lbool(is_def_eq_core(e1, elim_delayed_abstraction(e2)));
    }

    if (e1.kind() == e2.kind()) {
        switch (e1.kind()) {
        case expr_kind::Lambda: case expr_kind::Pi:
            return to_lbool(is_def_eq_binding(e1, e2));
        case expr_kind::Sort:
            return to_lbool(is_def_eq(sort_level(e1), sort_level(e2)));
        case expr_kind::Meta:     case expr_kind::Var:
        case expr_kind::Local:    case expr_kind::App:
        case expr_kind::Constant: case expr_kind::Macro:
        case expr_kind::Let:
            // We do not handle these cases in this method.
            break;
        }
    }
    return l_undef; // This is not an "easy case"
}

/* We say a reduction is productive iff the result is not a recursor application */
bool type_context::is_productive(expr const & e) {
    /* TODO(Leo): make this more general.
       Right now we consider the following cases to be non-productive
       1)  (C.rec ...)   where rec is rec/rec_on/cases_on/brec_on
       2)  (prod.fst A B (C.rec ...) ...)  where rec is rec/rec_on/cases_on/brec_on

       Second case is a byproduct of the recursive equation compiler.
    */
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return true;
    name const & n = const_name(f);
    if (n == get_pprod_fst_name()) {
        /* We use prod.fst when compiling recursive equations and brec_on.
           So, we should check whether the main argument of the projection
           is productive */
        buffer<expr> args;
        get_app_args(e, args);
        if (args.size() < 3)
            return false;
        expr const & major = args[2];
        return is_productive(major);
    } else {
        return !m_cache->is_aux_recursor(n) && !inductive::is_elim_rule(env(), n);
    }
}

expr type_context::reduce_if_productive(expr const & t) {
    if (auto r = unfold_definition(t)) {
        expr new_t = whnf_core(*r);
        if (is_productive(new_t)) {
            return new_t;
        }
    }
    return t;
}

static bool same_head_symbol(expr const & t, expr const & s) {
    expr const & f_t = get_app_fn(t);
    expr const & f_s = get_app_fn(s);
    return is_constant(f_t) && is_constant(f_s) && const_name(f_t) == const_name(f_s);
}

/* Apply unification hints and lazy delta-reduction */
lbool type_context::is_def_eq_lazy_delta(expr & t, expr & s) {
    while (true) {
        if (try_unification_hints(t, s))
            return l_true;
        lbool r = try_nat_offset_cnstrs(t, s);
        if (r != l_undef) return r;

        optional<declaration> d_t = is_delta(t);
        optional<declaration> d_s = is_delta(s);
        if (!d_t && !d_s) {
            /* none of them can be delta-reduced */
            return l_undef;
        } else if (d_t && !d_s) {
            /* only t_n can be delta reduced */
            lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold left: " << d_t->get_name() << "\n";);
            t = whnf_core(*unfold_definition(t));
        } else if (!d_t && d_s) {
            /* only s_n can be delta reduced */
            lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold right: " << d_s->get_name() << "\n";);
            s = whnf_core(*unfold_definition(s));
        } else {
            /* both t and s can be delta reduced */
            if (is_eqp(*d_t, *d_s)) {
                /* Same constant */
                if (is_app(t) && is_app(s)) {
                    bool has_postponed = !m_postponed.empty();
                    if (!is_cached_failure(t, s)) {
                        /* Heuristic: try so solve (f a =?= f b), by solving (a =?= b) */
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
                    lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold left&right: " << d_t->get_name() << "\n";);
                    t = whnf_core(*unfold_definition(t));
                    s = whnf_core(*unfold_definition(s));
                } else if (!is_app(t) && !is_app(s)) {
                    return to_lbool(is_def_eq(const_levels(t), const_levels(s)));
                } else {
                    return l_false;
                }
            } else {
                bool progress = false;
                if (m_transparency_mode == transparency_mode::Semireducible ||
                    m_transparency_mode == transparency_mode::All) {
                    /* Consider the following two cases

                       If t is reducible and s is not ==> reduce t
                       If s is reducible and t is not ==> reduce s

                       Remark: this can only happen if transparency_mode
                       is Semireducible or All
                    */
                    auto rd_t = is_transparent(transparency_mode::Reducible, d_t->get_name());
                    auto rd_s = is_transparent(transparency_mode::Reducible, d_s->get_name());
                    if (rd_t && !rd_s) {
                        progress = true;
                        lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold (reducible) left: " << d_t->get_name() << "\n";);
                        t = whnf_core(*unfold_definition(t));
                    } else if (!rd_t && rd_s) {
                        progress = true;
                        lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold (reducible) right: " << d_s->get_name() << "\n";);
                        s = whnf_core(*unfold_definition(s));
                    }
                }
                /* If we haven't reduced t nor s, and they do not contain metavariables,
                   then we try to use the definitional height to decide which one we will unfold
                   (i.e., we mimic the behavior of the kernel type checker. */
                if (!progress && !has_expr_metavar(t) && !has_expr_metavar(s)) {
                    int c = compare(d_t->get_hints(), d_s->get_hints());
                    if (c < 0) {
                        progress = true;
                        t        = whnf_core(*unfold_definition(t));
                    } else if (c > 0) {
                        progress = true;
                        s        = whnf_core(*unfold_definition(s));
                    }
                }
                /* If we haven't reduced t nor s, then we reduce both IF the reduction is productive.
                   That is, the result of the reduction is not a recursor application. */
                if (!progress) {
                    expr new_t = reduce_if_productive(t);
                    if (!is_eqp(new_t, t) && same_head_symbol(new_t, s)) {
                        lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold left (match right): " << d_t->get_name() << "\n";);
                        t = new_t;
                    } else {
                        expr new_s = reduce_if_productive(s);
                        if (!is_eqp(new_s, s) && same_head_symbol(t, new_s)) {
                            lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold right (match left): " << d_s->get_name() << "\n";);
                            s = new_s;
                        } else if (is_eqp(new_t, t) && is_eqp(new_s, s)) {
                            return l_undef;
                        } else {
                            if (!is_eqp(new_t, t)) {
                                lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold productive left: " << d_t->get_name() << "\n";);
                            }
                            if (!is_eqp(new_s, s)) {
                                lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold productive right: " << d_s->get_name() << "\n";);
                            }
                            t = new_t;
                            s = new_s;
                        }
                    }
                }
            }
        }
        r = quick_is_def_eq(t, s);
        if (r != l_undef) return r;
        lean_trace(name({"type_context", "is_def_eq_detail"}),
                   scope_trace_env scope(env(), *this);
                   tout() << "after delta: " << t << " =?= " << s << "\n";);
    }
}

expr type_context::try_to_unstuck_using_complete_instance(expr const & e) {
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
    if (optional<unsigned> major_idx = inductive::get_elim_major_idx(env(), const_name(fn))) {
        /* This is an optimization for recursor/eliminator applications.
           In this case, we only need to instantiate metavariables in the major premise */
        if (*major_idx < args.size()) {
            expr major     = args[*major_idx];
            expr new_major = complete_instance(major);
            if (new_major != major) {
                args[*major_idx] = new_major;
                return mk_app(fn, args);
            }
        }
        return e;
    }
    /* For projections and other builtin constants that compute in the kernel, we
       do not have any special optimization, we just invoke complete_instance */
    return complete_instance(e);
}

bool type_context::on_is_def_eq_failure(expr const & e1, expr const & e2) {
    lean_trace(name({"type_context", "is_def_eq_detail"}),
               scope_trace_env scope(env(), *this);
               tout() << "on failure: " << e1 << " =?= " << e2 << "\n";);

    if (is_stuck(e1)) {
        expr new_e1 = try_to_unstuck_using_complete_instance(e1);
        if (new_e1 != e1) {
            lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "synthesized instances on right\n";);
            return is_def_eq_core(new_e1, e2);
        }
    }

    if (is_stuck(e2)) {
        expr new_e2 = try_to_unstuck_using_complete_instance(e2);
        if (new_e2 != e2) {
            lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "synthesized instances on left\n";);
            return is_def_eq_core(e1, new_e2);
        }
    }

    return false;
}

/* If e is a (small) numeral, then return it. Otherwise return none. */
optional<unsigned> type_context::to_small_num(expr const & e) {
    unsigned r;
    if (is_constant(e, get_nat_zero_name())) {
        r = 0;
    } else if (is_app_of(e, get_zero_name(), 2) && is_constant(app_arg(e), get_nat_has_zero_name())) {
        r = 0;
    } else if (is_app_of(e, get_one_name(), 2) && is_constant(app_arg(e), get_nat_has_one_name())) {
        r = 1;
    } else if (auto a = is_bit0(e)) {
        if (auto r1 = to_small_num(*a))
            r = 2 * *r1;
        else
            return optional<unsigned>();
    } else if (auto a = is_bit1(e)) {
        if (auto r1 = to_small_num(*a))
            r = 2 * *r1 + 1;
        else
            return optional<unsigned>();
    } else if (is_app_of(e, get_nat_succ_name(), 1)) {
        if (auto r1 = to_small_num(app_arg(e)))
            r = *r1 + 1;
        else
            return optional<unsigned>();
    } else {
        return optional<unsigned>();
    }
    if (r > m_cache->m_nat_offset_cnstr_threshold)
        return optional<unsigned>();
    return optional<unsigned>(r);
}

/* If \c t is of the form (s + k) where k is a numeral, then return k. Otherwise, return none. */
optional<unsigned> type_context::is_offset_term (expr const & t) {
    if (!is_app_of(t, get_add_name(), 4)) return optional<unsigned>();
    expr const & k = app_arg(t);
    return to_small_num(k);
}

/* Return true iff t is of the form (t' + k) where k is a numeral */
static expr get_offset_term(expr const & t) {
    lean_assert(is_app_of(t, get_add_name(), 4));
    return app_arg(app_fn(t));
}

/* Return true iff t is of the form (@add _ nat_has_add a b)
   \pre is_offset_term(t) */
static bool uses_nat_has_add_instance(expr const & t) {
    lean_assert(is_app_of(t, get_add_name(), 4));
    return is_constant(app_arg(app_fn(app_fn(t))), get_nat_has_add_name());
}

/* Solve unification constraints of the form

       t' + k_1 =?= s' + k_2

   where k_1 and k_2 are numerals, and type is nat */
lbool type_context::try_offset_eq_offset(expr const & t, expr const & s) {
    optional<unsigned> k1 = is_offset_term(t);
    if (!k1) return l_undef;
    optional<unsigned> k2 = is_offset_term(s);
    if (!k2) return l_undef;

    if (!uses_nat_has_add_instance(t) || !uses_nat_has_add_instance(s))
        return l_undef;

    if (*k1 == *k2) {
        return to_lbool(is_def_eq_core(get_offset_term(t), get_offset_term(s)));
    } else if (*k1 > *k2) {
        return to_lbool(is_def_eq_core(mk_app(app_fn(app_fn(t)), get_offset_term(t), to_nat_expr(mpz(*k1 - *k2))),
                                       get_offset_term(s)));
    } else {
        lean_assert(*k2 > *k1);
        return to_lbool(is_def_eq_core(get_offset_term(t),
                                       mk_app(app_fn(app_fn(s)), get_offset_term(s), to_nat_expr(mpz(*k2 - *k1)))));
    }
}

/* Solve unification constraints of the form

       t' + k_1 =?= k_2

   where k_1 and k_2 are numerals, and type is nat */
lbool type_context::try_offset_eq_numeral(expr const & t, expr const & s) {
    optional<unsigned> k1 = is_offset_term(t);
    if (!k1) return l_undef;
    optional<unsigned> k2 = to_small_num(s);
    if (!k2) return l_undef;

    if (!uses_nat_has_add_instance(t))
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

   where k_1 and k_2 are numerals, and type is nat */
lbool type_context::try_numeral_eq_numeral(expr const & t, expr const & s) {
    optional<unsigned> k1 = to_small_num(t);
    if (!k1) return l_undef;
    optional<unsigned> k2 = to_small_num(s);
    if (!k2) return l_undef;

    if (is_nat_type(whnf(infer(t))))
        return l_undef;

    return to_lbool(*k1 == *k2);
}

/* Solve offset constraints. See discussion at issue #1226 */
lbool type_context::try_nat_offset_cnstrs(expr const & t, expr const & s) {
    /* We should not use this feature when transparency_mode is none.
       See issue #1295 */
    if (m_transparency_mode == transparency_mode::None) return l_undef;
    lbool r;
    r = try_offset_eq_offset(t, s);
    if (r != l_undef) return r;
    r = try_offset_eq_numeral(t, s);
    if (r != l_undef) return r;
    r = try_offset_eq_numeral(s, t);
    if (r != l_undef) return r;
    return try_numeral_eq_numeral(t, s);
}

bool type_context::is_def_eq_core_core(expr const & t, expr const & s) {
    lbool r = quick_is_def_eq(t, s);
    if (r != l_undef) return r == l_true;

    flet<unsigned> inc_depth(m_is_def_eq_depth, m_is_def_eq_depth+1);
    lean_trace(name({"type_context", "is_def_eq_detail"}),
               scope_trace_env scope(env(), *this);
               tout() << "[" << m_is_def_eq_depth << "]: " << t << " =?= " << s << "\n";);

    expr t_n = whnf_core(t);
    expr s_n = whnf_core(s);

    if (!is_eqp(t_n, t) || !is_eqp(s_n, s)) {
        lean_trace(name({"type_context", "is_def_eq_detail"}),
                   scope_trace_env scope(env(), *this);
                   tout() << "after whnf_core: " << t_n << " =?= " << s_n << "\n";);
        r = quick_is_def_eq(t_n, s_n);
        if (r != l_undef) return r == l_true;
    }

    check_system("is_def_eq");

    r = is_def_eq_lazy_delta(t_n, s_n);
    if (r != l_undef) return r == l_true;

    if (is_constant(t_n) && is_constant(s_n) && const_name(t_n) == const_name(s_n)) {
        return is_def_eq(const_levels(t_n), const_levels(s_n));
    }

    if (is_local(t_n) && is_local(s_n) && mlocal_name(t_n) == mlocal_name(s_n))
        return true;

    if (is_app(t_n) && is_app(s_n)) {
        scope s(*this);
        if (is_def_eq_core(get_app_fn(t_n), get_app_fn(s_n)) &&
            is_def_eq_args(t_n, s_n) &&
            process_postponed(s)) {
            s.commit();
            return true;
        }
    }

    if (is_def_eq_eta(t_n, s_n))
        return true;
    if (is_def_eq_eta(s_n, t_n))
        return true;
    if (is_def_eq_proof_irrel(t_n, s_n))
        return true;
    return on_is_def_eq_failure(t_n, s_n);
}

bool type_context::is_def_eq_core(expr const & t, expr const & s) {
    unsigned postponed_sz = m_postponed.size();
    bool r = is_def_eq_core_core(t, s);
    if (r && postponed_sz == m_postponed.size()) {
        cache_equiv(t, s);
    }
    return r;
}

bool type_context::is_def_eq(expr const & t, expr const & s) {
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

bool type_context::relaxed_is_def_eq(expr const & e1, expr const & e2) {
    relaxed_scope scope(*this);
    return is_def_eq(e1, e2);
}

class unification_hint_fn {
    type_context &           m_owner;
    unification_hint const & m_hint;
    buffer<optional<expr>>   m_assignment;

    bool match(expr const & pattern, expr const & e) {
        unsigned idx;
        switch (pattern.kind()) {
        case expr_kind::Var:
            idx = var_idx(pattern);
            if (!m_assignment[idx]) {
                m_assignment[idx] = some_expr(e);
                return true;
            } else {
                return m_owner.is_def_eq(*m_assignment[idx], e);
            }
        case expr_kind::Constant:
            return
                is_constant(e) &&
                const_name(pattern) == const_name(e) &&
                m_owner.is_def_eq(const_levels(pattern), const_levels(e));
        case expr_kind::Sort:
            return is_sort(e) && m_owner.is_def_eq(sort_level(pattern), sort_level(e));
        case expr_kind::Pi:    case expr_kind::Lambda:
        case expr_kind::Macro: case expr_kind::Let:
            // Remark: we do not traverse inside of binders.
            return pattern == e;
        case expr_kind::App:
            return
                is_app(e) &&
                match(app_fn(pattern), app_fn(e)) &&
                match(app_arg(pattern), app_arg(e));
        case expr_kind::Local: case expr_kind::Meta:
            lean_unreachable();
        }
        lean_unreachable();
    }

public:
    unification_hint_fn(type_context & o, unification_hint const & hint):
        m_owner(o), m_hint(hint) {
        m_assignment.resize(m_hint.get_num_vars());
    }

    bool operator()(expr const & lhs, expr const & rhs) {
        if (!match(m_hint.get_lhs(), lhs)) {
            lean_trace(name({"type_context", "unification_hint"}), tout() << "LHS does not match\n";);
            return false;
        } else if (!match(m_hint.get_rhs(), rhs)) {
            lean_trace(name({"type_context", "unification_hint"}), tout() << "RHS does not match\n";);
            return false;
        } else {
            auto instantiate_assignment_fn = [&](expr const & e, unsigned offset) {
                if (is_var(e)) {
                    unsigned idx = var_idx(e) + offset;
                    if (idx < m_assignment.size() && m_assignment[idx])
                        return m_assignment[idx];
                }
                return none_expr();
            };
            buffer<expr_pair> constraints;
            to_buffer(m_hint.get_constraints(), constraints);
            for (expr_pair const & p : constraints) {
                expr new_lhs = replace(p.first, instantiate_assignment_fn);
                expr new_rhs = replace(p.second, instantiate_assignment_fn);
                bool success = m_owner.is_def_eq(new_lhs, new_rhs);
                lean_trace(name({"type_context", "unification_hint"}),
                           scope_trace_env scope(m_owner.env(), m_owner);
                           tout() << new_lhs << " =?= " << new_rhs << "..."
                           << (success ? "success" : "failed") << "\n";);
                if (!success) return false;
            }
            lean_trace(name({"type_context", "unification_hint"}),
                       tout() << "hint successfully applied\n";);
            return true;
        }
    }
};

bool type_context::try_unification_hint(unification_hint const & hint, expr const & e1, expr const & e2) {
    scope s(*this);
    if (unification_hint_fn(*this, hint)(e1, e2) && process_postponed(s)) {
        s.commit();
        return true;
    } else {
        return false;
    }
}

bool type_context::try_unification_hints(expr const & e1, expr const & e2) {
    expr e1_fn = get_app_fn(e1);
    expr e2_fn = get_app_fn(e2);
    if (is_constant(e1_fn) && is_constant(e2_fn)) {
        buffer<unification_hint> hints;
        get_unification_hints(env(), const_name(e1_fn), const_name(e2_fn), hints);
        for (unification_hint const & hint : hints) {
            lean_trace(name({"type_context", "unification_hint"}),
                       scope_trace_env scope(env(), *this);
                       tout() << e1 << " =?= " << e2
                       << ", pattern: " << hint.get_lhs() << " =?= " << hint.get_rhs() << "\n";);
            if (try_unification_hint(hint, e1, e2) ||
                try_unification_hint(hint, e2, e1)) {
                return true;
            }
        }
    }
    return false;
}

/* -------------
   Type classes
   ------------- */

/** \brief If the constant \c e is a class, return its name */
optional<name> type_context::constant_is_class(expr const & e) {
    name const & cls_name = const_name(e);
    if (lean::is_class(env(), cls_name)) {
        return optional<name>(cls_name);
    } else {
        return optional<name>();
    }
}

optional<name> type_context::is_full_class(expr type) {
    type = whnf(type);
    if (is_pi(type)) {
        tmp_locals locals(*this);
        return is_full_class(::lean::instantiate(binding_body(type), locals.push_local_from_binding(type)));
    } else {
        expr f = get_app_fn(type);
        if (!is_constant(f))
            return optional<name>();
        return constant_is_class(f);
    }
}

/** \brief Partial/Quick test for is_class. Result
    l_true:   \c type is a class, and the name of the class is stored in \c result.
    l_false:  \c type is not a class.
    l_undef:  procedure did not establish whether \c type is a class or not. */
lbool type_context::is_quick_class(expr const & type, name & result) {
    expr const * it = &type;
    while (true) {
        switch (it->kind()) {
        case expr_kind::Var:  case expr_kind::Sort:   case expr_kind::Local:
        case expr_kind::Meta: case expr_kind::Lambda: case expr_kind::Let:
            return l_false;
        case expr_kind::Macro:
            return l_undef;
        case expr_kind::Constant:
            if (auto r = constant_is_class(*it)) {
                result = *r;
                return l_true;
            } else if (!is_transparent(const_name(*it))) {
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
                } else if (!is_transparent(const_name(f))) {
                    return l_false;
                } else {
                    return l_undef;
                }
            } else if (is_lambda(f) || is_macro(f)) {
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
optional<name> type_context::is_class(expr const & type) {
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
        list<name>         m_instances;
        state              m_state;
    };

    type_context &        m_ctx;
    expr                  m_main_mvar;
    state                 m_state;    // active state
    buffer<choice>        m_choices;
    bool                  m_displayed_trace_header;
    transparency_mode     m_old_transparency_mode;

    instance_synthesizer(type_context & ctx):
        m_ctx(ctx),
        m_displayed_trace_header(false),
        m_old_transparency_mode(m_ctx.m_transparency_mode) {
        lean_assert(m_ctx.in_tmp_mode());
        m_ctx.m_transparency_mode = transparency_mode::Reducible;
    }

    ~instance_synthesizer() {
        for (unsigned i = 0; i < m_choices.size(); i++) {
            m_ctx.pop_scope();
        }
        m_ctx.m_transparency_mode = m_old_transparency_mode;
    }

    environment const & env() const { return m_ctx.env(); }

    void push_scope() {
        lean_trace(name({"type_context", "tmp_vars"}), tout() << "push_scope, trail_sz: " << m_ctx.m_tmp_trail.size() << "\n";);
        m_ctx.push_scope();
    }

    void pop_scope() {
        lean_trace(name({"type_context", "tmp_vars"}), tout() << "pop_scope, trail_sz: " << m_ctx.m_tmp_trail.size() << "\n";);
        m_ctx.pop_scope();
    }

    bool is_done() const {
        return empty(m_state.m_stack);
    }

    void trace(unsigned depth, expr const & mvar, expr const & mvar_type, expr const & r) {
        auto out = tout();
        if (!m_displayed_trace_header && m_choices.size() == 1) {
            out << tclass("class_instances");
            if (m_ctx.m_cache->m_pip) {
                if (auto fname = m_ctx.m_cache->m_pip->get_file_name()) {
                    out << fname << ":";
                }
                if (m_ctx.m_cache->m_ci_pos)
                    out << m_ctx.m_cache->m_ci_pos->first << ":" << m_ctx.m_cache->m_ci_pos->second << ":";
            }
            out << " class-instance resolution trace" << endl;
            m_displayed_trace_header = true;
        }
        out << tclass("class_instances") << "(" << depth << ") ";
        out << mvar << " : " << m_ctx.instantiate_mvars(mvar_type) << " := " << r << endl;
    }

    /* Try to synthesize e.m_mvar using instance inst : inst_type. */
    bool try_instance(stack_entry const & e, expr const & inst, expr const & inst_type) {
        try {
            type_context::tmp_locals locals(m_ctx);
            expr const & mvar = e.m_mvar;
            expr mvar_type    = m_ctx.infer(mvar);
            while (true) {
                mvar_type = m_ctx.relaxed_whnf(mvar_type);
                if (!is_pi(mvar_type))
                    break;
                expr local  = locals.push_local_from_binding(mvar_type);
                mvar_type   = instantiate(binding_body(mvar_type), local);
            }
            expr type  = inst_type;
            expr r     = inst;
            buffer<expr> new_inst_mvars;
            while (true) {
                type = m_ctx.relaxed_whnf(type);
                if (!is_pi(type))
                    break;
                expr new_mvar = m_ctx.mk_tmp_mvar(locals.mk_pi(binding_domain(type)));
                if (binding_info(type).is_inst_implicit()) {
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
            unsigned num_univ_ps = decl->get_num_univ_params();
            for (unsigned i = 0; i < num_univ_ps; i++)
                ls_buffer.push_back(m_ctx.mk_tmp_univ_mvar());
            levels ls = to_list(ls_buffer.begin(), ls_buffer.end());
            expr inst_cnst = mk_constant(inst_name, ls);
            expr inst_type = instantiate_type_univ_params(*decl, ls);
            return try_instance(e, inst_cnst, inst_type);
        } else {
            return false;
        }
    }

    list<expr> get_local_instances(name const & cname) {
        buffer<expr> selected;
        for (pair<name, expr> const & p : m_ctx.m_local_instances) {
            if (p.first == cname)
                selected.push_back(p.second);
        }
        return to_list(selected);
    }

    bool mk_choice_point(expr const & mvar) {
        lean_assert(is_metavar(mvar));
        if (m_choices.size() > m_ctx.m_cache->m_ci_max_depth) {
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
        expr mvar_type       = m_ctx.instantiate_mvars(mlocal_type(mvar));
        m_choices.push_back(choice());
        push_scope();
        choice & r = m_choices.back();
        auto cname = m_ctx.is_class(mvar_type);
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

    bool process_next_alt_core(stack_entry const & e, list<name> & inst_names) {
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
        list<name> insts = cs.back().m_instances;
        if (process_next_alt_core(e, insts)) {
            cs.back().m_instances = insts;
            return true;
        }
        cs.back().m_instances = list<name>();
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

    void cache_result(expr const & type, optional<expr> const & inst) {
        m_ctx.m_cache->m_instance_cache.insert(mk_pair(type, inst));
    }

    optional<expr> ensure_no_meta(optional<expr> r) {
        while (true) {
            if (!r) {
                cache_result(m_ctx.infer(m_main_mvar), r);
                return none_expr();
            }
            if (!has_expr_metavar(*r)) {
                if (has_idx_metavar(*r)) {
                    /* r has universe metavariables.
                       Try to instantiate them. */
                    r = m_ctx.instantiate_mvars(*r);
                }
                if (!has_idx_metavar(*r)) {
                    /* We only cache the result if it does not contain universe tmp metavars. */
                    cache_result(m_ctx.infer(m_main_mvar), some_expr(m_ctx.instantiate_mvars(*r)));
                    return r;
                }
            }
            lean_trace("class_instances",
                       tout() << "trying next solution, current solution has metavars\n" << *r << "\n";);
            r = next_solution();
        }
    }

    optional<expr> mk_class_instance_core(expr const & type) {
        /* We do not cache results when multiple instances have to be generated. */
        auto it = m_ctx.m_cache->m_instance_cache.find(type);
        if (it != m_ctx.m_cache->m_instance_cache.end()) {
            /* instance/failure is already cached */
            lean_trace("class_instances",
                       if (it->second)
                           tout() << "cached instance for " << type << "\n" << *(it->second) << "\n";
                       else
                           tout() << "cached failure for " << type << "\n";);
            return it->second;
        }
        m_state          = state();
        m_main_mvar      = m_ctx.mk_tmp_mvar(type);
        m_state.m_stack  = to_list(stack_entry(m_main_mvar, 0));
        auto r = search();
        return ensure_no_meta(r);
    }

    optional<expr> operator()(expr const & type) {
        lean_trace_init_bool("class_instances", get_pp_purify_metavars_name(), false);
        lean_trace_init_bool("class_instances", get_pp_implicit_name(), true);
        auto r = mk_class_instance_core(type);
        if (r) {
            for (unsigned i = 0; i < m_choices.size(); i++) {
                m_ctx.commit_scope();
            }
            m_choices.clear();
        }
        return r;
    }
};

optional<expr> type_context::mk_class_instance(expr const & type) {
    if (in_tmp_mode()) {
        return instance_synthesizer(*this)(type);
    } else {
        tmp_mode_scope s(*this);
        return instance_synthesizer(*this)(type);
    }
}

optional<expr> type_context::mk_subsingleton_instance(expr const & type) {
    auto it = m_cache->m_subsingleton_cache.find(type);
    if (it != m_cache->m_subsingleton_cache.end())
        return it->second;
    expr Type  = whnf(infer(type));
    if (!is_sort(Type)) {
        m_cache->m_subsingleton_cache.insert(mk_pair(type, none_expr()));
        return none_expr();
    }
    level lvl    = sort_level(Type);
    expr subsingleton =mk_app(mk_constant(get_subsingleton_name(), {lvl}), type);
    auto r = mk_class_instance(subsingleton);
    m_cache->m_subsingleton_cache.insert(mk_pair(type, r));
    return r;
}

/* -------------
   Auxiliary
   ------------- */

expr type_context::eta_expand(expr const & e) {
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

tmp_type_context::tmp_type_context(type_context & tctx, unsigned num_umeta, unsigned num_emeta): m_tctx(tctx) {
    m_tmp_uassignment.resize(num_umeta, none_level());
    m_tmp_eassignment.resize(num_emeta, none_expr());
}

bool tmp_type_context::is_def_eq(expr const & e1, expr const & e2) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.is_def_eq(e1, e2);
}

expr tmp_type_context::infer(expr const & e) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.infer(e);
}

expr tmp_type_context::whnf(expr const & e) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.whnf(e);
}

level tmp_type_context::mk_tmp_univ_mvar() {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.mk_tmp_univ_mvar();
}

expr tmp_type_context::mk_tmp_mvar(expr const & type) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.mk_tmp_mvar(type);
}

bool tmp_type_context::is_uassigned(unsigned i) const {
    lean_assert(i < m_tmp_uassignment.size());
    return static_cast<bool>(m_tmp_uassignment[i]);
}

bool tmp_type_context::is_eassigned(unsigned i) const {
    lean_assert(i < m_tmp_eassignment.size());
    return static_cast<bool>(m_tmp_eassignment[i]);
}

void tmp_type_context::clear_eassignment() {
    m_tmp_eassignment.clear();
}

expr tmp_type_context::instantiate_mvars(expr const & e) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.instantiate_mvars(e);
}

void tmp_type_context::assign(expr const & m, expr const & v) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    m_tctx.assign(m, v);
}

expr tmp_type_context::mk_lambda(buffer<expr> const & locals, expr const & e) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.mk_lambda(locals, e);
}

expr tmp_type_context::mk_pi(buffer<expr> const & locals, expr const & e) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.mk_pi(locals, e);
}

expr tmp_type_context::mk_lambda(expr const & local, expr const & e) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.mk_lambda(local, e);
}

expr tmp_type_context::mk_pi(expr const & local, expr const & e) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.mk_pi(local, e);
}

expr tmp_type_context::mk_lambda(std::initializer_list<expr> const & locals, expr const & e) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.mk_lambda(locals, e);
}

expr tmp_type_context::mk_pi(std::initializer_list<expr> const & locals, expr const & e) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.mk_pi(locals, e);
}

bool tmp_type_context::is_prop(expr const & e) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.is_prop(e);
}

/** \brief Helper class for pretty printing terms that contain local_decl_ref's and metavar_decl_ref's */
class pp_ctx {
    type_context m_ctx;
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
mk_pp_ctx(type_context const & ctx) {
    return mk_pp_ctx(ctx.env(), ctx.get_options(), ctx.mctx(), ctx.lctx());
}

void initialize_type_context() {
    register_trace_class("class_instances");
    register_trace_class(name({"type_context", "unification_hint"}));
    register_trace_class(name({"type_context", "is_def_eq"}));
    register_trace_class(name({"type_context", "is_def_eq_detail"}));
    register_trace_class(name({"type_context", "univ_is_def_eq"}));
    register_trace_class(name({"type_context", "univ_is_def_eq_detail"}));
    register_trace_class(name({"type_context", "tmp_vars"}));
    register_trace_class("type_context_cache");
    g_class_instance_max_depth     = new name{"class", "instance_max_depth"};
    register_unsigned_option(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH,
                             "(class) max allowed depth in class-instance resolution");
    g_nat_offset_threshold         = new name{"unifier", "nat_offset_cnstr_threshold"};
    register_unsigned_option(*g_nat_offset_threshold, LEAN_DEFAULT_NAT_OFFSET_CNSTR_THRESHOLD,
                             "(unifier) the unifier has special support for offset nat constraints of the form: "
                             "(t + k_1 =?= s + k_2), (t + k_1 =?= k_2) and (k_1 =?= k_2), "
                             "where k_1 and k_2 are numerals, t and s are arbitrary terms, and they all have type nat, "
                             "the offset constraint solver is used if k_1 and k_2 are smaller than the given threshold");
}

void finalize_type_context() {
    delete g_class_instance_max_depth;
    delete g_nat_offset_threshold;
}
}
