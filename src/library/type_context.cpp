/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <lean/interrupt.h>
#include <lean/flet.h>
#include "util/option_declarations.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/quot.h"
#include "kernel/inductive.h"
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
    return m == transparency_mode::All || m == transparency_mode::Semireducible;
}

transparency_mode ensure_semireducible_mode(transparency_mode m) {
    return is_at_least_semireducible(m) ? m : transparency_mode::Semireducible;
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

type_context_old::type_context_old(environment const & env, options const & o, metavar_context const & mctx,
                                   local_context const & lctx, transparency_mode):
    m_env(env),
    m_mctx(mctx), m_lctx(lctx),
    m_dummy_cache(o),
    m_cache(&m_dummy_cache) {
}

type_context_old::type_context_old(environment const & env, metavar_context const & mctx,
                                   local_context const & lctx, abstract_context_cache & cache, transparency_mode):
    m_env(env),
    m_mctx(mctx), m_lctx(lctx),
    m_cache(&cache) {
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
}

void finalize_type_context() {
}
}
