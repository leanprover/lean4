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
#include "library/num.h"
#include "library/check.h"
#include "library/time_task.h"

namespace lean {

/* =====================
   type_context_old::tmp_locals
   ===================== */
type_context_old::tmp_locals::~tmp_locals() {
    for (unsigned i = 0; i < m_locals.size(); i++)
        m_ctx.pop_local();
}

/* =====================
   type_context_old
   ===================== */

type_context_old::type_context_old(environment const & env, options const &, metavar_context const & mctx,
                                   local_context const & lctx, transparency_mode):
    m_env(env),
    m_mctx(mctx), m_lctx(lctx) {
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
