/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/lbool.h"
#include "util/interrupt.h"
#include "util/fresh_name.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/metavar.h"
#include "library/normalize.h"
#include "library/reducible.h"
#include "library/class.h"
#include "library/old_local_context.h"
#include "library/generic_exception.h"
#include "library/io_state_stream.h"
#include "library/replace_visitor.h"
#include "library/constants.h"
#include "library/pp_options.h"
#include "library/choice_iterator.h"
#include "library/legacy_type_context.h"
#include "library/class_instance_resolution.h"

namespace lean {
[[ noreturn ]] void throw_class_exception(char const * msg, expr const & m) { throw_generic_exception(msg, m); }
[[ noreturn ]] void throw_class_exception(expr const & m, pp_fn const & fn) { throw_generic_exception(m, fn); }

static name * g_class_force_new              = nullptr;

bool get_class_force_new(options const & o) {
    return o.get_bool(*g_class_force_new, false);
}

struct cienv {
    typedef std::unique_ptr<legacy_type_context> ti_ptr;
    ti_ptr m_ti_ptr;

    void reset(environment const & env, options const & o, list<expr> const & ctx) {
        m_ti_ptr.reset(new legacy_type_context(env, o, ctx));
    }

    bool compatible_env(environment const & env) {
        environment const & curr_env = m_ti_ptr->env();
        return is_eqp(env, curr_env);
    }

    void ensure_compatible(environment const & env, options const & o, list<expr> const & ctx) {
        if (!m_ti_ptr || !compatible_env(env) || !m_ti_ptr->compatible_local_instances(ctx))
            reset(env, o, ctx);
        if (!m_ti_ptr->update_options(o))
            m_ti_ptr->clear_cache();
    }

    optional<expr> operator()(environment const & env, options const & o,
                              pos_info_provider const * pip, list<expr> const & ctx, expr const & type,
                              expr const & pos_ref) {
        ensure_compatible(env, o, ctx);
        old_type_context::scope_pos_info scope(*m_ti_ptr, pip, pos_ref);
        return m_ti_ptr->mk_class_instance(type);
    }
};

MK_THREAD_LOCAL_GET_DEF(cienv, get_cienv);

static optional<expr> mk_class_instance(environment const & env, options const & o, list<expr> const & ctx,
                                        expr const & e, pos_info_provider const * pip, expr const & pos_ref) {
    return get_cienv()(env, o, pip, ctx, e, pos_ref);
}

optional<expr> mk_class_instance(environment const & env, options const & o, list<expr> const & ctx,
                                 expr const & e, pos_info_provider const * pip) {
    return mk_class_instance(env, o, ctx, e, pip, e);
}

optional<expr> mk_class_instance(environment const & env, list<expr> const & ctx, expr const & e,
                                 pos_info_provider const * pip) {
    return mk_class_instance(env, options(), ctx, e, pip);
}

static constraint mk_class_instance_root_cnstr(environment const & env, io_state const & ios, old_local_context const & _ctx, expr const & m, bool is_strict,
                                               bool use_local_instances, pos_info_provider const * pip) {
    justification j         = mk_failed_to_synthesize_jst(env, m);
    auto choice_fn = [=](expr const & meta, expr const & meta_type, substitution const & s) {
        old_local_context ctx;
        if (use_local_instances)
            ctx = _ctx.instantiate(substitution(s));
        cienv & cenv = get_cienv();
        cenv.ensure_compatible(env, ios.get_options(), ctx.get_data());
        auto cls_name = cenv.m_ti_ptr->is_class(meta_type);
        if (!cls_name) {
            // do nothing, since type is not a class.
            return lazy_list<constraints>(constraints());
        }
        pair<expr, justification> mj = update_meta(meta, s);
        expr new_meta                = mj.first;
        justification new_j          = mj.second;
        if (auto r = mk_class_instance(env, ios.get_options(), ctx.get_data(), meta_type, pip, meta)) {
            constraint c = mk_eq_cnstr(new_meta, *r, new_j);
            return lazy_list<constraints>(constraints(c));
        } else if (is_strict) {
            return lazy_list<constraints>();
        } else {
            return lazy_list<constraints>(constraints());
        }
    };
    bool owner = false;
    delay_factor factor;
    return mk_choice_cnstr(m, choice_fn, factor, owner, j);
}

/** \brief Create a metavariable, and attach choice constraint for generating
    solutions using class-instances
*/
pair<expr, constraint> mk_new_class_instance_elaborator(
    environment const & env, io_state const & ios, old_local_context const & ctx,
    optional<name> const & suffix, bool use_local_instances,
    bool is_strict, optional<expr> const & type, tag g, pos_info_provider const * pip) {
    expr m       = ctx.mk_meta(suffix, type, g);
    constraint c = mk_class_instance_root_cnstr(env, ios, ctx, m, is_strict,
                                                use_local_instances, pip);
    return mk_pair(m, c);
}

optional<expr> mk_class_instance(environment const & env, io_state const & ios, old_local_context const & ctx, expr const & type, bool use_local_instances) {
    if (use_local_instances)
        return mk_class_instance(env, ios.get_options(), ctx.get_data(), type, nullptr);
    else
        return mk_class_instance(env, ios.get_options(), list<expr>(), type, nullptr);
}

optional<expr> mk_class_instance(environment const & env, old_local_context const & ctx, expr const & type) {
    return mk_class_instance(env, ctx.get_data(), type, nullptr);
}

optional<expr> mk_set_instance(old_type_checker & tc, options const & o, list<expr> const & ctx, expr const & type) {
    level lvl        = sort_level(tc.ensure_type(type).first);
    expr is_set     = tc.whnf(mk_app(mk_constant(get_is_trunc_is_set_name(), {lvl}), type)).first;
    return mk_class_instance(tc.env(), o, ctx, is_set);
}

optional<expr> mk_subsingleton_instance(environment const & env, options const & o, list<expr> const & ctx, expr const & type) {
    cienv & cenv = get_cienv();
    cenv.ensure_compatible(env, o, ctx);
    return cenv.m_ti_ptr->mk_subsingleton_instance(type);
}

void initialize_class_instance_resolution() {
    g_class_force_new              = new name{"class", "force_new"};

    register_bool_option(*g_class_force_new,  false,
                         "(class) force new type class resolution procedure to be used even in HoTT mode (THIS IS TEMPORARY OPTION)");
}

void finalize_class_instance_resolution() {
    delete g_class_force_new;
}

pair<expr, constraint> mk_class_instance_elaborator(
    environment const & env, io_state const & ios, old_local_context const & ctx,
    optional<name> const & suffix, bool use_local_instances,
    bool is_strict, optional<expr> const & type, tag g,
    pos_info_provider const * pip) {
    return mk_new_class_instance_elaborator(env, ios, ctx, suffix, use_local_instances,
                                            is_strict, type, g, pip);
}
}
