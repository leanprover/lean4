/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/kernel_exception.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/projection.h"
#include "library/module.h"
#include "library/kernel_serializer.h"

namespace lean {
/** \brief This environment extension stores information about all projection functions
    defined in an environment object.
*/
struct projection_ext : public environment_extension {
    name_map<projection_info> m_info;
    projection_ext() {}
};

struct projection_ext_reg {
    unsigned m_ext_id;
    projection_ext_reg() {
        m_ext_id = environment::register_extension(std::make_shared<projection_ext>());
    }
};

static projection_ext_reg * g_ext = nullptr;
static projection_ext const & get_extension(environment const & env) {
    return static_cast<projection_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, projection_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<projection_ext>(ext));
}

static std::string * g_proj_key = nullptr;

static environment save_projection_info_core(environment const & env, name const & p, name const & mk, unsigned nparams,
                                             unsigned i, bool inst_implicit) {
    projection_ext ext = get_extension(env);
    ext.m_info.insert(p, projection_info(mk, nparams, i, inst_implicit));
    return update(env, ext);
}

environment save_projection_info(environment const & env, name const & p, name const & mk, unsigned nparams, unsigned i, bool inst_implicit) {
    environment new_env = save_projection_info_core(env, p, mk, nparams, i, inst_implicit);
    return module::add(new_env, *g_proj_key, [=](environment const &, serializer & s) {
            s << p << mk << nparams << i << inst_implicit;
        });
}

projection_info const * get_projection_info(environment const & env, name const & p) {
    projection_ext const & ext = get_extension(env);
    return ext.m_info.find(p);
}

name_map<projection_info> const & get_projection_info_map(environment const & env) {
    return get_extension(env).m_info;
}

static void projection_info_reader(deserializer & d, shared_environment & senv,
                                   std::function<void(asynch_update_fn const &)> &,
                                   std::function<void(delayed_update_fn const &)> &) {
    name p, mk; unsigned nparams, i; bool inst_implicit;
    d >> p >> mk >> nparams >> i >> inst_implicit;
    senv.update([=](environment const & env) -> environment {
            return save_projection_info_core(env, p, mk, nparams, i, inst_implicit);
        });
}

/** \brief Return true iff the type named \c S can be viewed as
    a structure in the given environment.

    If not, generate an error message using \c pos.
*/
bool is_structure_like(environment const & env, name const & S) {
    optional<inductive::inductive_decls> idecls = inductive::is_inductive_decl(env, S);
    if (!idecls || length(std::get<2>(*idecls)) != 1)
        return false;
    inductive::inductive_decl decl   = head(std::get<2>(*idecls));
    return length(inductive::inductive_decl_intros(decl)) == 1 && *inductive::get_num_indices(env, S) == 0;
}

projection_info const * projection_converter::is_projection(expr const & e) const {
    expr const & f = get_app_fn(e);
    if (is_constant(f))
        return m_proj_info.find(const_name(f));
    else
        return nullptr;
}

bool projection_converter::is_opaque(declaration const & d) const {
    return m_proj_info.find(d.get_name()) != nullptr;
}

optional<pair<expr, constraint_seq>> projection_converter::reduce_projection(expr const & t) {
    projection_info const * info = is_projection(t);
    if (!info)
        return optional<pair<expr, constraint_seq>>();
    buffer<expr> args;
    get_app_args(t, args);
    if (args.size() <= info->m_nparams) {
        return optional<pair<expr, constraint_seq>>();
    }
    unsigned mkidx  = info->m_nparams;
    expr const & mk = args[mkidx];
    pair<expr, constraint_seq> new_mk_cs = whnf(mk);
    expr new_mk     = new_mk_cs.first;
    expr const & new_mk_fn = get_app_fn(new_mk);
    if (!is_constant(new_mk_fn) || const_name(new_mk_fn) != info->m_constructor) {
        return optional<pair<expr, constraint_seq>>();
    }
    buffer<expr> mk_args;
    get_app_args(new_mk, mk_args);
    unsigned i = info->m_nparams + info->m_i;
    if (i >= mk_args.size()) {
        return optional<pair<expr, constraint_seq>>();
    }
    expr r = mk_args[i];
    r = mk_app(r, args.size() - mkidx - 1, args.data() + mkidx + 1);
    return optional<pair<expr, constraint_seq>>(r, new_mk_cs.second);
}

optional<pair<expr, constraint_seq>> projection_converter::norm_ext(expr const & e) {
    if (auto r = reduce_projection(e)) {
        return r;
    } else {
        return default_converter::norm_ext(e);
    }
}

bool projection_converter::postpone_is_def_eq(expr const & t, expr const & s) {
    if (has_expr_metavar(t) || has_expr_metavar(s)) {
        auto it1 = is_projection(t);
        auto it2 = is_projection(s);
        if (it1 && it2) {
            return true;
        }
        if (it1 && is_stuck(t, *m_tc))
            return true;
        if (it2 && is_stuck(s, *m_tc))
            return true;
    }
    return default_converter::postpone_is_def_eq(t, s);
}

// Apply lazy delta-reduction and then normalizer extensions
lbool projection_converter::reduce_def_eq(expr & t_n, expr & s_n, constraint_seq & cs) {
    while (true) {
        // first, keep applying lazy delta-reduction while applicable
        lbool r = lazy_delta_reduction(t_n, s_n, cs);
        if (r != l_undef) return r;

        auto p_t = reduce_projection(t_n);
        auto p_s = reduce_projection(s_n);
        if (p_t && p_s) {
            t_n = whnf_core(p_t->first);
            s_n = whnf_core(p_s->first);
            cs += p_t->second;
            cs += p_s->second;
        } else if (p_t || p_s) {
            expr const & f_t = get_app_fn(t_n);
            expr const & f_s = get_app_fn(s_n);
            if (is_constant(f_t) && is_constant(f_s) && const_name(f_t) == const_name(f_s) &&
                (p_t || is_stuck(t_n, *m_tc)) && (p_s || is_stuck(s_n, *m_tc))) {
                // treat it as a delta-delta step
                return l_undef;
            }
            if (p_t) {
                t_n = whnf_core(p_t->first);
                cs += p_t->second;
            } else if (p_s) {
                s_n = whnf_core(p_s->first);
                cs += p_s->second;
            } else {
                lean_unreachable();
            }
        } else {
            auto new_t_n = d_norm_ext(t_n, cs);
            auto new_s_n = d_norm_ext(s_n, cs);
            if (!new_t_n && !new_s_n)
                return l_undef;
            if (new_t_n) {
                t_n = whnf_core(*new_t_n);
            }
            if (new_s_n) {
                s_n = whnf_core(*new_s_n);
            }
        }
        r = quick_is_def_eq(t_n, s_n, cs);
        if (r != l_undef) return r;
    }
}

optional<expr> projection_converter::is_stuck(expr const & e, type_checker & c) {
    projection_info const * info = is_projection(e);
    if (!info)
        return default_converter::is_stuck(e, c);
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() <= info->m_nparams)
        return none_expr();
    expr mk = whnf(args[info->m_nparams], c).first;
    return c.is_stuck(mk);
}

projection_converter::projection_converter(environment const & env):
    default_converter(env, true) {
    m_proj_info = ::lean::get_extension(env).m_info;
}

void initialize_projection() {
    g_ext      = new projection_ext_reg();
    g_proj_key = new std::string("proj");
    register_module_object_reader(*g_proj_key, projection_info_reader);
}

void finalize_projection() {
    delete g_proj_key;
    delete g_ext;
}
}
