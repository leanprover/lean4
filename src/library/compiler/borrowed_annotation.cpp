/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/annotation.h"
#include "library/compiler/util.h"
#include "library/compiler/llnf.h"
#include "library/compiler/extern_attribute.h"
#include "library/compiler/export_attribute.h"

namespace lean {
static name * g_borrowed = nullptr;

expr mk_borrowed(expr const & e) { return mk_annotation(*g_borrowed, e); }
bool is_borrowed(expr const & e) { return is_annotation(e, *g_borrowed); }
expr const & get_borrowed_arg(expr const & e) { lean_assert(is_borrowed(e)); return get_annotation_arg(e); }

struct borrowed_info {
    list<bool> m_borrowed_args;
    bool       m_borrowed_res;
};

/* Inferred borrowed annotations cache. */
struct borrowed_ext : public environment_extension {
    typedef name_map<borrowed_info> cache;
    cache m_cache;
};

struct borrowed_ext_reg {
    unsigned m_ext_id;
    borrowed_ext_reg() { m_ext_id = environment::register_extension(new borrowed_ext()); }
};

static borrowed_ext_reg * g_ext = nullptr;
static borrowed_ext const & get_extension(environment const & env) {
    return static_cast<borrowed_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, borrowed_ext const & ext) {
    return env.update(g_ext->m_ext_id, new borrowed_ext(ext));
}

/* Support for old module manager.
   Remark: this code will be deleted in the future */
struct borrowed_modification : public modification {
    LEAN_MODIFICATION("borrowed");

    name          m_fn;
    borrowed_info m_info;

    borrowed_modification(name const & fn, borrowed_info const & info):m_fn(fn), m_info(info) {}

    void perform(environment & env) const override {
        borrowed_ext ext = get_extension(env);
        ext.m_cache.insert(m_fn, m_info);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_fn << m_info.m_borrowed_res;
        write_list(s, m_info.m_borrowed_args);
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name fn; borrowed_info info;
        d >> fn >> info.m_borrowed_res;
        info.m_borrowed_args = read_list<bool>(d);
        return std::make_shared<borrowed_modification>(fn, info);
    }
};

bool get_inferred_borrowed_info(environment const & env, name const & fn, buffer<bool> & borrowed_args, bool & borrowed_res) {
    borrowed_ext const & ext = get_extension(env);
    if (borrowed_info const * info = ext.m_cache.find(fn)) {
        to_buffer(info->m_borrowed_args, borrowed_args);
        borrowed_res = info->m_borrowed_res;
        return true;
    } else {
        return false;
    }
}

class borrow_inference_fn {
    environment               m_env;
    name_generator            m_ngen;
    buffer<comp_decl> const & m_decls;
    buffer<buffer<bool>>      m_borrowed_args;
    bool                      m_changed;
    unsigned                  m_curr_fidx;
    name_set                  m_owned_vars;
    local_ctx                 m_lctx;

    name_generator & ngen() { return m_ngen; }

    void get_borrowed_info(name const & fn, buffer<bool> & borrowed_args, bool & borrowed_res) {
        if (get_extern_borrowed_info(m_env, fn, borrowed_args, borrowed_res))
            return;
        if (get_inferred_borrowed_info(m_env, fn, borrowed_args, borrowed_res))
            return;
        for (unsigned i = 0; i < m_decls.size(); i++) {
            if (m_decls[i].fst() == fn) {
                borrowed_args.clear();
                borrowed_args.append(m_borrowed_args[i]);
                borrowed_res = false;
                return;
            }
        }
        unsigned arity = get_llnf_arity(m_env, fn);
        borrowed_args.clear();
        borrowed_args.resize(arity, false);
        borrowed_res = false;
    }

    bool has_borrowed_result(name const & fn) {
        buffer<bool> borrowed_args;
        bool borrowed_res;
        get_borrowed_info(fn, borrowed_args, borrowed_res);
        return borrowed_res;
    }

    static bool is_proj(expr const & e) { return is_llnf_proj(get_app_fn(e)); }

    bool is_owned(expr const & e) const {
        return is_fvar(e) && m_owned_vars.contains(fvar_name(e));
    }

    void mark_owned(expr const & e) {
        if (is_fvar(e))
            m_owned_vars.insert(fvar_name(e));
    }

    void mark_owned(buffer<expr> const & es) {
        for (expr const & e : es) mark_owned(e);
    }

    void collect_app(expr const & e, bool terminal) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        if (is_cases_on_app(m_env, e)) {
            for (unsigned i = 1; i < args.size(); i++)
                collect(args[i]);
        } else if (is_llnf_apply(fn) || is_llnf_closure(fn) || is_llnf_reset(fn) || is_llnf_cnstr(fn) || is_llnf_reuse(fn)) {
            mark_owned(args);
        } else if (!is_llnf_op(fn)) {
            bool tail_call = terminal && (m_decls[m_curr_fidx].fst() == const_name(fn));
            buffer<bool> borrowed_args;
            bool borrowed_res;
            get_borrowed_info(const_name(fn), borrowed_args, borrowed_res);
            for (unsigned i = 0; i < args.size(); i++) {
                if (borrowed_args[i]) {
                    if (tail_call && is_owned(args[i])) {
                        /* We want to preserve tail calls.
                           Recall that given a call `f a`, if `a` is owned, but `f`'s argument is borrowed,
                           we must perform `dec a` after `f a`. */
                        lean_assert(const_name(fn) == m_decls[m_curr_fidx].fst());
                        lean_assert(borrowed_args[i] == m_borrowed_args[m_curr_fidx][i]);
                        lean_assert(m_borrowed_args[m_curr_fidx][i]);
                        m_borrowed_args[m_curr_fidx][i] = false;
                        m_changed = true;
                    }
                } else {
                    mark_owned(args[i]);
                }
            }
        }
    }

    expr get_lambda_body(expr e, buffer<expr> & fvars) {
        while (is_lambda(e)) {
            lean_assert(!has_loose_bvars(binding_domain(e)));
            expr type    = binding_domain(e);
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), type);
            fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        return instantiate_rev(e, fvars.size(), fvars.data());
    }

    void collect_lambda(expr const & e) {
        /* Visiting join point */
        buffer<expr> fvars;
        expr body = get_lambda_body(e, fvars);
        for (expr const & x : fvars) {
            /* All join-point arguments are considered to be owned. */
            mark_owned(x);
        }
        return collect(body);
    }

    void collect_let(expr e) {
        buffer<expr> fvars;
        while (is_let(e)) {
            lean_assert(!has_loose_bvars(let_type(e)));
            expr type    = let_type(e);
            expr val     = instantiate_rev(let_value(e), fvars.size(), fvars.data());
            /* if `e` is of ther form `let x := val in x`, process `val` as terminal. */
            bool terminal = is_bvar(let_body(e), 0);
            collect(val, terminal);
            expr new_fvar = m_lctx.mk_local_decl(ngen(), let_name(e), type, val);
            if (is_app(val)) {
                expr const & fn = get_app_fn(val);
                if (is_llnf_apply(fn) || is_llnf_closure(fn) || is_llnf_cnstr(fn) || is_llnf_reuse(fn) || is_llnf_reset(fn)) {
                    mark_owned(new_fvar);
                } else if (is_llnf_proj(fn)) {
                    if (is_owned(app_arg(val)))
                        mark_owned(new_fvar);
                } else if (!is_llnf_op(fn) && !has_borrowed_result(const_name(fn))) {
                    mark_owned(new_fvar);
                }
            }
            fvars.push_back(new_fvar);
            e = let_body(e);
        }
        collect(instantiate_rev(e, fvars.size(), fvars.data()));
        unsigned i = fvars.size();
        while (i > 0) {
            --i;
            expr z     = fvars[i];
            expr z_val = *m_lctx.get_local_decl(z).get_value();
            if (is_owned(z) && is_proj(z_val)) {
                mark_owned(app_arg(z_val));
            }
        }
    }

    void collect(expr const & e, bool terminal = true) {
        switch (e.kind()) {
        case expr_kind::App:    collect_app(e, terminal); return;
        case expr_kind::Let:    collect_let(e); return;
        case expr_kind::Lambda: collect_lambda(e); return;
        default: return;
        }
    }

    void init_borrowed_args() {
        m_borrowed_args.resize(m_decls.size());
        for (unsigned i = 0; i < m_decls.size(); i++) {
            bool is_exported = has_export_name(m_env, m_decls[i].fst());
            /* For now, we assume that all exported functions all arguments are *not* borrowed */
            m_borrowed_args[i].resize(get_num_nested_lambdas(m_decls[i].snd()), !is_exported);
        }
    }

public:
    borrow_inference_fn(environment const & env, buffer<comp_decl> const & decls):
        m_env(env), m_decls(decls) {
    }

    environment operator()() {
        init_borrowed_args();
        m_changed = true;
        while (m_changed) {
            m_changed = false;
            for (unsigned fidx = 0; fidx < m_decls.size(); fidx++) {
                comp_decl const & d = m_decls[fidx];
                m_curr_fidx = fidx;
                m_owned_vars.clear();
                m_lctx = local_ctx();
                expr const & code = d.snd();
                if (is_lambda(code)) {
                    buffer<expr> args;
                    expr body = get_lambda_body(code, args);
                    for (unsigned i = 0; i < m_borrowed_args[fidx].size(); i++) {
                        if (!m_borrowed_args[fidx][i])
                            mark_owned(args[i]);
                    }
                    collect(body);
                    for (unsigned i = 0; i < args.size(); i++) {
                        expr arg_type = m_lctx.get_local_decl(args[i]).get_type();
                        if (!is_llnf_unboxed_type(arg_type) && is_owned(args[i]) && m_borrowed_args[fidx][i]) {
                            m_changed = true;
                            m_borrowed_args[fidx][i] = false;
                        }
                    }
                }
            }
        }
        lean_trace(name({"compiler", "borrowed_inference"}),
                   for (unsigned fidx = 0; fidx < m_decls.size(); fidx++) {
                       comp_decl const & d = m_decls[fidx];
                       tout() << d.fst();
                       for (unsigned i = 0; i < m_borrowed_args[fidx].size(); i++) {
                           tout() << " " << m_borrowed_args[fidx][i];
                       }
                       tout() << "\n";
                   });
        borrowed_ext ext    = get_extension(m_env);
        environment new_env = m_env;
        for (unsigned fidx = 0; fidx < m_decls.size(); fidx++) {
            name fn = m_decls[fidx].fst();
            borrowed_info info{to_list(m_borrowed_args[fidx]), false};
            new_env = module::add(new_env, std::make_shared<borrowed_modification>(fn, info));
            ext.m_cache.insert(fn, info);
        }
        return update(new_env, ext);
    }
};

environment infer_borrowed_annotations(environment const & env, buffer<comp_decl> const & ds) {
    return borrow_inference_fn(env, ds)();
}

void initialize_borrowed_annotation() {
    g_borrowed = new name("borrowed");
    register_annotation(*g_borrowed);
    g_ext = new borrowed_ext_reg();
    borrowed_modification::init();
    register_trace_class({"compiler", "borrowed_inference"});
}

void finalize_borrowed_annotation() {
    delete g_borrowed;
    delete g_ext;
    borrowed_modification::finalize();
}
}
