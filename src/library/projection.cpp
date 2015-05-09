/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/kernel_exception.h"
#include "kernel/instantiate.h"
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

static void projection_info_reader(deserializer & d, shared_environment & senv,
                                   std::function<void(asynch_update_fn const &)> &,
                                   std::function<void(delayed_update_fn const &)> &) {
    name p, mk; unsigned nparams, i; bool inst_implicit;
    d >> p >> mk >> nparams >> i >> inst_implicit;
    senv.update([=](environment const & env) -> environment {
            return save_projection_info_core(env, p, mk, nparams, i, inst_implicit);
        });
}

static name * g_projection_macro_name    = nullptr;
static std::string * g_projection_opcode = nullptr;

class projection_macro_definition_cell : public macro_definition_cell {
    name m_proj_name;
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception(sstream() << "invalid '" << m_proj_name
                            << "' projection macro, incorrect number of arguments");
    }

public:
    projection_macro_definition_cell(name const & n):m_proj_name(n) {}
    name const & get_proj_name() const { return m_proj_name; }
    virtual name get_name() const { return m_proj_name; } // *g_projection_macro_name; }
    virtual format pp(formatter const &) const { return format(m_proj_name); }
    virtual void display(std::ostream & out) const { out << m_proj_name; }

    virtual pair<expr, constraint_seq> check_type(expr const & m, extension_context & ctx, bool infer_only) const {
        check_macro(m);
        environment const & env = ctx.env();
        constraint_seq cs;
        expr s   = macro_arg(m, 0);
        expr s_t = ctx.whnf(ctx.check_type(s, cs, infer_only), cs);
        buffer<expr> I_args;
        expr const & I = get_app_args(s_t, I_args);
        if (is_constant(I)) {
            declaration proj_decl = env.get(m_proj_name);
            if (length(const_levels(I)) != proj_decl.get_num_univ_params())
                throw_kernel_exception(env, sstream() << "invalid projection application '" << m_proj_name
                                       << "', incorrect number of universe parameters", m);
            expr t = instantiate_type_univ_params(proj_decl, const_levels(I));
            I_args.push_back(s);
            unsigned num = I_args.size();
            for (unsigned i = 0; i < num; i++) {
                if (!is_pi(t))
                    throw_kernel_exception(env, sstream() << "invalid projection application '" << m_proj_name
                                           << "', number of arguments mismatch", m);
                t = binding_body(t);
            }
            return mk_pair(instantiate_rev(t, I_args.size(), I_args.data()), cs);
        } else {
            // TODO(Leo)
            throw_kernel_exception(env, sstream() << "projection macros do not support arbitrary terms "
                                   << "containing metavariables yet (solution: use trust-level 0)", m);
        }
    }

    // try to unfold projection argument into a \c c constructor application
    static optional<expr> process_proj_arg(environment const & env, name const & c, expr const & s) {
        if (optional<name> mk_name = is_constructor_app_ext(env, s)) {
            if (*mk_name == c) {
                expr new_s = s;
                while (is_app(new_s) && !is_constructor_app(env, new_s)) {
                    if (auto next_new_s = unfold_app(env, new_s))
                        new_s = *next_new_s;
                    else
                        return none_expr();
                }
                if (is_app(new_s))
                    return some_expr(new_s);
            }
        }
        return none_expr();
    }

    virtual optional<expr> expand(expr const & m, extension_context & ctx) const {
        check_macro(m);
        environment const & env = ctx.env();
        auto info = get_projection_info(env, m_proj_name);
        if (!info)
            throw_kernel_exception(env, sstream() << "invalid projection application '" << m_proj_name
                                   << "', constant is not a projection function", m);
        expr const & s  = macro_arg(m, 0);
        if (optional<expr> mk = process_proj_arg(env, info->m_constructor, s)) {
            // efficient version
            buffer<expr> mk_args;
            get_app_args(*mk, mk_args);
            unsigned i = info->m_nparams + info->m_i;
            lean_assert(i < mk_args.size());
            return some_expr(mk_args[i]);
        } else {
            // use definition
            constraint_seq cs;
            expr s_t = ctx.whnf(ctx.infer_type(s, cs), cs);
            if (cs)
                return none_expr();
            buffer<expr> I_args;
            expr const & I = get_app_args(s_t, I_args);
            if (!is_constant(I))
                return none_expr();
            return some_expr(mk_app(mk_app(mk_constant(m_proj_name, const_levels(I)), I_args), s));
        }
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_projection_opcode);
        s << m_proj_name;
    }
};

expr mk_projection_macro(name const & proj_name, expr const & e) {
    macro_definition def(new projection_macro_definition_cell(proj_name));
    return mk_macro(def, 1, &e);
}

void initialize_projection() {
    g_ext      = new projection_ext_reg();
    g_proj_key = new std::string("proj");
    register_module_object_reader(*g_proj_key, projection_info_reader);
    g_projection_macro_name = new name("projection");
    g_projection_opcode     = new std::string("Proj");
    register_macro_deserializer(*g_projection_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    name proj_name;
                                    d >> proj_name;
                                    return mk_projection_macro(proj_name, args[0]);
                                });
}

void finalize_projection() {
    delete g_proj_key;
    delete g_ext;
    delete g_projection_macro_name;
    delete g_projection_opcode;
}
}
