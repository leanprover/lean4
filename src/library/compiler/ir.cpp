/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/module.h"
#include "library/compiler/util.h"

namespace lean {
/* Extension used to store data needed when translating LLNF into IR.
   TODO(Leo): use the to be implemented new module system. */
struct ir_ext : public environment_extension {
    typedef name_map<name> boxed_map;
    boxed_map m_boxed_map;
};

struct ir_ext_reg {
    unsigned m_ext_id;
    ir_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<ir_ext>()); }
};

static ir_ext_reg * g_ext = nullptr;
static ir_ext const & get_extension(environment const & env) {
    return static_cast<ir_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, ir_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<ir_ext>(ext));
}

static name * g_inc_instr = nullptr;
static expr * g_dec_instr = nullptr;
static expr * g_apply_instr = nullptr;
static name * g_mk_closure_instr = nullptr;

expr mk_inc_instr_expr(unsigned n) {
    return mk_constant(name(*g_inc_instr, n));
}

expr mk_dec_instr_expr() {
    return *g_dec_instr;
}

expr mk_apply_instr_expr() {
    return *g_apply_instr;
}

expr mk_mk_closure_instr_expr(unsigned arity) {
    return mk_constant(name(*g_mk_closure_instr, arity));
}

class to_ir_fn {
    enum var_kind { BObject, Object, Scalar };
    typedef std::unordered_map<name, var_kind, name_hash> var_kinds;
    environment         m_env;
    ir_ext              m_ext;
    name_generator      m_ngen;
    local_ctx           m_lctx;
    buffer<expr>        m_fvars;
    buffer<comp_decl>   m_new_decls;
    name                m_base_name;
    name                m_x;
    name                m_j;
    unsigned            m_next_idx{1};
    unsigned            m_next_jp_idx{1};
    expr_map<name_set>  m_live_obj_vars;
    var_kinds           m_var_kinds;


    environment const & env() const { return m_env; }

    name_generator & ngen() { return m_ngen; }

    name next_name() {
        name r = m_x.append_after(m_next_idx);
        m_next_idx++;
        return r;
    }

    name next_jp_name() {
        name r = m_j.append_after(m_next_jp_idx);
        m_next_jp_idx++;
        return mk_join_point_name(r);
    }

    expr mk_void_type() {
        /* TODO(Leo): add void type? */
        return mk_enf_neutral();
    }

    expr mk_dec(expr const & fvar) {
        return mk_app(mk_dec_instr_expr(), fvar);
    }

    unsigned get_arity(name const & n) const {
        /* First, try to infer arity from `_cstage2` auxiliary definition. */
        name c = mk_cstage2_name(n);
        optional<constant_info> info = env().find(c);
        if (info && info->is_definition()) {
            unsigned arity = 0;
            expr v = info->get_value();
            while (is_lambda(v)) {
                v = binding_body(v);
                arity++;
            }
            return arity;
        }

        /* If `_cstage2` declaration is not available, then use the type.

           Remark: we will probably have to add support for some builtin primitives in
           the future. */
        unsigned arity = 0;
        expr t = env().get(n).get_type();
        while (is_pi(t)) {
            t = binding_body(t);
            arity++;
        }
        return arity;
    }

    void register_var_kind(expr const & fvar) {
        lean_assert(is_fvar(fvar));
        local_decl d = m_lctx.get_local_decl(fvar);
        if (is_join_point_name(d.get_user_name())) return;
        if (d.get_type() == mk_enf_object_type()) {
            /* TODO(Leo): add support for borrowed variables */
            m_var_kinds.insert(mk_pair(fvar_name(fvar), Object));
        } else {
            m_var_kinds.insert(mk_pair(fvar_name(fvar), Scalar));
        }
    }

    void collect_live_obj_vars(expr const & e, name_set & S) {
        name_set visited_jps;
        if (!has_fvar(e)) return;
        for_each(e, [&](expr const & x, unsigned) {
                if (!has_fvar(x)) return false;
                if (is_fvar(x)) {
                    local_decl d = m_lctx.get_local_decl(x);
                    if (is_join_point_name(d.get_user_name())) {
                        if (visited_jps.contains(fvar_name(x))) return false;
                        visited_jps.insert(fvar_name(x));
                        name_set jp_vars = get_live_obj_vars(*d.get_value());
                        S.merge(jp_vars);
                    } else {
                        S.insert(fvar_name(x));
                    }
                }
                return true;
            });
    }

    name_set get_live_obj_vars(expr const & e) {
        auto it = m_live_obj_vars.find(e);
        if (it != m_live_obj_vars.end())
            return it->second;
        name_set S;
        collect_live_obj_vars(e, S);
        m_live_obj_vars.insert(mk_pair(e, S));
        return S;
    }

    bool is_dead_obj_var(expr const & e, name_set & live_obj_vars) {
        if (!is_fvar(e)) return false;
        if (live_obj_vars.contains(fvar_name(e))) return false;
        auto it = m_var_kinds.find(fvar_name(e));
        return it != m_var_kinds.end() && it->second == Object;
    }

    void insert_live_obj_var(expr const & e, name_set & live_obj_vars) {
        if (is_fvar(e)) {
            auto it = m_var_kinds.find(fvar_name(e));
            if (it != m_var_kinds.end() && it->second != Scalar)
                live_obj_vars.insert(fvar_name(e));
        }
    }

    expr process_cases(expr const & e, name_set & live_obj_vars) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        lean_assert(is_constant(fn));
        lean_assert(args.size() >= 3);
        insert_live_obj_var(args[0], live_obj_vars);
        // TODO(Leo):
        return mk_app(fn, args);
    }

    expr process(expr const & e, name_set & live_obj_vars) {
        if (is_cases_on_app(env(), e)) {
            return process_cases(e, live_obj_vars);
        }
        // TODO(Leo)
        return e;
    }

    expr mk_let(buffer<expr> const & input_vars, unsigned saved_fvars_size, expr r) {
        name_set live_obj_vars;
        r = process(r, live_obj_vars);
        /* `entries` contains pairs (let-decl fvar, new value) for building the resultant let-declaration.
           We simplify the value of some let-declarations in this method, but we don't want to create
           a new temporary declaration just for this. */
        buffer<expr_pair> entries;
        while (m_fvars.size() > saved_fvars_size) {
            expr x = m_fvars.back();
            m_fvars.pop_back();
            local_decl x_decl = m_lctx.get_local_decl(x);
            expr val          = *x_decl.get_value();
            if (!is_join_point_name(x_decl.get_user_name())) {
                /* If `x` is a dead object variable, we don't even process it */
                if (!is_dead_obj_var(x, live_obj_vars)) {
                    val = process(val, live_obj_vars);
                    live_obj_vars.erase(fvar_name(x));
                    entries.emplace_back(x, val);
                }
            } else {
                entries.emplace_back(x, val);
            }
        }
        /* We need to add a `dec` instruction for each input variable that is dead at the beginning
           of the let-block, and has kind `Object`. */
        for (expr const & input_var : input_vars) {
            if (is_dead_obj_var(input_var, live_obj_vars)) {
                expr val      = mk_dec(input_var);
                expr aux_fvar = m_lctx.mk_local_decl(ngen(), next_name(), mk_void_type(), val);
                entries.emplace_back(aux_fvar, val);
            }
        }
        buffer<name> user_names;
        buffer<expr> fvars;
        buffer<expr> vals;
        buffer<expr> types;
        unsigned i = entries.size();
        while (i > 0) {
            --i;
            expr const & fvar = entries[i].first;
            fvars.push_back(fvar);
            vals.push_back(entries[i].second);
            local_decl fvar_decl = m_lctx.get_local_decl(fvar);
            user_names.push_back(fvar_decl.get_user_name());
            types.push_back(fvar_decl.get_type());
        }
        r = abstract(r, fvars.size(), fvars.data());
        i = fvars.size();
        while (i > 0) {
            --i;
            expr new_value = abstract(vals[i], i, fvars.data());
            expr new_type  = types[i];
            r = ::lean::mk_let(user_names[i], new_type, new_value, r);
        }
        return r;
    }

    expr visit_lambda(expr e) {
        buffer<expr> binding_fvars;
        while (is_lambda(e)) {
            lean_assert(!has_loose_bvars(binding_domain(e)));
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), binding_domain(e), binding_info(e));
            register_var_kind(new_fvar);
            binding_fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        e = instantiate_rev(e, binding_fvars.size(), binding_fvars.data());
        unsigned saved_fvars_size = m_fvars.size();
        e = visit(e);
        e = mk_let(binding_fvars, saved_fvars_size, e);
        e = m_lctx.mk_lambda(binding_fvars, e);
        return e;
    }

    expr visit_let(expr e) {
        buffer<expr> fvars;
        while (is_let(e)) {
            lean_assert(!has_loose_bvars(let_type(e)));
            expr val = instantiate_rev(let_value(e), fvars.size(), fvars.data());
            name n   = let_name(e);
            if (is_internal_name(n)) {
                if (is_join_point_name(n))
                    n = next_jp_name();
                else
                    n = next_name();
            }
            if (is_join_point_name(n)) {
                val = visit(val);
            }
            expr new_fvar = m_lctx.mk_local_decl(ngen(), n, let_type(e), val);
            register_var_kind(new_fvar);
            fvars.push_back(new_fvar);
            m_fvars.push_back(new_fvar);
            e = let_body(e);
        }
        return visit(instantiate_rev(e, fvars.size(), fvars.data()));
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        default:                return e;
        }
    }

public:
    to_ir_fn(environment const & env):
        m_env(env), m_ext(get_extension(env)), m_x("_x"), m_j("_j") {
    }

    pair<environment, comp_decls> operator()(comp_decl const & d) {
        expr v      = d.snd();
        m_base_name = d.fst();
        expr new_v  = visit(v);
        buffer<expr> input;
        new_v       = mk_let(input, 0, new_v);
        comp_decl new_d(d.fst(), new_v);
        environment new_env = update(env(), m_ext);
        return mk_pair(new_env, comp_decls(new_d, comp_decls(m_new_decls)));
    }
};

static pair<environment, comp_decls> to_ir_core(environment const & env, comp_decl const & d) {
    return to_ir_fn(env)(d);
}

pair<environment, comp_decls> to_ir(environment env, comp_decls const & ds) {
    comp_decls r;
    for (comp_decl const & d : ds) {
        comp_decls new_ds;
        std::tie(env, new_ds) = to_ir_core(env, d);
        r = append(r, new_ds);
    }
    return mk_pair(env, r);
}

void initialize_ir() {
    g_ext              = new ir_ext_reg();
    g_inc_instr        = new name("_inc");
    g_dec_instr        = new expr(mk_constant("_dec"));
    g_apply_instr      = new expr(mk_constant("_apply"));
    g_mk_closure_instr = new name("_mk_closure");
}

void finalize_ir() {
    delete g_ext;
    delete g_inc_instr;
    delete g_dec_instr;
    delete g_apply_instr;
    delete g_mk_closure_instr;
}
}
