/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
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
    environment         m_env;
    ir_ext              m_ext;
    name_generator      m_ngen;
    local_ctx           m_lctx;
    buffer<comp_decl>   m_new_decls;
    name                m_base_name;

    environment const & env() const { return m_env; }

    expr visit(expr const & e) {
        // TODO(Leo):
        return e;
    }

public:
    to_ir_fn(environment const & env):
        m_env(env), m_ext(get_extension(env)) {
    }

    pair<environment, comp_decls> operator()(comp_decl const & d) {
        expr v      = d.snd();
        m_base_name = d.fst();
        expr new_v  = visit(v);
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
