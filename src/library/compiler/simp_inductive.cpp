/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/sstream.h"
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/vm/vm.h"
#include "library/compiler/util.h"

namespace lean {
static name * g_cases = nullptr;
static name * g_cnstr = nullptr;

static expr mk_cnstr(unsigned cidx) {
    return mk_constant(name(*g_cnstr, cidx));
}

static expr mk_cases(unsigned n) {
    return mk_constant(name(*g_cases, n));
}

static optional<unsigned> is_internal_symbol(expr const & e, name const & prefix) {
    if (!is_constant(e))
        return optional<unsigned>();
    name const & n = const_name(e);
    if (n.is_atomic() || !n.is_numeral())
        return optional<unsigned>();
    if (n.get_prefix() == prefix)
        return optional<unsigned>(n.get_numeral().get_small_value()); /// <<< HACK
    else
        return optional<unsigned>();
}

optional<unsigned> is_internal_cnstr(expr const & e) {
    return is_internal_symbol(e, *g_cnstr);
}

optional<unsigned> is_internal_cases(expr const & e) {
    return is_internal_symbol(e, *g_cases);
}

class simp_inductive_fn {
    environment          m_env;
    name_generator       m_ngen;
    local_ctx            m_lctx;
    name_map<list<bool>> m_constructor_info;

    environment const & env() { return m_env; }

    name_generator & ngen() { return m_ngen; }

    /* Return new minor premise and a flag indicating whether the body is unreachable or not */
    pair<expr, bool> visit_minor_premise(expr e, buffer<bool> const & rel_fields) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        for (unsigned i = 0; i < rel_fields.size(); i++) {
            lean_assert(is_lambda(e));
            if (rel_fields[i]) {
                expr fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), binding_domain(e));
                fvars.push_back(fvar);
                e = instantiate(binding_body(e), fvar);
            } else {
                e = instantiate(binding_body(e), mk_enf_neutral());
            }
        }
        e = visit(e);
        bool unreachable = is_enf_unreachable(e);
        return mk_pair(m_lctx.mk_lambda(fvars, e), unreachable);
    }

    void get_constructor_info(name const & n, buffer<bool> & rel_fields) {
        if (auto r = m_constructor_info.find(n)) {
            to_buffer(*r, rel_fields);
        } else {
            get_constructor_relevant_fields(env(), n, rel_fields);
            m_constructor_info.insert(n, to_list(rel_fields));
        }
    }

    expr visit_cases_on(expr const & fn, buffer<expr> & args) {
        lean_assert(is_constant(fn));
        name const & I_name = const_name(fn).get_prefix();
        if (is_inductive_predicate(env(), I_name))
            throw exception(sstream() << "code generation failed, inductive predicate '" << I_name << "' is not supported");
        buffer<name> cnames;
        get_constructor_names(env(), I_name, cnames);
        lean_assert(args.size() == cnames.size() + 1);
        /* Process major premise */
        args[0] = visit(args[0]);
        unsigned num_reachable = 0;
        expr reachable_case;
        unsigned last_reachable_idx = 0;
        /* Process minor premises */
        for (unsigned i = 0; i < cnames.size(); i++) {
            buffer<bool> rel_fields;
            get_constructor_info(cnames[i], rel_fields);
            auto p = visit_minor_premise(args[i+1], rel_fields);
            expr new_minor = p.first;
            args[i+1] = new_minor;
            if (!p.second) {
                num_reachable++;
                last_reachable_idx = i+1;
                reachable_case     = p.first;
            }
        }

        if (num_reachable == 0) {
            return mk_enf_unreachable();
        } else if (num_reachable == 1) {
            /* Use _cases.1 */
            return mk_app(mk_cases(1), args[0], reachable_case);
        } else {
            if (last_reachable_idx != cnames.size()) {
                /* Compress number of cases by removing the tail of unreachable cases */
                buffer<expr> new_args;
                new_args.append(last_reachable_idx+1, args.data());
                new_args.append(args.size() - cnames.size() - 1, args.data() + cnames.size() + 1);
                return mk_app(mk_cases(last_reachable_idx), new_args);
            } else {
                return mk_app(mk_cases(cnames.size()), args);
            }
        }
    }

    expr visit_default(expr const & fn, buffer<expr> const & args) {
        buffer<expr> new_args;
        for (expr const & arg : args)
            new_args.push_back(visit(arg));
        return mk_app(fn, new_args);
    }

    expr visit_constructor(expr const & fn, buffer<expr> const & args) {
        lean_assert(is_constant(fn));
        if (is_vm_builtin_function(const_name(fn))) {
            return visit_default(fn, args);
        } else {
            constructor_val cnstr_val = env().get(const_name(fn)).to_constructor_val();
            unsigned nparams = cnstr_val.get_nparams();
            unsigned cidx    = get_constructor_idx(env(), const_name(fn));
            buffer<bool> rel_fields;
            get_constructor_info(const_name(fn), rel_fields);
            lean_assert(args.size() == nparams + rel_fields.size());
            buffer<expr> new_args;
            for (unsigned i = 0; i < rel_fields.size(); i++) {
                if (rel_fields[i]) {
                    new_args.push_back(visit(args[nparams + i]));
                }
            }
            return mk_app(mk_cnstr(cidx), new_args);
        }
    }

    expr visit_app(expr const & e) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);
        if (is_constant(fn)) {
            name const & n = const_name(fn);
            if (is_cases_on_recursor(env(), n)) {
                return visit_cases_on(fn, args);
            } else if (is_constructor(env(), n)) {
                return visit_constructor(fn, args);
            }
        }
        fn = visit(fn);
        return visit_default(fn, args);
    }

    expr visit_constant(expr const & e) {
        name const & n = const_name(e);
        if (is_vm_builtin_function(n)) {
            return e;
        } else if (is_constructor(env(), n)) {
            return mk_cnstr(get_constructor_idx(env(), n));
        } else {
            return e;
        }
    }

    expr visit_let(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        while (is_let(e)) {
            lean_assert(!has_loose_bvars(let_type(e)));
            expr new_val  = visit(instantiate_rev(let_value(e), fvars.size(), fvars.data()));
            expr new_fvar = m_lctx.mk_local_decl(ngen(), let_name(e), let_type(e), new_val);
            fvars.push_back(new_fvar);
            e = let_body(e);
        }
        expr r = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        return m_lctx.mk_lambda(fvars, r);
    }

    expr visit_lambda(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        while (is_lambda(e)) {
            lean_assert(!has_loose_bvars(binding_domain(e)));
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), binding_domain(e));
            fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        expr r = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        return m_lctx.mk_lambda(fvars, r);
    }

    expr visit_proj(expr const & e) {
        name S_name = proj_sname(e);
        inductive_val S_val = env().get(S_name).to_inductive_val();
        lean_assert(S_val.get_ncnstrs() == 1);
        name k_name = head(S_val.get_cnstrs());
        buffer<bool> rel_fields;
        get_constructor_info(k_name, rel_fields);
        /* Adjust projection index by ignoring irrelevant fields */
        unsigned j = 0;
        for (unsigned i = 0; i < proj_idx(e).get_small_value(); i++) {
            if (rel_fields[i])
                j++;
        }
        expr v = visit(proj_expr(e));
        return mk_proj(S_name, j, v);
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::App:    return visit_app(e);
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        case expr_kind::Proj:   return visit_proj(e);
        case expr_kind::Const:  return visit_constant(e);
        default:                return e;
        }
    }

public:
    simp_inductive_fn(environment const & env):
        m_env(env) {}

    expr operator()(expr const & e) { return visit(e); }
};

expr simp_inductive(environment const & env, expr const & e) {
    return simp_inductive_fn(env)(e);
}

void initialize_simp_inductive() {
    g_cases = new name("_cases");
    g_cnstr = new name("_cnstr");
}

void finalize_simp_inductive() {
    delete g_cases;
    delete g_cnstr;
}
}
