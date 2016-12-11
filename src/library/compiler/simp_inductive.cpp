/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/projection.h"
#include "library/normalize.h"
#include "library/constants.h"
#include "library/vm/vm.h"
#include "library/compiler/util.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/compiler_step_visitor.h"
#include "library/compiler/procedure.h"

namespace lean {
static name * g_cases = nullptr;
static name * g_cnstr = nullptr;
static name * g_proj  = nullptr;

static expr mk_cnstr(unsigned cidx) {
    return mk_constant(name(*g_cnstr, cidx));
}

static expr mk_proj(unsigned idx) {
    return mk_constant(name(*g_proj, idx));
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
        return optional<unsigned>(n.get_numeral());
    else
        return optional<unsigned>();
}

optional<unsigned> is_internal_cnstr(expr const & e) {
    return is_internal_symbol(e, *g_cnstr);
}

optional<unsigned> is_internal_cases(expr const & e) {
    return is_internal_symbol(e, *g_cases);
}

optional<unsigned> is_internal_proj(expr const & e) {
    return is_internal_symbol(e, *g_proj);
}

bool is_vm_supported_cases(environment const & env, expr const & e) {
    return
        is_internal_cases(e) ||
        is_constant(e, get_nat_cases_on_name()) ||
        (is_constant(e) && get_vm_builtin_cases_idx(env, const_name(e)));
}

class simp_inductive_fn : public compiler_step_visitor {
    name_map<list<bool>> m_constructor_info;

    void get_constructor_info(name const & n, buffer<bool> & rel_fields) {
        if (auto r = m_constructor_info.find(n)) {
            to_buffer(*r, rel_fields);
        } else {
            get_constructor_relevant_fields(env(), n, rel_fields);
            m_constructor_info.insert(n, to_list(rel_fields));
        }
    }

    /* Return new minor premise and a flag indicating whether the body is unreachable or not */
    pair<expr, bool> visit_minor_premise(expr e, buffer<bool> const & rel_fields) {
        type_context::tmp_locals locals(ctx());
        for (unsigned i = 0; i < rel_fields.size(); i++) {
            lean_assert(is_lambda(e));
            if (rel_fields[i]) {
                expr l = locals.push_local_from_binding(e);
                e = instantiate(binding_body(e), l);
            } else {
                e = instantiate(binding_body(e), mk_neutral_expr());
            }
        }
        e = visit(e);
        bool unreachable = is_unreachable_expr(e);
        return mk_pair(locals.mk_lambda(e), unreachable);
    }

    bool has_only_one_constructor(name const & I_name) const {
        if (auto r = inductive::get_num_intro_rules(env(), I_name))
            return *r == 1;
        else
            return false;
    }

    /* Return true iff inductive datatype I_name has only one constructor,
       and this constructor has only one relevant field.
       The argument rel_fields is a bit-vector of relevant fields.

       In this case, we use a simple optimization where we represent elements of this inductive
       datatype as the only relevant element. */
    bool has_trivial_structure(name const & I_name, buffer<bool> const & rel_fields) const {
        if (!has_only_one_constructor(I_name))
            return false;
        unsigned num_rel = 0;
        for (bool b : rel_fields) {
            if (b)
                num_rel++;
            if (num_rel > 1)
                return false;
        }
        return num_rel == 1;
    }

    /* Given a cases_on application, distribute extra arguments over minor premisses.

           cases_on major minor_1 ... minor_n a_1 ... a_n

       We apply a similar transformation at erase_irrelevant, but its effect can be undone
       in subsequent compilation steps.
    */
    void distribute_extra_args_over_minors(name const & I_name, buffer<name> const & cnames, buffer<expr> & args) {
        lean_assert(args.size() > cnames.size() + 1);
        unsigned nparams = *inductive::get_num_params(env(), I_name);
        for (unsigned i = 0; i < cnames.size(); i++) {
            unsigned carity  = get_constructor_arity(env(), cnames[i]);
            unsigned data_sz = carity - nparams;
            type_context::tmp_locals locals(ctx());
            expr new_minor   = args[i+1];
            for (unsigned j = 0; j < data_sz; j++) {
                if (!is_lambda(new_minor))
                    throw exception("unexpected occurrence of 'cases_on' expression, "
                                    "the minor premise is expected to be a lambda-expression");
                expr local = locals.push_local_from_binding(new_minor);
                new_minor  = instantiate(binding_body(new_minor), local);
            }
            new_minor = beta_reduce(mk_app(new_minor, args.size() - cnames.size() - 1, args.data() + cnames.size() + 1));
            args[i+1] = locals.mk_lambda(new_minor);
        }
        args.shrink(cnames.size() + 1);
    }

    expr visit_cases_on(name const & fn, buffer<expr> & args) {
        name const & I_name = fn.get_prefix();
        if (is_inductive_predicate(env(), I_name))
            throw exception(sstream() << "code generation failed, inductive predicate '" << I_name << "' is not supported");
        bool is_builtin = is_vm_builtin_function(fn);
        buffer<name> cnames;
        get_intro_rule_names(env(), I_name, cnames);
        lean_assert(args.size() >= cnames.size() + 1);
        if (args.size() > cnames.size() + 1)
            distribute_extra_args_over_minors(I_name, cnames, args);
        lean_assert(args.size() == cnames.size() + 1);
        /* Process major premise */
        args[0] = visit(args[0]);
        unsigned num_reachable = 0;
        optional<expr> reachable_case;
        /* Process minor premises */
        for (unsigned i = 0; i < cnames.size(); i++) {
            buffer<bool> rel_fields;
            get_constructor_info(cnames[i], rel_fields);
            auto p = visit_minor_premise(args[i+1], rel_fields);
            expr new_minor = p.first;
            if (i == 0 && has_trivial_structure(I_name, rel_fields)) {
                /* Optimization for an inductive datatype that has a single constructor with only one relevant field */
                return beta_reduce(mk_app(new_minor, args[0]));
            }
            args[i+1] = new_minor;
            if (!p.second) {
                num_reachable++;
                reachable_case = p.first;
            }
        }

        if (num_reachable == 0) {
            return mk_unreachable_expr();
        } else if (num_reachable == 1 && !is_builtin) {
            /* Use _cases.1 */
            return mk_app(mk_cases(1), args[0], *reachable_case);
        } else if (is_builtin) {
            return mk_app(mk_constant(fn), args);
        } else {
            return mk_app(mk_cases(cnames.size()), args);
        }
    }

    expr visit_constructor(name const & fn, buffer<expr> const & args) {
        bool is_builtin  = is_vm_builtin_function(fn);
        name I_name      = *inductive::is_intro_rule(env(), fn);
        unsigned nparams = *inductive::get_num_params(env(), I_name);
        unsigned cidx    = get_constructor_idx(env(), fn);
        buffer<bool> rel_fields;
        get_constructor_info(fn, rel_fields);
        lean_assert(args.size() == nparams + rel_fields.size());
        buffer<expr> new_args;
        for (unsigned i = 0; i < rel_fields.size(); i++) {
            if (rel_fields[i]) {
                new_args.push_back(visit(args[nparams + i]));
            }
        }
        if (has_trivial_structure(I_name, rel_fields)) {
            lean_assert(new_args.size() == 1);
            return new_args[0];
        } else if (is_builtin) {
            return mk_app(mk_constant(fn), new_args);
        } else {
            return mk_app(mk_cnstr(cidx), new_args);
        }
    }

    expr visit_projection(name const & fn, buffer<expr> const & args) {
        projection_info const & info = *get_projection_info(env(), fn);
        expr major = visit(args[info.m_nparams]);
        buffer<bool> rel_fields;
        name I_name = *inductive::is_intro_rule(env(), info.m_constructor);
        get_constructor_info(info.m_constructor, rel_fields);
        lean_assert(info.m_i < rel_fields.size());
        lean_assert(rel_fields[info.m_i]); /* We already erased irrelevant information */
        /* Adjust projection index by ignoring irrelevant fields */
        unsigned j = 0;
        for (unsigned i = 0; i < info.m_i; i++) {
            if (rel_fields[i])
                j++;
        }
        expr r;
        if (has_trivial_structure(I_name, rel_fields)) {
            lean_assert(j == 0);
            r = major;
        } else {
            r = mk_app(mk_proj(j), major);
        }
        /* Add additional arguments */
        for (unsigned i = info.m_nparams + 1; i < args.size(); i++)
            r = mk_app(r, visit(args[i]));
        return r;
    }

    virtual expr visit_app(expr const & e) override {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        if (is_constant(fn)) {
            name const & n = const_name(fn);
            if (is_cases_on_recursor(env(), n)) {
                return visit_cases_on(n, args);
            } else if (inductive::is_intro_rule(env(), n)) {
                return visit_constructor(n, args);
            } else if (is_projection(env(), n)) {
                return visit_projection(n, args);
            }
        }
        return compiler_step_visitor::visit_app(e);
    }

    virtual expr visit_constant(expr const & e) override {
        name const & n = const_name(e);
        if (is_vm_builtin_function(n)) {
            return e;
        } else if (inductive::is_intro_rule(env(), n)) {
            return mk_cnstr(get_constructor_idx(env(), n));
        } else {
            return e;
        }
    }

public:
    simp_inductive_fn(environment const & env):compiler_step_visitor(env) {}
};

expr simp_inductive(environment const & env, expr const & e) {
    return simp_inductive_fn(env)(e);
}

void simp_inductive(environment const & env, buffer<procedure> & procs) {
    simp_inductive_fn fn(env);
    for (auto & proc : procs)
        proc.m_code = fn(proc.m_code);
}

void initialize_simp_inductive() {
    g_cases = new name("_cases");
    g_proj  = new name("_proj");
    g_cnstr = new name("_cnstr");
}

void finalize_simp_inductive() {
    delete g_cases;
    delete g_proj;
    delete g_cnstr;
}
}
