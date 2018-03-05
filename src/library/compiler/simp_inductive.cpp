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
#include "library/inductive_compiler/ginductive.h"
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

unsigned get_vm_supported_cases_num_minors(environment const & env, expr const & fn) {
    name const & fn_name = const_name(fn);
    if (fn_name == get_nat_cases_on_name()) {
        return 2;
    } else {
        optional<unsigned> builtin_cases_idx = get_vm_builtin_cases_idx(env, fn_name);
        if (builtin_cases_idx) {
            name const & I_name = fn_name.get_prefix();
            return *inductive::get_num_intro_rules(env, I_name);
        } else {
            lean_assert(is_internal_cases(fn));
            return *is_internal_cases(fn);
        }
    }
}

class simp_inductive_core_fn : public compiler_step_visitor {
    name_map<list<bool>> m_constructor_info;
protected:
    /* Return new minor premise and a flag indicating whether the body is unreachable or not */
    pair<expr, bool> visit_minor_premise(expr e, buffer<bool> const & rel_fields) {
        type_context_old::tmp_locals locals(ctx());
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

    void get_constructor_info(name const & n, buffer<bool> & rel_fields) {
        if (auto r = m_constructor_info.find(n)) {
            to_buffer(*r, rel_fields);
        } else {
            get_constructor_relevant_fields(env(), n, rel_fields);
            m_constructor_info.insert(n, to_list(rel_fields));
        }
    }
public:
    simp_inductive_core_fn(environment const & env, abstract_context_cache & cache):
        compiler_step_visitor(env, cache) {}
};

/* \brief Remove constructor/projection/cases_on applications of trivial structures.

   We say a structure is trivial if it has only constructor and
   the constructor has only one relevant field.
   In this case, we use a simple optimization where we represent elements of this inductive
   datatype as the only relevant element. */
class erase_trivial_structures_fn : public simp_inductive_core_fn {
    bool has_only_one_constructor(name const & I_name) const {
        if (auto r = inductive::get_num_intro_rules(env(), I_name))
            return *r == 1;
        else
            return false;
    }

    /* Return true iff inductive datatype I_name has only one constructor,
       and this constructor has only one relevant field.
       The argument rel_fields is a bit-vector of relevant fields. */
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

    expr visit_default(name const & fn, buffer<expr> const & args) {
        buffer<expr> new_args;
        for (expr const & arg : args)
            new_args.push_back(visit(arg));
        return mk_app(mk_constant(fn), new_args);
    }

    expr visit_constructor(name const & fn, buffer<expr> const & args) {
        if (is_vm_builtin_function(fn))
            return visit_default(fn, args);

        name I_name      = *inductive::is_intro_rule(env(), fn);
        buffer<bool> rel_fields;
        get_constructor_info(fn, rel_fields);
        if (has_trivial_structure(I_name, rel_fields)) {
            unsigned nparams = *inductive::get_num_params(env(), I_name);
            for (unsigned i = 0; i < rel_fields.size(); i++) {
                if (rel_fields[i]) {
                    return visit(args[nparams + i]);
                }
            }
            lean_unreachable();
        } else {
            return visit_default(fn, args);
        }
    }

    expr visit_projection(name const & fn, buffer<expr> const & args) {
        if (is_vm_builtin_function(fn))
            return visit_default(fn, args);

        projection_info const & info = *get_projection_info(env(), fn);
        name I_name = *inductive::is_intro_rule(env(), info.m_constructor);
        buffer<bool> rel_fields;
        get_constructor_info(info.m_constructor, rel_fields);
        if (has_trivial_structure(I_name, rel_fields)) {
            expr major = args[info.m_nparams];
            expr r     = visit(major);
            /* Add additional arguments */
            for (unsigned i = info.m_nparams + 1; i < args.size(); i++)
                r = mk_app(r, visit(args[i]));
            return r;
        } else {
            return visit_default(fn, args);
        }
    }

    expr visit_cases_on(name const & fn, buffer<expr> & args) {
        if (is_vm_builtin_function(fn))
            return visit_default(fn, args);

        name const & I_name = fn.get_prefix();
        buffer<name> cnames;
        get_intro_rule_names(env(), I_name, cnames);
        if (cnames.size() != 1)
            return visit_default(fn, args);

        buffer<bool> rel_fields;
        get_constructor_info(cnames[0], rel_fields);

        if (has_trivial_structure(I_name, rel_fields)) {
            lean_assert(args.size() >= 2);
            expr major = visit(args[0]);
            expr minor = visit_minor_premise(args[1], rel_fields).first;
            for (unsigned i = 2; i < args.size(); i++)
                args[i] = visit(args[i]);
            return beta_reduce(mk_app(mk_app(minor, major), args.size() - 2, args.data() + 2));
        } else {
            return visit_default(fn, args);
        }
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
public:
    erase_trivial_structures_fn(environment const & env, abstract_context_cache & cache):
        simp_inductive_core_fn(env, cache) {}
};

class simp_inductive_fn : public simp_inductive_core_fn {
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
            type_context_old::tmp_locals locals(ctx());
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
            return mk_unreachable_expr();
        } else if (num_reachable == 1 && !is_builtin) {
            /* Use _cases.1 */
            return mk_app(mk_cases(1), args[0], *reachable_case);
        } else if (is_builtin) {
            return mk_app(mk_constant(fn), args);
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

    expr visit_default(name const & fn, buffer<expr> const & args) {
        buffer<expr> new_args;
        for (expr const & arg : args)
            new_args.push_back(visit(arg));
        return mk_app(mk_constant(fn), new_args);
    }

    expr visit_constructor(name const & fn, buffer<expr> const & args) {
        if (is_vm_builtin_function(fn)) {
            return visit_default(fn, args);
        } else {
            /* The following invariant should hold since erase_irrelevant rejected code
               where it doesn't hold. */
            lean_assert(ir_to_simulated_ir_offset(env(), fn) == 0);
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
            return mk_app(mk_cnstr(cidx), new_args);
        }
    }

    expr visit_projection(name const & fn, buffer<expr> const & args) {
        if (is_vm_builtin_function(fn)) {
            return visit_default(fn, args);
        } else {
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
            r = mk_app(mk_proj(j), major);
            /* Add additional arguments */
            for (unsigned i = info.m_nparams + 1; i < args.size(); i++)
                r = mk_app(r, visit(args[i]));
            return r;
        }
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
    simp_inductive_fn(environment const & env, abstract_context_cache & cache):
        simp_inductive_core_fn(env, cache) {}
};

/*
  Remark: we used to combine erase_trivial_structures_fn and simp_inductive_fn in
  a single pass. This is bad because the result may contain `cases` applications
  where the number of arguments is not equal to the number of case + 1 (major).
  The issue is that erase_trivial_structures_fn step may produce new opportunites
  for the distribute-arguments-over-minor-premises transformation.

  Here is an small example that exposes the problem:
  ```
  structure box (α : Type) :=
  (val : α)

  def f (g h : box (ℕ → ℕ)) (b : bool) : ℕ → ℕ :=
  box.val (bool.cases_on b g h)
  ```

  Remark: it is useful to erase_trivial_structures before applying lamba lifting since
  it will prevent the generation of unnecessary closures. Here is an example:
  ```
  structure box (α : Type) :=
  (val : α)

  set_option trace.compiler true
  def f1 : box (ℕ → ℕ) :=
  box.mk id
  ```
*/

void erase_trivial_structures(environment const & env, abstract_context_cache & cache, buffer<procedure> & procs) {
    erase_trivial_structures_fn eraser(env, cache);
    for (auto & proc : procs)
        proc.m_code = eraser(proc.m_code);
}

void simp_inductive(environment const & env, abstract_context_cache & cache, buffer<procedure> & procs) {
    simp_inductive_fn simplifier(env, cache);
    for (auto & proc : procs)
        proc.m_code = simplifier(proc.m_code);
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
