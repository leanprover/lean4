/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "util/sstream.h"
#include "util/list_fn.h"
#include "kernel/expr.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/error_msgs.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "kernel/replace_fn.h"
#include "library/generic_exception.h"
#include "library/kernel_serializer.h"
#include "library/io_state_stream.h"
#include "library/annotation.h"
#include "library/util.h"
#include "library/locals.h"
#include "library/constants.h"
#include "library/normalize.h"
#include "library/pp_options.h"
#include "library/tactic/inversion_tactic.h"

namespace lean {
static name * g_equations_name                 = nullptr;
static name * g_equation_name                  = nullptr;
static name * g_no_equation_name               = nullptr;
static name * g_decreasing_name                = nullptr;
static name * g_inaccessible_name              = nullptr;
static name * g_equations_result_name          = nullptr;
static std::string * g_equations_opcode        = nullptr;
static std::string * g_equation_opcode         = nullptr;
static std::string * g_no_equation_opcode      = nullptr;
static std::string * g_decreasing_opcode       = nullptr;
static std::string * g_equations_result_opcode = nullptr;

[[ noreturn ]] static void throw_eqs_ex() { throw exception("unexpected occurrence of 'equations' expression"); }

class equations_macro_cell : public macro_definition_cell {
    unsigned m_num_fns;
public:
    equations_macro_cell(unsigned num_fns):m_num_fns(num_fns) {}
    virtual name get_name() const { return *g_equations_name; }
    virtual pair<expr, constraint_seq> check_type(expr const &, extension_context &, bool) const { throw_eqs_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_eqs_ex(); }
    virtual void write(serializer & s) const { s << *g_equations_opcode << m_num_fns; }
    unsigned get_num_fns() const { return m_num_fns; }
};

class equation_base_macro_cell : public macro_definition_cell {
public:
    virtual pair<expr, constraint_seq> check_type(expr const &, extension_context &, bool) const {
        expr dummy = mk_Prop();
        return mk_pair(dummy, constraint_seq());
    }
    virtual optional<expr> expand(expr const &, extension_context &) const {
        expr dummy = mk_Type();
        return some_expr(dummy);
    }
};

class equation_macro_cell : public equation_base_macro_cell {
public:
    virtual name get_name() const { return *g_equation_name; }
    virtual void write(serializer & s) const { s.write_string(*g_equation_opcode); }
};

// This is just a placeholder to indicate no equations were provided
class no_equation_macro_cell : public equation_base_macro_cell {
public:
    virtual name get_name() const { return *g_no_equation_name; }
    virtual void write(serializer & s) const { s.write_string(*g_no_equation_opcode); }
};

class decreasing_macro_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 2)
            throw exception("invalid 'decreasing' expression, incorrect number of arguments");
    }
public:
    decreasing_macro_cell() {}
    virtual name get_name() const { return *g_decreasing_name; }
    virtual pair<expr, constraint_seq> check_type(expr const & m, extension_context & ctx, bool infer_only) const {
        check_macro(m);
        return ctx.check_type(macro_arg(m, 0), infer_only);
    }
    virtual optional<expr> expand(expr const & m, extension_context &) const {
        check_macro(m);
        return some_expr(macro_arg(m, 0));
    }
    virtual void write(serializer & s) const { s.write_string(*g_decreasing_opcode); }
};

static macro_definition * g_equation    = nullptr;
static macro_definition * g_no_equation = nullptr;
static macro_definition * g_decreasing  = nullptr;

bool is_equation(expr const & e) { return is_macro(e) && macro_def(e) == *g_equation; }

bool is_lambda_equation(expr const & e) {
    if (is_lambda(e))
        return is_lambda_equation(binding_body(e));
    else
        return is_equation(e);
}

expr const & equation_lhs(expr const & e) { lean_assert(is_equation(e)); return macro_arg(e, 0); }
expr const & equation_rhs(expr const & e) { lean_assert(is_equation(e)); return macro_arg(e, 1); }
expr mk_equation(expr const & lhs, expr const & rhs) {
    expr args[2] = { lhs, rhs };
    return mk_macro(*g_equation, 2, args);
}
expr mk_no_equation() { return mk_macro(*g_no_equation); }
bool is_no_equation(expr const & e) { return is_macro(e) && macro_def(e) == *g_no_equation; }

bool is_lambda_no_equation(expr const & e) {
    if (is_lambda(e))
        return is_lambda_no_equation(binding_body(e));
    else
        return is_no_equation(e);
}

bool is_decreasing(expr const & e) { return is_macro(e) && macro_def(e) == *g_decreasing; }
expr const & decreasing_app(expr const & e) { lean_assert(is_decreasing(e)); return macro_arg(e, 0); }
expr const & decreasing_proof(expr const & e) { lean_assert(is_decreasing(e)); return macro_arg(e, 1); }
expr mk_decreasing(expr const & t, expr const & H) {
    expr args[2] = { t, H };
    return mk_macro(*g_decreasing, 2, args);
}

bool is_equations(expr const & e) { return is_macro(e) && macro_def(e).get_name() == *g_equations_name; }
bool is_wf_equations_core(expr const & e) {
    lean_assert(is_equations(e));
    return macro_num_args(e) >= 3 && !is_lambda_equation(macro_arg(e, macro_num_args(e) - 1));
}
bool is_wf_equations(expr const & e) { return is_equations(e) && is_wf_equations_core(e); }
unsigned equations_size(expr const & e) {
    lean_assert(is_equations(e));
    if (is_wf_equations_core(e))
        return macro_num_args(e) - 2;
    else
        return macro_num_args(e);
}
unsigned equations_num_fns(expr const & e) {
    lean_assert(is_equations(e));
    return static_cast<equations_macro_cell const*>(macro_def(e).raw())->get_num_fns();
}
expr const & equations_wf_proof(expr const & e) {
    lean_assert(is_wf_equations(e));
    return macro_arg(e, macro_num_args(e) - 1);
}
expr const & equations_wf_rel(expr const & e) {
    lean_assert(is_wf_equations(e));
    return macro_arg(e, macro_num_args(e) - 2);
}
void to_equations(expr const & e, buffer<expr> & eqns) {
    lean_assert(is_equations(e));
    unsigned sz = equations_size(e);
    for (unsigned i = 0; i < sz; i++)
        eqns.push_back(macro_arg(e, i));
}
expr mk_equations(unsigned num_fns, unsigned num_eqs, expr const * eqs) {
    lean_assert(num_fns > 0);
    lean_assert(num_eqs > 0);
    lean_assert(std::all_of(eqs, eqs+num_eqs, [](expr const & e) {
                return is_lambda_equation(e) || is_lambda_no_equation(e);
            }));
    macro_definition def(new equations_macro_cell(num_fns));
    return mk_macro(def, num_eqs, eqs);
}
expr mk_equations(unsigned num_fns, unsigned num_eqs, expr const * eqs, expr const & R, expr const & Hwf) {
    lean_assert(num_fns > 0);
    lean_assert(num_eqs > 0);
    lean_assert(std::all_of(eqs, eqs+num_eqs, is_lambda_equation));
    buffer<expr> args;
    args.append(num_eqs, eqs);
    args.push_back(R);
    args.push_back(Hwf);
    macro_definition def(new equations_macro_cell(num_fns));
    return mk_macro(def, args.size(), args.data());
}

expr update_equations(expr const & eqns, buffer<expr> const & new_eqs) {
    lean_assert(is_equations(eqns));
    lean_assert(!new_eqs.empty());
    if (is_wf_equations(eqns)) {
        return mk_equations(equations_num_fns(eqns), new_eqs.size(), new_eqs.data(),
                            equations_wf_rel(eqns), equations_wf_proof(eqns));
    } else {
        return mk_equations(equations_num_fns(eqns), new_eqs.size(), new_eqs.data());
    }
}

expr mk_inaccessible(expr const & e) { return mk_annotation(*g_inaccessible_name, e); }
bool is_inaccessible(expr const & e) { return is_annotation(e, *g_inaccessible_name); }

// Auxiliary macro used to store the result of a set of equations defining a mutually recursive
// definition.
class equations_result_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_equations_result_name; }
    virtual pair<expr, constraint_seq> check_type(expr const & m, extension_context & ctx, bool infer_only) const {
        return ctx.check_type(macro_arg(m, 0), infer_only);
    }
    virtual optional<expr> expand(expr const & m, extension_context &) const {
        return some_expr(macro_arg(m, 0));
    }
    virtual void write(serializer & s) const { s << *g_equations_result_opcode; }
};

static macro_definition * g_equations_result = nullptr;

static expr mk_equations_result(unsigned n, expr const * rs) {
    return mk_macro(*g_equations_result, n, rs);
}

bool is_equations_result(expr const & e) { return is_macro(e) && macro_def(e) == *g_equations_result; }
unsigned get_equations_result_size(expr const & e) { return macro_num_args(e); }
expr const & get_equations_result(expr const & e, unsigned i) { return macro_arg(e, i); }

void initialize_equations() {
    g_equations_name          = new name("equations");
    g_equation_name           = new name("equation");
    g_no_equation_name        = new name("no_equation");
    g_decreasing_name         = new name("decreasing");
    g_inaccessible_name       = new name("innaccessible");
    g_equations_result_name   = new name("equations_result");
    g_equation                = new macro_definition(new equation_macro_cell());
    g_no_equation             = new macro_definition(new no_equation_macro_cell());
    g_decreasing              = new macro_definition(new decreasing_macro_cell());
    g_equations_result        = new macro_definition(new equations_result_macro_cell());
    g_equations_opcode        = new std::string("Eqns");
    g_equation_opcode         = new std::string("Eqn");
    g_no_equation_opcode      = new std::string("NEqn");
    g_decreasing_opcode       = new std::string("Decr");
    g_equations_result_opcode = new std::string("EqnR");
    register_annotation(*g_inaccessible_name);
    register_macro_deserializer(*g_equations_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    unsigned num_fns;
                                    d >> num_fns;
                                    if (num == 0 || num_fns == 0)
                                        throw corrupted_stream_exception();
                                    if (!is_lambda_equation(args[num-1]) && !is_lambda_no_equation(args[num-1])) {
                                        if (num <= 2)
                                            throw corrupted_stream_exception();
                                        return mk_equations(num_fns, num-2, args, args[num-2], args[num-1]);
                                    } else {
                                        return mk_equations(num_fns, num, args);
                                    }
                                });
    register_macro_deserializer(*g_equation_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 2)
                                        throw corrupted_stream_exception();
                                    return mk_equation(args[0], args[1]);
                                });
    register_macro_deserializer(*g_no_equation_opcode,
                                [](deserializer &, unsigned num, expr const *) {
                                    if (num != 0)
                                        throw corrupted_stream_exception();
                                    return mk_no_equation();
                                });
    register_macro_deserializer(*g_decreasing_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 2)
                                        throw corrupted_stream_exception();
                                    return mk_decreasing(args[0], args[1]);
                                });
    register_macro_deserializer(*g_equations_result_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    return mk_equations_result(num, args);
                                });
}

void finalize_equations() {
    delete g_equations_result_opcode;
    delete g_equation_opcode;
    delete g_no_equation_opcode;
    delete g_equations_opcode;
    delete g_decreasing_opcode;
    delete g_equations_result;
    delete g_equation;
    delete g_no_equation;
    delete g_decreasing;
    delete g_equations_result_name;
    delete g_equations_name;
    delete g_equation_name;
    delete g_no_equation_name;
    delete g_decreasing_name;
    delete g_inaccessible_name;
}

class equation_compiler_fn {
    type_checker &   m_tc;
    io_state const & m_ios;
    expr             m_meta;
    expr             m_meta_type;
    buffer<expr>     m_global_context;
    // The additional context is used to store inductive datatype parameters that occur as arguments in recursive equations.
    // For example, suppose the user writes
    //
    //   definition append : Π (A : Type), list A → list A → list A,
    //   append A nil      l := l,
    //   append A (h :: t) l := h :: (append t l)
    //
    // instead of
    //
    //   definition append (A : Type) : list A → list A → list A,
    //   append nil      l := l,
    //   append (h :: t) l := h :: (append t l)
    //
    // In this case, we move the parameter (A : Type) to m_additional_context and simplify the recursive equations.
    // The simplification is necessary when we are translating the recursive applications into a brec_on recursor.
    buffer<expr>     m_additional_context;
    buffer<expr>     m_fns; // functions being defined

    environment const & env() const { return m_tc.env(); }
    io_state const & ios() const { return m_ios; }
    io_state_stream out() const { return regular(env(), ios()); }
    name mk_fresh_name() { return m_tc.mk_fresh_name(); }
    expr whnf(expr const & e) { return m_tc.whnf(e).first; }
    expr infer_type(expr const & e) { return m_tc.infer(e).first; }
    bool is_def_eq(expr const & e1, expr const & e2) { return m_tc.is_def_eq(e1, e2).first; }
    bool is_proof_irrelevant() const { return m_tc.env().prop_proof_irrel(); }

    optional<name> is_constructor(expr const & e) const {
       if (!is_constant(e))
            return optional<name>();
        return inductive::is_intro_rule(env(), const_name(e));
    }

    expr to_telescope(expr const & e, buffer<expr> & tele) {
        name_generator ngen = m_tc.mk_ngen();
        return ::lean::to_telescope(ngen, e, tele, optional<binder_info>());
    }

    expr fun_to_telescope(expr const & e, buffer<expr> & tele) {
        name_generator ngen = m_tc.mk_ngen();
        return ::lean::fun_to_telescope(ngen, e, tele, optional<binder_info>());
    }

    // Similar to to_telescope, but uses normalization
    expr to_telescope_ext(expr const & e, buffer<expr> & tele) {
        return ::lean::to_telescope(m_tc, e, tele, optional<binder_info>());
    }

    [[ noreturn ]] static void throw_error(char const * msg, expr const & src) { throw_generic_exception(msg, src); }
    [[ noreturn ]] static void throw_error(sstream const & ss, expr const & src) { throw_generic_exception(ss, src); }
    [[ noreturn ]] static void throw_error(expr const & src, pp_fn const & fn) { throw_generic_exception(src, fn); }
    [[ noreturn ]] void throw_error(sstream const & ss) const { throw_generic_exception(ss, m_meta); }
    [[ noreturn ]] void throw_error(expr const & src, sstream const & ss) const { throw_generic_exception(ss, src); }

    void check_limitations(expr const & eqns) const {
        if (is_wf_equations(eqns) && equations_num_fns(eqns) != 1)
            throw_error("mutually recursive equations do not support well-founded recursion yet", eqns);
    }

#ifdef LEAN_DEBUG
    static bool disjoint(list<expr> const & l1, list<expr> const & l2) {
        for (expr const & e1 : l1) {
            for (expr const & e2 : l2) {
                lean_assert(mlocal_name(e1) != mlocal_name(e2));
            }
        }
        return true;
    }

    // Return true iff all names in s1 are names of local constants in s2.
    static bool contained(list<optional<name>> const & s1, list<expr> const & s2) {
        return std::all_of(s1.begin(), s1.end(), [&](optional<name> const & n) {
                return
                    !n ||
                    std::any_of(s2.begin(), s2.end(), [&](expr const & e) {
                            return mlocal_name(e) == *n;
                        });
            });
    }
#endif

    struct eqn {
        // The local context for an equation is of additional
        // local constants occurring in m_patterns and m_rhs
        // which are not in m_global_context or
        // in the function containing the equation.
        // Remark: each function/program contains its own m_context.
        // So, the variables occurring in m_patterns and m_rhs
        // are in m_global_context, m_context, or m_local_context,
        // or is one of the functions being defined.
        // We say an equation is in "compiled" form
        // if m_local_context and m_patterns are empty.
        list<expr> m_local_context;
        list<expr> m_patterns; // patterns to be processed
        expr       m_rhs;      // right-hand-side
        eqn(list<expr> const & c, list<expr> const & p, expr const & r):
            m_local_context(c), m_patterns(p), m_rhs(r) {}
        eqn(eqn const & e, list<expr> const & c, list<expr> const & p):
            eqn(c, p, e.m_rhs) {}
    };

    // Data-structure used to store for compiling pattern matching.
    // We create a program object for each function being defined
    struct program {
        expr       m_fn;        // function being defined
        list<expr> m_context;   // local constants
        list<optional<name>> m_var_stack; // variables that must be matched with the patterns it is a "subset" of m_context.
        list<eqn>  m_eqns;      // equations
        expr       m_type;      // result type

        // Due to dependent pattern matching some elements in m_var_stack are "none", and are skipped
        // during dependent pattern matching.

        // The goal of the compiler is to process all variables in m_var_stack
        program(expr const & fn, list<expr> const & ctx, list<optional<name>> const & s, list<eqn> const & e, expr const & t):
            m_fn(fn), m_context(ctx), m_var_stack(s), m_eqns(e), m_type(t) {
            lean_assert(contained(m_var_stack, m_context));
        }
        program(program const & p, list<expr> const & ctx, list<optional<name>> const & new_s, list<eqn> const & new_e):
            program(p.m_fn, ctx, new_s, new_e, p.m_type) {}
        program(program const & p, list<optional<name>> const & new_s, list<eqn> const & new_e):
            program(p.m_fn, p.m_context, new_s, new_e, p.m_type) {}
        program(program const & p, list<expr> const & ctx):
            program(p.m_fn, ctx, p.m_var_stack, p.m_eqns, p.m_type) {}
        program(program const & p, list<eqn> const & new_e):
            program(p, p.m_var_stack, new_e) {}
        program() {}
        expr const & get_var(name const & n) const {
            for (expr const & v : m_context) {
                if (mlocal_name(v) == n)
                    return v;
            }
            lean_unreachable();
        }
    };

    // Auxiliary fields for producing error messages
    buffer<program>  m_init_prgs;
    unsigned         m_prg_idx; // current program index being compiled

#ifdef LEAN_DEBUG
    // For debugging purposes: checks whether all local constants occurring in \c e
    // are in local_ctx or m_global_context
    bool check_ctx(expr const & e, list<expr> const & context, list<expr> const & local_context) const {
        for_each(e, [&](expr const & e, unsigned) {
                if (is_local(e)) {
                    if (!(contains_local(e, local_context) ||
                          contains_local(e, context) ||
                          contains_local(e, m_additional_context) ||
                          contains_local(e, m_global_context) ||
                          contains_local(e, m_fns))) {
                        lean_unreachable();
                    }
                    return false; // do not visit type
                }
                if (is_metavar(e))
                    return false;  // do not visit type
                return true;
            });
        return true;
    }

    // For debugging purposes: check if the program is well-formed
    bool check_program(program const & s) const {
        unsigned sz = length(s.m_var_stack);
        lean_assert(contained(s.m_var_stack, s.m_context));
        for (eqn const & e : s.m_eqns) {
            // the number of patterns in each equation is equal to the variable stack size
            if (length(e.m_patterns) != sz) {
                lean_unreachable();
                return false;
            }
            check_ctx(e.m_rhs, s.m_context, e.m_local_context);
            for (expr const & p : e.m_patterns)
                check_ctx(p, s.m_context, e.m_local_context);
            lean_assert(disjoint(e.m_local_context, s.m_context));
        }
        return true;
    }
#endif

    // Initialize m_fns (the vector of functions to be compiled)
    void initialize_fns(expr const & eqns) {
        lean_assert(is_equations(eqns));
        unsigned num_fns = equations_num_fns(eqns);
        buffer<expr> eqs;
        to_equations(eqns, eqs);
        expr eq = eqs[0];
        for (unsigned i = 0; i < num_fns; i++) {
            expr fn = mk_local(mk_fresh_name(), binding_name(eq), binding_domain(eq), binder_info());
            m_fns.push_back(fn);
            eq      = instantiate(binding_body(eq), fn);
        }
    }

    // Store in \c arities the number of arguments of each function being defined.
    // This procedure also makes sure that two different equations for the same function
    // contain the same number of arguments in the left-hand-side.
    // Remark: after executing this procedure the arity of m_fns[i] is stored in arities[i]
    // if there is at least one equation for m_fns[i].
    void initialize_arities(expr const & eqns, buffer<optional<unsigned>> & arities) {
        lean_assert(arities.empty());
        buffer<expr> eqs;
        to_equations(eqns, eqs);
        lean_assert(!eqs.empty());
        arities.resize(m_fns.size());
        for (expr eq : eqs) {
            if (is_lambda_equation(eq)) {
                for (expr const & fn : m_fns)
                    eq = instantiate(binding_body(eq), fn);
                while (is_lambda(eq))
                    eq = binding_body(eq);
                lean_assert(is_equation(eq));
                expr const & lhs    = equation_lhs(eq);
                buffer<expr> lhs_args;
                expr const & lhs_fn = get_app_args(lhs, lhs_args);
                if (!is_local(lhs_fn))
                    throw_error(sstream() << "invalid recursive equation, "
                                << "left-hand-side is not one of the functions being defined", eq);
                unsigned i = 0;
                for (; i < m_fns.size(); i++) {
                    if (lhs_fn == m_fns[i]) {
                        if (arities[i] && *arities[i] != lhs_args.size())
                            throw_error(sstream() << "invalid recursive equation for '" << lhs_fn << "' "
                                        << "left-hand-side of different equations have different number of arguments", eq);
                        arities[i] = lhs_args.size();
                    }
                }
            }
        }
    }

    // Initialize the variable stack for each function that needs
    // to be compiled.
    // This method assumes m_fns has been already initialized.
    // This method also initialized the buffer prg, but the eqns
    // field of each program is not initialized by it.
    //
    // See initialize_arities for an explanation for \c arities.
    void initialize_var_stack(buffer<program> & prgs, buffer<optional<unsigned>> const & arities) {
        lean_assert(!m_fns.empty());
        lean_assert(prgs.empty());
        for (unsigned i = 0; i < m_fns.size(); i++) {
            expr const & fn = m_fns[i];
            buffer<expr> args;
            expr r_type     = to_telescope(mlocal_type(fn), args);
            for (expr & arg : args)
                arg = update_mlocal(arg, whnf(mlocal_type(arg)));
            if (arities[i]) {
                unsigned arity = *arities[i];
                if (args.size() > arity) {
                    r_type = Pi(args.size() - arity, args.data() + arity, r_type);
                    args.shrink(arity);
                }
            }
            list<expr> ctx    = to_list(args);
            list<optional<name>> vstack = map2<optional<name>>(ctx, [](expr const & e) {
                    return optional<name>(mlocal_name(e));
                });
            prgs.push_back(program(fn, ctx, vstack, list<eqn>(), r_type));
        }
    }

    struct validate_exception {
        expr m_expr;
        validate_exception(expr const & e):m_expr(e) {}
    };

    void check_in_local_ctx(expr const & e, buffer<expr> const & local_ctx) {
        if (!contains_local(e, local_ctx))
            throw_error(e, sstream() << "invalid recursive equation, variable '" << e
                        << "' has the same name of a variable in an outer-scope (solution: rename this variable)");
    }

    // Validate/normalize the given pattern.
    // It stores in reachable_vars any variable that does not occur
    // in inaccessible terms.
    expr validate_pattern(expr pat, buffer<expr> const & local_ctx, name_set & reachable_vars) {
        if (is_inaccessible(pat))
            return pat;
        if (is_local(pat)) {
            reachable_vars.insert(mlocal_name(pat));
            check_in_local_ctx(pat, local_ctx);
            return pat;
        }
        expr new_pat = whnf(pat);
        if (is_local(new_pat)) {
            reachable_vars.insert(mlocal_name(new_pat));
            check_in_local_ctx(new_pat, local_ctx);
            return new_pat;
        }
        buffer<expr> pat_args;
        expr const & fn = get_app_args(new_pat, pat_args);
        if (auto in = is_constructor(fn)) {
            unsigned num_params = *inductive::get_num_params(env(), *in);
            for (unsigned i = num_params; i < pat_args.size(); i++)
                pat_args[i] = validate_pattern(pat_args[i], local_ctx, reachable_vars);
            return mk_app(fn, pat_args, pat.get_tag());
        } else {
            throw validate_exception(pat);
        }
    }

    // Validate/normalize the patterns associated with the given lhs.
    // The lhs is only used to report errors.
    // It stores in reachable_vars any variable that does not occur
    // in inaccessible terms.
    void validate_patterns(expr const & lhs, buffer<expr> const & local_ctx, buffer<expr> & patterns, name_set & reachable_vars) {
        for (expr & pat : patterns) {
            try {
                pat = validate_pattern(pat, local_ctx, reachable_vars);
            } catch (validate_exception & ex) {
                expr problem_expr = ex.m_expr;
                throw_error(lhs, [=](formatter const & fmt) {
                        format r("invalid argument, it is not a constructor, variable, "
                                 "nor it is marked as an inaccessible pattern");
                        r += pp_indent_expr(fmt, problem_expr);
                        r += compose(line(), format("in the following equation left-hand-side"));
                        r += pp_indent_expr(fmt, lhs);
                        return r;
                    });
            }
        }
    }

    // Create initial program state for each function being defined.
    void initialize(expr const & eqns, buffer<program> & prg) {
        lean_assert(is_equations(eqns));
        buffer<optional<unsigned>> arities;
        initialize_fns(eqns);
        initialize_arities(eqns, arities);
        initialize_var_stack(prg, arities);
        buffer<expr> eqs;
        to_equations(eqns, eqs);
        buffer<buffer<eqn>> res_eqns;
        res_eqns.resize(m_fns.size());
        for (expr eq : eqs) {
            if (is_lambda_no_equation(eq))
                continue; // skip marker
            for (expr const & fn : m_fns)
                eq = instantiate(binding_body(eq), fn);
            buffer<expr> local_ctx;
            eq = fun_to_telescope(eq, local_ctx);
            expr const & lhs = equation_lhs(eq);
            expr const & rhs = equation_rhs(eq);
            buffer<expr> patterns;
            expr const & fn  = get_app_args(lhs, patterns);
            name_set reachable_vars;
            validate_patterns(lhs, local_ctx, patterns, reachable_vars);
            for (expr const & v : local_ctx) {
                // every variable in the local_ctx must be "reachable".
                if (!reachable_vars.contains(mlocal_name(v))) {
                    throw_error(lhs, [=](formatter const & fmt) {
                            options o = fmt.get_options().update_if_undef(get_pp_implicit_name(), true);
                            formatter new_fmt = fmt.update_options(o);
                            format r("invalid equation left-hand-side, variable '");
                            r += format(local_pp_name(v));
                            r += format("' only occurs in inaccessible terms in the following equation left-hand-side");
                            r += pp_indent_expr(new_fmt, lhs);
                            return r;
                        });
                }
            }
            for (unsigned i = 0; i < m_fns.size(); i++) {
                if (mlocal_name(fn) == mlocal_name(m_fns[i])) {
                    if (patterns.size() != length(prg[i].m_var_stack))
                        throw_error("ill-formed equation, number of provided arguments does not match function type", eq);
                    res_eqns[i].push_back(eqn(to_list(local_ctx), to_list(patterns), rhs));
                }
            }
        }
        for (unsigned i = 0; i < m_fns.size(); i++) {
            prg[i].m_eqns = to_list(res_eqns[i]);
            lean_assert(check_program(prg[i]));
        }
    }

    // For debugging purposes: display the context at m_ios
    template<typename Ctx>
    void display_ctx(Ctx const & ctx) const {
        bool first = true;
        for (expr const & e : ctx) {
            out() << (first ? "" : ", ") << local_pp_name(e) << " : " << mlocal_type(e);
            first = false;
        }
    }

    // For debugging purposes: dump prg in m_ios
    void display(program const & prg) const {
        display_ctx(prg.m_context);
        out() << " ;;";
        for (optional<name> const & v : prg.m_var_stack) {
            if (v)
                out() << " " << local_pp_name(prg.get_var(*v));
            else
                out() << " <none>";
        }
        out() << " |- " << prg.m_type << "\n";
        out() << "\n";
        for (eqn const & e : prg.m_eqns) {
            out() << "> ";
            display_ctx(e.m_local_context);
            out() << " |-";
            for (expr const & p : e.m_patterns) {
                if (is_atomic(p))
                    out() << " " << p;
                else
                    out() << " (" << p << ")";
            }
            out() << " := " << e.m_rhs << "\n";
        }
    }

    // Return true iff the next pattern in all equations is a variable or an inaccessible term
    bool is_variable_transition(program const & p) const {
        for (eqn const & e : p.m_eqns) {
            lean_assert(e.m_patterns);
            if (!is_local(head(e.m_patterns)) && !is_inaccessible(head(e.m_patterns)))
                return false;
        }
        return true;
    }

    // Return true iff the next pattern in all equations is a constructor.
    bool is_constructor_transition(program const & p) const {
        for (eqn const & e : p.m_eqns) {
            lean_assert(e.m_patterns);
            if (!is_constructor(get_app_fn(head(e.m_patterns))))
                return false;
        }
        return true;
    }

    // Return true if there are no equations, and the next variable is an indexed inductive datatype.
    // In this case, it is worth trying the cases tactic, since this may be a conflicting state.
    bool is_no_equation_constructor_transition(program const & p) {
        lean_assert(p.m_var_stack);
        if (!p.m_eqns && head(p.m_var_stack)) {
            expr const & x = p.get_var(*head(p.m_var_stack));
            expr const & I = get_app_fn(mlocal_type(x));
            return
                is_constant(I) &&
                inductive::is_inductive_decl(env(), const_name(I)) &&
                *inductive::get_num_indices(env(), const_name(I)) > 0;
        } else {
            return false;
        }
    }

    // Return true iff the next pattern of every equation is a constructor or variable,
    // and there are at least one equation where it is a variable and another where it is a
    // constructor.
    bool is_complete_transition(program const & p) const {
        bool has_variable    = false;
        bool has_constructor = false;
        for (eqn const & e : p.m_eqns) {
            lean_assert(e.m_patterns);
            expr const & p = head(e.m_patterns);
            if (is_local(p))
                has_variable = true;
            else if (is_constructor(get_app_fn(p)))
                has_constructor = true;
            else
                return false;
        }
        return has_variable && has_constructor;
    }

    // Remove variable from local context
    static list<expr> remove(list<expr> const & local_ctx, expr const & l) {
        if (!local_ctx)
            return local_ctx;
        else if (mlocal_name(head(local_ctx)) == mlocal_name(l))
            return tail(local_ctx);
        else
            return cons(head(local_ctx), remove(tail(local_ctx), l));
    }

    static expr replace(expr const & e, buffer<expr> const & from_buffer, buffer<expr> const & to_buffer) {
        lean_assert(from_buffer.size() == to_buffer.size());
        return instantiate_rev(abstract_locals(e, from_buffer.size(), from_buffer.data()),
                               to_buffer.size(), to_buffer.data());
    }

    eqn replace(eqn const & e, expr const & from, expr const & to) {
        buffer<expr> from_buffer; from_buffer.push_back(from);
        buffer<expr> to_buffer;   to_buffer.push_back(to);
        buffer<expr> new_ctx;
        for (expr const & l : e.m_local_context) {
            expr new_l = replace(l, from_buffer, to_buffer);
            if (new_l != l) {
                from_buffer.push_back(l);
                to_buffer.push_back(new_l);
            }
            new_ctx.push_back(new_l);
        }
        list<expr> new_patterns = map(e.m_patterns, [&](expr const & p) { return replace(p, from_buffer, to_buffer); });
        expr new_rhs = replace(e.m_rhs, from_buffer, to_buffer);
        return eqn(to_list(new_ctx), new_patterns, new_rhs);
    }

    expr compile_skip(program const & prg) {
        lean_assert(!head(prg.m_var_stack));
        auto new_stack     = tail(prg.m_var_stack);
        buffer<eqn> new_eqs;
        for (eqn const & e : prg.m_eqns) {
            auto new_patterns  = tail(e.m_patterns);
            new_eqs.emplace_back(e.m_local_context, new_patterns, e.m_rhs);
        }
        return compile_core(program(prg, new_stack, to_list(new_eqs)));
    }

    expr compile_variable(program const & prg) {
        // The next pattern of every equation is a variable (or inaccessible term).
        // Thus, we just rename them with the variable on
        // the top of the variable stack.
        // Remark: if the pattern is an inaccessible term, we just ignore it.
        expr x = prg.get_var(*head(prg.m_var_stack));
        auto new_stack     = tail(prg.m_var_stack);
        buffer<eqn> new_eqs;
        for (eqn const & e : prg.m_eqns) {
            expr p = head(e.m_patterns);
            if (is_inaccessible(p)) {
                new_eqs.emplace_back(e.m_local_context, tail(e.m_patterns), e.m_rhs);
            } else {
                lean_assert(is_local(p));
                if (contains_local(p, e.m_local_context)) {
                    list<expr> new_local_ctx = remove(e.m_local_context, p);
                    new_eqs.push_back(replace(eqn(e, new_local_ctx, tail(e.m_patterns)), p, x));
                } else {
                    new_eqs.emplace_back(eqn(e, e.m_local_context, tail(e.m_patterns)));
                }
            }
        }
        return compile_core(program(prg, new_stack, to_list(new_eqs)));
    }

    class implementation : public inversion::implementation {
        eqn m_eqn;
    public:
        implementation(eqn const & e):m_eqn(e) {}

        eqn const & get_eqn() const { return m_eqn; }

        virtual name const & get_constructor_name() const {
            return const_name(get_app_fn(head(m_eqn.m_patterns)));
        }

        virtual void update_exprs(std::function<expr(expr const &)> const & fn) {
            m_eqn.m_local_context = map(m_eqn.m_local_context, fn);
            m_eqn.m_patterns  = map(m_eqn.m_patterns, fn);
            m_eqn.m_rhs       = fn(m_eqn.m_rhs);
        }
    };

    // Wrap the equations from \c p as an "implementation_list" for the inversion package.
    inversion::implementation_list to_implementation_list(program const & p) {
        return map2<inversion::implementation_ptr>(p.m_eqns, [&](eqn const & e) {
                return std::shared_ptr<inversion::implementation>(new implementation(e));
            });
    }

    // Convert program into a goal. We need that to be able to invoke the inversion package.
    goal to_goal(program const & p) {
        buffer<expr> hyps;
        to_buffer(p.m_context, hyps);
        expr new_type = p.m_type;
        expr new_meta = mk_app(mk_metavar(mk_fresh_name(), Pi(hyps, new_type)), hyps);
        return goal(new_meta, new_type);
    }

    // Convert goal and implementation_list back into a program.
    //  - nvars is the number of new variables in the variable stack.
    program to_program(expr const & fn, goal const & g, unsigned nvars, list<optional<name>> const & new_var_stack,
                       inversion::implementation_list const & imps) {
        buffer<expr> new_context;
        g.get_hyps(new_context);
        expr new_type = g.get_type();
        buffer<eqn> new_equations;
        for (inversion::implementation_ptr const & imp : imps) {
            eqn e = static_cast<implementation*>(imp.get())->get_eqn();
            buffer<expr> pat_args;
            get_app_args(head(e.m_patterns), pat_args);
            lean_assert(pat_args.size() >= nvars);
            list<expr> new_pats = to_list(pat_args.end() - nvars, pat_args.end(), tail(e.m_patterns));
            new_equations.push_back(eqn(e.m_local_context, new_pats, e.m_rhs));
        }
        return program(fn, to_list(new_context), new_var_stack, to_list(new_equations), new_type);
    }

    /** \brief Compile constructor transition.
        \remark if fail_if_subgoals is true, then it returns none if there are subgoals.
    */
    optional<expr> compile_constructor_core(program const & p, bool fail_if_subgoals) {
        expr h                    = p.get_var(*head(p.m_var_stack));
        goal g                    = to_goal(p);
        auto imps                 = to_implementation_list(p);
        bool clear_elim           = false;
        if (auto r = apply(env(), ios(), m_tc, g, h, imps, clear_elim)) {
            substitution subst       = r->m_subst;
            list<list<expr>> args    = r->m_args;
            list<rename_map> rn_maps = r->m_renames;
            list<inversion::implementation_list> imps_list = r->m_implementation_lists;
            if (fail_if_subgoals && r->m_goals)
                return none_expr();
            for (goal const & new_g : r->m_goals) {
                list<optional<name>> new_vars = map2<optional<name>>(head(args),
                                                                     [](expr const & a) {
                                                                         if (is_local(a))
                                                                             return optional<name>(mlocal_name(a));
                                                                         else
                                                                             return optional<name>();
                                                                     });
                rename_map const & rn         = head(rn_maps);
                list<optional<name>> new_var_stack = map(tail(p.m_var_stack),
                                                         [&](optional<name> const & n) -> optional<name> {
                                                             if (n)
                                                                 return optional<name>(rn.find(*n));
                                                             else
                                                                 return n;
                                                         });
                list<optional<name>> new_case_stack = append(new_vars, new_var_stack);
                program new_p             = to_program(p.m_fn, new_g, length(new_vars), new_case_stack, head(imps_list));
                args                      = tail(args);
                imps_list                 = tail(imps_list);
                rn_maps                   = tail(rn_maps);
                expr t                    = compile_core(new_p);
                assign(subst, new_g, t);
            }
            expr t = subst.instantiate_all(g.get_meta());
            return some_expr(t);
        } else {
            throw_error(sstream() << "patter matching failed");
        }
    }

    expr compile_constructor(program const & p) {
        bool fail_if_subgoals = false;
        return *compile_constructor_core(p, fail_if_subgoals);
    }

    expr compile_no_equations(program const & p) {
        bool fail_if_subgoals = true;
        if (auto r = compile_constructor_core(p, fail_if_subgoals))
            return *r;
        else
            return compile_variable(p);
    }

    expr mk_constructor(name const & n, levels const & ls, buffer<expr> const & params, buffer<expr> & args) {
        expr c = mk_app(mk_constant(n, ls), params);
        expr t = infer_type(c);
        to_telescope_ext(t, args);
        return mk_app(c, args);
    }

    expr compile_complete(program const & prg) {
        // The next pattern of every equation is a constructor or variable.
        // We split the equations where the next pattern is a variable into cases.
        // That is, we are reducing this case to the compile_constructor case.
        buffer<eqn> new_eqns;
        for (eqn const & e : prg.m_eqns) {
            expr const & p = head(e.m_patterns);
            if (is_local(p)) {
                list<expr> rest_ctx = remove(e.m_local_context, p);
                expr x              = prg.get_var(*head(prg.m_var_stack));
                expr x_type         = whnf(mlocal_type(x));
                buffer<expr> I_args;
                expr const & I      = get_app_args(x_type, I_args);
                name const & I_name = const_name(I);
                levels const & I_ls = const_levels(I);
                unsigned nparams    = *inductive::get_num_params(env(), I_name);
                buffer<expr> I_params;
                I_params.append(nparams, I_args.data());
                buffer<name> constructor_names;
                get_intro_rule_names(env(), I_name, constructor_names);
                for (name const & c_name : constructor_names) {
                    buffer<expr> new_args;
                    expr c = mk_constructor(c_name, I_ls, I_params, new_args);
                    list<expr> new_ctx      = to_list(new_args.begin(), new_args.end(), rest_ctx);
                    list<expr> new_patterns = cons(c, tail(e.m_patterns));
                    new_eqns.push_back(replace(eqn(e, new_ctx, new_patterns), p, c));
                }
            } else {
                new_eqns.push_back(e);
            }
        }
        return compile_core(program(prg, to_list(new_eqns)));
    }

    [[ noreturn ]] void throw_non_exhaustive() {
        program prg = m_init_prgs[m_prg_idx];
        throw_error(m_meta, [=](formatter const & _fmt) {
                options opts  = _fmt.get_options().update_if_undef(get_pp_implicit_name(), true);
                opts          = opts.update_if_undef(get_pp_purify_locals_name(), false);
                formatter fmt = _fmt.update_options(opts);
                format r      = format("invalid non-exhaustive set of recursive equations, "
                                       "left-hand-side(s) after elaboration:");
                for (eqn const & e : prg.m_eqns) {
                    expr lhs = prg.m_fn;
                    for (expr const & p : e.m_patterns) lhs = mk_app(lhs, p);
                    r += pp_indent_expr(fmt, lhs);
                    r += line();
                }
                return r;
            });
    }

    expr compile_core(program const & p) {
        lean_assert(check_program(p));
        // out() << "compile_core step\n";
        // display(p);
        // out() << "------------------\n";
        if (p.m_var_stack) {
            if (!head(p.m_var_stack)) {
                return compile_skip(p);
            } else if (is_no_equation_constructor_transition(p)) {
                return compile_no_equations(p);
            } else if (is_variable_transition(p)) {
                return compile_variable(p);
            } else if (is_constructor_transition(p)) {
                return compile_constructor(p);
            } else if (is_complete_transition(p)) {
                return compile_complete(p);
            } else {
                // In some equations the next pattern is an inaccessible term,
                // and in others it is a constructor.
                throw_error(sstream() << "invalid recursive equations for '" << local_pp_name(p.m_fn)
                            << "', inconsistent use of inaccessible term annotation, "
                            << "in some equations a pattern is a constructor, and in another it is an inaccessible term");
            }
        } else {
            if (p.m_eqns) {
                // variable stack is empty
                expr r = head(p.m_eqns).m_rhs;
                lean_assert(is_def_eq(infer_type(r), p.m_type));
                return r;
            } else {
                throw_non_exhaustive();
            }
        }
    }

    expr compile_pat_match(program const & p, unsigned i) {
        flet<unsigned> set(m_prg_idx, i); // we only use m_prg_idx for producing error messages
        buffer<expr> vars;
        to_buffer(p.m_context, vars);
        if (!is_proof_irrelevant()) {
            // We have to include the global context because the proof relevant version
            // uses the class-instance resolution, and must be able to "see" the complete
            // context.
            program new_p(p, append(to_list(m_global_context), p.m_context));
            return Fun(vars, compile_core(new_p));
        } else {
            return Fun(vars, compile_core(p));
        }
    }

    /** \brief Return true iff \c e is one of the functions being defined */
    bool is_fn(expr const & e) const {
        return is_local(e) && contains_local(e, m_fns);
    }

    /** \brief Return true iff the equations are recursive. */
    bool is_recursive(buffer<program> const & prgs) const {
        lean_assert(!prgs.empty());
        for (program const & p : prgs) {
            for (eqn const & e : p.m_eqns) {
                if (find(e.m_rhs, [&](expr const & e, unsigned) { return is_fn(e); }))
                    return true;
            }
        }
        if (prgs.size() > 1)
            throw_error(sstream() << "mutual recursion is not needed when defining non-recursive functions");
        return false;
    }

    /** \brief Return true if all locals are distinct local constants. */
    static bool all_distinct_locals(unsigned num, expr const * locals) {
        for (unsigned i = 0; i < num; i++) {
            if (!is_local(locals[i]))
                return false;
            if (contains_local(locals[i], locals, locals + i))
                return false;
        }
        return true;
    }

    /** \brief Return true iff \c t is an inductive datatype (I A j) which constains an associated brec_on definition,
        and all indices of t are in ctx. */
    bool is_rec_inductive(list<expr> const & ctx, expr const & t) const {
        expr const & I = get_app_fn(t);
        if (is_constant(I) && env().find(name{const_name(I), "brec_on"})) {
            unsigned nindices = *inductive::get_num_indices(env(), const_name(I));
            if (nindices > 0) {
                buffer<expr> args;
                get_app_args(t, args);
                lean_assert(args.size() >= nindices);
                return
                    all_distinct_locals(nindices, args.end() - nindices) &&
                    std::all_of(args.end() - nindices, args.end(),
                                [&](expr const & idx) { return contains_local(idx, ctx); });
            } else {
                return true;
            }
        } else {
            return false;
        }
    }

    /** \brief Return true iff t1 and t2 are inductive datatypes of the same mutually inductive declaration. */
    bool is_compatible_inductive(expr const & t1, expr const & t2) {
        buffer<expr> args1, args2;
        name const & I1 = const_name(get_app_args(t1, args1));
        name const & I2 = const_name(get_app_args(t2, args2));
        inductive::inductive_decls decls = *inductive::is_inductive_decl(env(), I1);
        unsigned nparams = std::get<1>(decls);
        for (auto decl : std::get<2>(decls)) {
            if (inductive::inductive_decl_name(decl) == I2) {
                // parameters must be definitionally equal
                unsigned i = 0;
                for (; i < nparams; i++) {
                    if (!is_def_eq(args1[i], args2[i]))
                        break;
                }
                if (i == nparams)
                    return true;
            }
        }
        return false;
    }

    /** \brief Return true iff \c t1 and \c t2 are instances of the same inductive datatype */
    static bool is_same_inductive(expr const & t1, expr const & t2) {
        return const_name(get_app_fn(t1)) == const_name(get_app_fn(t2));
    }

    /** \brief Return true iff \c s is structurally smaller than \c t OR equal to \c t */
    bool is_le(expr const & s, expr const & t) {
        return is_def_eq(s, t) || is_lt(s, t);
    }

    /** Return true iff \c s is structurally smaller than \c t */
    bool is_lt(expr s, expr const & t) {
        s = whnf(s);
        if (is_app(s)) {
            expr const & s_fn = get_app_fn(s);
            if (!is_constructor(s_fn))
                return is_lt(s_fn, t); // f < t ==> s := f a_1 ... a_n < t
        }
        buffer<expr> t_args;
        expr const & t_fn = get_app_args(t, t_args);
        if (!is_constructor(t_fn))
            return false;
        return std::any_of(t_args.begin(), t_args.end(), [&](expr const & t_arg) { return is_le(s, t_arg); });
    }

    /** \brief Auxiliary functional object for checking whether recursive application are structurally smaller or not */
    struct check_rhs_fn {
        equation_compiler_fn &   m_main;
        buffer<program> const &  m_prgs;
        buffer<unsigned> const & m_arg_pos;

        check_rhs_fn(equation_compiler_fn & m, buffer<program> const & prgs, buffer<unsigned> const & arg_pos):
            m_main(m), m_prgs(prgs), m_arg_pos(arg_pos) {}

        /** \brief Return true iff all recursive applications in \c e are structurally smaller than \c arg. */
        bool check_rhs(expr const & e, expr const & arg) const {
            switch (e.kind()) {
            case expr_kind::Var:   case expr_kind::Meta:
            case expr_kind::Local: case expr_kind::Constant:
            case expr_kind::Sort:
                return true;
            case expr_kind::Macro:
                for (unsigned i = 0; i < macro_num_args(e); i++)
                    if (!check_rhs(macro_arg(e, i), arg))
                        return false;
                return true;
            case expr_kind::App: {
                buffer<expr> args;
                expr const & fn = get_app_args(e, args);
                if (!check_rhs(fn, arg))
                    return false;
                for (unsigned i = 0; i < args.size(); i++)
                    if (!check_rhs(args[i], arg))
                        return false;
                if (is_local(fn)) {
                    for (unsigned j = 0; j < m_prgs.size(); j++) {
                        if (mlocal_name(fn) == mlocal_name(m_prgs[j].m_fn)) {
                            // it is a recusive application
                            unsigned pos_j = m_arg_pos[j];
                            if (pos_j < args.size()) {
                                expr const & arg_j = args[pos_j];
                                // arg_j must be structurally smaller than arg
                                if (!m_main.is_lt(arg_j, arg))
                                    return false;
                            } else {
                                return false;
                            }
                            break;
                        }
                    }
                }
                return true;
            }
            case expr_kind::Lambda:
            case expr_kind::Pi:
                if (!check_rhs(binding_domain(e), arg)) {
                    return false;
                } else {
                    expr l = mk_local(m_main.mk_fresh_name(), binding_name(e), binding_domain(e), binding_info(e));
                    return check_rhs(instantiate(binding_body(e), l), arg);
                }
            }
            lean_unreachable();
        }

        bool operator()(expr const & e, expr const & arg) const {
            return check_rhs(e, arg);
        }
    };

    /** \brief Return true iff the recursive equations in prgs are "admissible" with respect to
        the following configuration of recursive arguments.
        We say the equations are admissible when every recursive application of prgs[i]
        is structurally smaller at arguments arg_pos[i].
    */
    bool check_rec_args(buffer<program> const & prgs, buffer<unsigned> const & arg_pos) {
        lean_assert(prgs.size() == arg_pos.size());
        check_rhs_fn check_rhs(*this, prgs, arg_pos);
        for (unsigned i = 0; i < prgs.size(); i++) {
            program const & prg = prgs[i];
            unsigned pos_i      = arg_pos[i];
            for (eqn const & e : prg.m_eqns) {
                expr const & p_i = get_ith(e.m_patterns, pos_i);
                if (!check_rhs(e.m_rhs, p_i))
                    return false;
            }
        }
        return true;
    }

    bool find_rec_args(buffer<program> const & prgs, unsigned i, buffer<unsigned> & arg_pos, buffer<expr> & arg_types) {
        if (i == prgs.size()) {
            return check_rec_args(prgs, arg_pos);
        } else {
            program const & p = prgs[i];
            unsigned j = 0;
            for (optional<name> const & n : p.m_var_stack) {
                lean_assert(n);
                expr const & v = p.get_var(*n);
                expr const & t = mlocal_type(v);
                if (// argument must be an inductive datatype
                    is_rec_inductive(p.m_context, t) &&
                    // argument must be an inductive datatype different from the ones in arg_types
                    std::all_of(arg_types.begin(), arg_types.end(),
                                [&](expr const & prev_type) { return !is_same_inductive(t, prev_type); }) &&
                    // argument type must be in the same mutually recursive declaration of previous argument types
                    (arg_types.empty() || is_compatible_inductive(t, arg_types[0]))) {
                    // Found candidate
                    arg_pos.push_back(j);
                    arg_types.push_back(t);
                    if (find_rec_args(prgs, i+1, arg_pos, arg_types))
                        return true;
                    arg_pos.pop_back();
                    arg_types.pop_back();
                }
                j++;
            }
            return false;
        }
    }

    bool find_rec_args(buffer<program> const & prgs, buffer<unsigned> & arg_pos) {
        buffer<expr> arg_types;
        return find_rec_args(prgs, 0, arg_pos, arg_types);
    }

    // Auxiliary function object used to eliminate recursive applications using "below" applications
    struct elim_rec_apps_fn {
        equation_compiler_fn &           m_main;
        buffer<program> const &          m_prgs;
        unsigned                         m_nparams;
        buffer<expr> const &             m_below_cnsts; // below constants
        buffer<expr> const &             m_Cs_locals;   // auxiliary local constants representing the "motives"
        buffer<unsigned> const &         m_rec_arg_pos; // position of recursive argument for each program
        buffer<buffer<unsigned>> const & m_rest_pos;    // position of remaining arguments for each program

        elim_rec_apps_fn(equation_compiler_fn & m, buffer<program> const & prgs, unsigned nparams,
                         buffer<expr> const & below_cnsts, buffer<expr> const & Cs_locals,
                         buffer<unsigned> const & rec_arg_pos, buffer<buffer<unsigned>> const & rest_pos):
            m_main(m), m_prgs(prgs), m_nparams(nparams), m_below_cnsts(below_cnsts), m_Cs_locals(Cs_locals),
            m_rec_arg_pos(rec_arg_pos), m_rest_pos(rest_pos) {}

        bool is_below_type(expr const & t) const {
            expr const & fn = get_app_fn(t);
            return is_constant(fn) && std::find(m_below_cnsts.begin(), m_below_cnsts.end(), fn) != m_below_cnsts.end();
        }

        /** \brief Return the number of arguments in the left-hand-side of program prg_idx */
        unsigned get_lhs_size(unsigned prg_idx) const { return length(m_prgs[prg_idx].m_context); }

        /** \brief Retrieve \c a from the below dictionary \c d. \c d is a term made of products, and C's from (m_Cs_locals).
            \c b is the below constant that was used to create the below dictionary \c d.
        */
        optional<expr> to_below(expr const & d, expr const & a, expr const & b) {
            expr const & fn = get_app_fn(d);
            if (is_constant(fn) && const_name(fn) == get_prod_name()) {
                if (auto r = to_below(app_arg(app_fn(d)), a, mk_pr1(m_main.m_tc, b)))
                    return r;
                else if (auto r = to_below(app_arg(d), a, mk_pr2(m_main.m_tc, b)))
                    return r;
                else
                    return none_expr();
            } else if (is_constant(fn) && const_name(fn) == get_and_name()) {
                // For ibelow, we use "and" instead of products
                if (auto r = to_below(app_arg(app_fn(d)), a, mk_and_elim_left(m_main.m_tc, b)))
                    return r;
                else if (auto r = to_below(app_arg(d), a, mk_and_elim_right(m_main.m_tc, b)))
                    return r;
                else
                    return none_expr();
            } else if (is_local(fn)) {
                for (expr const & C : m_Cs_locals) {
                    if (mlocal_name(C) == mlocal_name(fn) && app_arg(d) == a)
                        return some_expr(b);
                }
                return none_expr();
            } else if (is_pi(d)) {
                if (is_app(a)) {
                    return to_below(instantiate(binding_body(d), app_arg(a)), a, mk_app(b, app_arg(a)));
                } else {
                    return none_expr();
                }
            } else {
                return none_expr();
            }
        }

        expr elim(unsigned prg_idx, buffer<expr> const & args, expr const & below, tag g) {
            // Replace motives with abstract ones. We use the abstract motives (m_Cs_locals) as "markers"
            buffer<expr> below_args;
            expr const & below_cnst = get_app_args(mlocal_type(below), below_args);
            buffer<expr> abst_below_args;
            abst_below_args.append(m_nparams, below_args.data());
            abst_below_args.append(m_Cs_locals);
            for (unsigned i = m_nparams + m_Cs_locals.size(); i < below_args.size(); i++)
                abst_below_args.push_back(below_args[i]);
            expr abst_below   = mk_app(below_cnst, abst_below_args);
            expr below_dict   = normalize(m_main.m_tc, abst_below);
            expr rec_arg      = normalize(m_main.m_tc, args[m_rec_arg_pos[prg_idx]]);
            unsigned lhs_size = get_lhs_size(prg_idx);
            if (optional<expr> b = to_below(below_dict, rec_arg, below)) {
                expr r = *b;
                for (unsigned rest_pos : m_rest_pos[prg_idx]) {
                    if (rest_pos < args.size())
                        r = mk_app(r, args[rest_pos], g);
                }
                for (unsigned i = lhs_size; i < args.size(); i++) {
                    r = mk_app(r, args[i], g);
                }
                return r;
            } else {
                m_main.throw_error(sstream() << "failed to compile recursive equations using "
                                   << "brec_on approach (possible solution: use well-founded recursion)");
            }
        }

        /** \brief Return true iff all recursive applications in \c e are structurally smaller than \c arg. */
        expr elim(expr const & e, optional<expr> const & b) {
            switch (e.kind()) {
            case expr_kind::Var:   case expr_kind::Meta:
            case expr_kind::Local: case expr_kind::Constant:
            case expr_kind::Sort:
                return e;
            case expr_kind::Macro: {
                buffer<expr> new_args;
                for (unsigned i = 0; i < macro_num_args(e); i++)
                    new_args.push_back(elim(macro_arg(e, i), b));
                return update_macro(e, new_args.size(), new_args.data());
            }
            case expr_kind::App: {
                buffer<expr> args;
                expr const & fn = get_app_args(e, args);
                expr new_fn     = elim(fn, b);
                buffer<expr> new_args;
                for (expr const & arg : args)
                    new_args.push_back(elim(arg, b));
                if (is_local(fn) && b) {
                    for (unsigned j = 0; j < m_prgs.size(); j++) {
                        if (mlocal_name(fn) == mlocal_name(m_prgs[j].m_fn)) {
                            return elim(j, new_args, *b, e.get_tag());
                        }
                    }
                }
                return mk_app(new_fn, new_args, e.get_tag());
            }
            case expr_kind::Lambda: {
                expr local    = mk_local(m_main.mk_fresh_name(), binding_name(e), binding_domain(e), binding_info(e));
                expr body     = instantiate(binding_body(e), local);
                expr new_body;
                if (is_below_type(binding_domain(e)))
                    new_body = elim(body, some_expr(local));
                else
                    new_body = elim(body, b);
                return copy_tag(e, Fun(local, new_body));
            }
            case expr_kind::Pi: {
                expr new_domain = elim(binding_domain(e), b);
                expr local      = mk_local(m_main.mk_fresh_name(), binding_name(e), new_domain, binding_info(e));
                expr new_body   = elim(instantiate(binding_body(e), local), b);
                return copy_tag(e, Pi(local, new_body));
            }}
            lean_unreachable();
        }

        expr operator()(expr const & e) {
            return elim(e, none_expr());
        }
    };

    // Fix the i-th argument in the Pi-type t
    expr fix_fn_type(expr const & t, unsigned i, expr const & p) {
        if (!is_pi(t)) {
            throw_error(sstream() << "invalid recursive equation, failed to move parameter '" << p << "'");
        } else if (i == 0) {
            return instantiate(binding_body(t), p);
        } else {
            expr local = mk_local(mk_fresh_name(), binding_name(t), binding_domain(t), binding_info(t));
            expr body  = fix_fn_type(instantiate(binding_body(t), local), i-1, p);
            return Pi(local, body);
        }
    }

    // For each function application (fn ...) in e, replace it with (new_fn ...) and remove the i-th
    // argument.
    expr fix_rec_arg(expr const & fn, expr const & new_fn, unsigned i, expr const & e) {
        return ::lean::replace(e, [&](expr const & e) {
                if (is_app(e) && get_app_fn(e) == fn) {
                    buffer<expr> args;
                    get_app_args(e, args);
                    if (i < args.size())
                        args.erase(i);
                    return some_expr(mk_app(new_fn, args));
                } else {
                    return none_expr();
                }
            });
    }

    // Move inductive datatype parameters occuring in prg to m_additional_context
    pair<program, unsigned> move_params(program const & prg, unsigned arg_pos) {
        expr const & a_type = mlocal_type(get_ith(prg.m_context, arg_pos));
        buffer<expr> a_type_args;
        expr const & I      = get_app_args(a_type, a_type_args);
        unsigned nparams    = *inductive::get_num_params(env(), const_name(I));
        buffer<expr> params;
        params.append(nparams, a_type_args.data());
        if (std::all_of(params.begin(), params.end(),
                        [&](expr const & p) { return !is_local(p) || contains_local(p, m_global_context); })) {
            return mk_pair(prg, arg_pos);
        } else {
            list<expr>             new_context = prg.m_context;
            buffer<optional<name>> new_var_stack;
            buffer<eqn>            new_eqns;
            to_buffer(prg.m_var_stack, new_var_stack);
            to_buffer(prg.m_eqns, new_eqns);
            expr new_fn = prg.m_fn;
            for (expr const & param : params) {
                if (contains_local(param, m_global_context))
                    continue; // parameter doesn't need to be moved
                m_additional_context.push_back(param);
                new_context = remove(new_context, param);
                unsigned i  = 0;
                for (; i < new_var_stack.size(); i++) {
                    if (*new_var_stack[i] == mlocal_name(param))
                        break;
                }
                lean_assert(i < new_var_stack.size());
                lean_assert(i != arg_pos);
                expr new_fn_type = fix_fn_type(mlocal_type(new_fn), i, param);
                expr new_new_fn  = update_mlocal(new_fn, new_fn_type);

                if (i < arg_pos)
                    arg_pos--;
                new_var_stack.erase(i);
                for (eqn & e : new_eqns) {
                    expr const & p = get_ith(e.m_patterns, i);
                    if (!is_local(p)) {
                        throw_error(sstream() << "invalid recursive equations, "
                                    << "trying to pattern match inductive datatype parameter '" << p << "'");
                    } else {
                        list<expr> new_local_ctx = remove(e.m_local_context, p);
                        list<expr> new_patterns  = ::lean::remove(e.m_patterns, p);
                        expr       new_rhs       = fix_rec_arg(new_fn, new_new_fn, i, e.m_rhs);
                        e = replace(eqn(new_local_ctx, new_patterns, new_rhs), p, param);
                    }
                }
                new_fn = new_new_fn;
            }
            return mk_pair(program(new_fn, new_context, to_list(new_var_stack), to_list(new_eqns), prg.m_type), arg_pos);
        }
    }

    // Move inductive datatype parameters occuring in prg to m_additional_context
    void move_params(buffer<program> & prgs, buffer<unsigned> & arg_pos) {
        if (prgs.size() != 1) {
            // The parameters already occur in m_global_context when there is more than one program.
            return;
        }
        auto p     = move_params(prgs[0], arg_pos[0]);
        prgs[0]    = p.first;
        arg_pos[0] = p.second;
        lean_assert(check_program(prgs[0]));
    }

    expr compile_brec_on_core(buffer<program> const & prgs, buffer<unsigned> const & arg_pos) {
        // Return the recursive argument of the i-th program
        auto get_rec_arg = [&](unsigned i) -> expr {
            program const & pi = prgs[i];
            return get_ith(pi.m_context, arg_pos[i]);
        };

        // Return the type of the recursive argument of the i-th program
        auto get_rec_type = [&](unsigned i) -> expr {
            return mlocal_type(get_rec_arg(i));
        };

        // Return the program associated with the inductive datatype named I_name.
        // Return none if there isn't one.
        auto get_prg_for = [&](name const & I_name) -> optional<unsigned> {
            for (unsigned i = 0; i < prgs.size(); i++) {
                expr const & t = get_rec_type(i);
                if (const_name(get_app_fn(t)) == I_name)
                    return optional<unsigned>(i);
            }
            return optional<unsigned>();
        };

        expr const & a0_type = get_rec_type(0);
        lean_assert(is_rec_inductive(prgs[0].m_context, a0_type));
        buffer<expr> a0_type_args;
        expr const & I0      = get_app_args(a0_type, a0_type_args);
        inductive::inductive_decls t = *inductive::is_inductive_decl(env(), const_name(I0));
        unsigned nparams                      = std::get<1>(t);
        list<inductive::inductive_decl> decls = std::get<2>(t);
        buffer<expr> params;
        params.append(nparams, a0_type_args.data());

        // Return true if the local constant l is in the buffer b.
        // This is similar to contains_local, but b may contain arbitrary terms
        auto contains_local_at = [&](expr const & l, buffer<expr> const & b) {
            lean_assert(is_mlocal(l));
            for (expr const & e : b) {
                if (is_local(e) && mlocal_name(l) == mlocal_name(e))
                    return true;
            }
            return false;
        };

        // Distribute parameters of the ith program intro three groups:
        //    indices, major premise (arg), and remaining arguments (rest)
        // We store the position of the rest arguments in the buffer rest_pos.
        // The buffer rest_pos is used to replace the recursive applications with below applications.
        auto distribute_context_core = [&](unsigned i, buffer<expr> & indices, expr & arg, buffer<expr> & rest,
                                           buffer<unsigned> & indices_pos, buffer<unsigned> & rest_pos) {
            program const & p      = prgs[i];
            arg                    = get_rec_arg(i);
            list<expr> const & ctx = p.m_context;
            buffer<expr> arg_args;
            get_app_args(mlocal_type(arg), arg_args);
            lean_assert(nparams <= arg_args.size());
            indices.append(arg_args.size() - nparams, arg_args.data() + nparams);
            unsigned j = 0;
            for (expr const & l : ctx) {
                if (mlocal_name(l) == mlocal_name(arg) || contains_local_at(l, params)) {
                    // do nothing
                } else if (contains_local_at(l, indices)) {
                    indices_pos.push_back(j);
                } else {
                    rest.push_back(l);
                    rest_pos.push_back(j);
                }
                j++;
            }
        };

        auto distribute_context = [&](unsigned i, buffer<expr> & indices, expr & arg, buffer<expr> & rest) {
            buffer<unsigned> indices_pos, rest_pos;
            distribute_context_core(i, indices, arg, rest, indices_pos, rest_pos);
        };

        // Compute the resulting universe level for brec_on
        auto get_brec_on_result_level = [&]() -> level {
            buffer<expr> indices, rest; expr arg;
            distribute_context(0, indices, arg, rest);
            expr r_type = Pi(rest, prgs[0].m_type);
            return sort_level(m_tc.ensure_type(r_type).first);
        };

        level rlvl          = get_brec_on_result_level();
        bool reflexive      = env().prop_proof_irrel() && is_reflexive_datatype(m_tc, const_name(I0));
        bool use_ibelow     = reflexive && is_zero(rlvl);
        if (reflexive) {
            if (!is_zero(rlvl) && !is_not_zero(rlvl))
                throw_error(sstream() << "invalid recursive equations, "
                            << "when trying to recurse over reflexive inductive datatype, "
                            << "the universe level of the resultant universe must be zero OR "
                            << "not zero for every level assignment");
            if (!is_zero(rlvl)) {
                // For reflexive type, the type of brec_on and ibelow perform a +1 on the motive universe.
                // Example: for a reflexive formula type, we have:
                //     formula.below.{l_1} : Π {C : formula → Type.{l_1+1}}, formula → Type.{max (l_1+1) 1}
                if (auto dlvl = dec_level(rlvl)) {
                    rlvl = *dlvl;
                } else {
                    throw_error(sstream() << "invalid recursive equations, "
                                << "when trying to recurse over reflexive inductive datatype, "
                                << "the universe level of the resultant universe must be zero OR "
                                << "not zero for every level assignment, "
                                << "the compiler managed to establish that the resultant "
                                << "universe level L is never zero, but fail to comput L-1");
                }
            }
        }
        levels brec_on_lvls;
        expr brec_on;
        if (use_ibelow) {
            brec_on_lvls = const_levels(I0);
            brec_on      = mk_constant(name{const_name(I0), "binduction_on"}, brec_on_lvls);
        } else {
            brec_on_lvls = cons(rlvl, const_levels(I0));
            brec_on      = mk_constant(name{const_name(I0), "brec_on"}, brec_on_lvls);
        }
        // add parameters
        brec_on = mk_app(brec_on, params);

        buffer<expr> Cs; // brec_on "motives"
        // The following loop fills Cs_locals with auxiliary local constants that will be used to
        // convert recursive applications into "below applications".
        // These constants are essentially abstracting Cs.
        buffer<expr> Cs_locals;
        buffer<buffer<expr>> C_args_buffer;
        for (inductive::inductive_decl const & decl : decls) {
            name const & I_name = inductive::inductive_decl_name(decl);
            expr C;
            C_args_buffer.push_back(buffer<expr>());
            buffer<expr> & C_args = C_args_buffer.back();
            expr C_type           = whnf(infer_type(brec_on));
            expr C_local          = mk_local(mk_fresh_name(), "C", C_type, binder_info());
            Cs_locals.push_back(C_local);
            if (optional<unsigned> p_idx = get_prg_for(I_name)) {
                buffer<expr> indices, rest; expr arg;
                distribute_context(*p_idx, indices, arg, rest);
                expr type = Pi(rest, prgs[*p_idx].m_type);
                C_args.append(indices);
                C_args.push_back(arg);
                C = Fun(C_args, type);
            } else {
                expr d    = binding_domain(C_type);
                expr unit = mk_constant(get_poly_unit_name(), rlvl);
                to_telescope_ext(d, C_args);
                C = Fun(C_args, unit);
            }
            brec_on = mk_app(brec_on, C);
            Cs.push_back(C);
        }

        // add indices and major
        buffer<expr> indices0, rest0; expr arg0;
        distribute_context(0, indices0, arg0, rest0);
        brec_on = mk_app(mk_app(brec_on, indices0), arg0);

        // add functionals
        unsigned i = 0;
        buffer<expr> below_cnsts;
        buffer<buffer<unsigned>> rest_arg_pos;
        for (inductive::inductive_decl const & decl : decls) {
            name const & I_name = inductive::inductive_decl_name(decl);
            expr below_cnst;
            if (use_ibelow)
                below_cnst = mk_constant(name{I_name, "ibelow"}, brec_on_lvls);
            else
                below_cnst = mk_constant(name{I_name, "below"}, brec_on_lvls);
            below_cnsts.push_back(below_cnst);
            expr below     = mk_app(mk_app(below_cnst, params), Cs);
            expr F;
            buffer<expr> & C_args = C_args_buffer[i];
            rest_arg_pos.push_back(buffer<unsigned>());
            if (optional<unsigned> p_idx = get_prg_for(I_name)) {
                program const & prg_i = prgs[*p_idx];
                buffer<expr> indices, rest; expr arg; buffer<unsigned> indices_pos;
                buffer<unsigned> & rest_pos = rest_arg_pos.back();
                distribute_context_core(*p_idx, indices, arg, rest, indices_pos, rest_pos);
                below           = mk_app(mk_app(below, indices), arg);
                expr b          = mk_local(mk_fresh_name(), "b", below, binder_info());
                buffer<expr> new_ctx;
                new_ctx.append(indices);
                new_ctx.push_back(arg);
                new_ctx.push_back(b);
                new_ctx.append(rest);
                F               = compile_pat_match(program(prg_i, to_list(new_ctx)), *p_idx);
            } else {
                expr star    = mk_constant(get_poly_unit_star_name(), rlvl);
                buffer<expr> F_args;
                F_args.append(C_args);
                below        = mk_app(below, F_args);
                F_args.push_back(mk_local(mk_fresh_name(), "b", below, binder_info()));
                F = Fun(F_args, star);
            }
            brec_on = mk_app(brec_on, F);
            i++;
        }
        expr r = elim_rec_apps_fn(*this, prgs, nparams, below_cnsts, Cs_locals, arg_pos, rest_arg_pos)(brec_on);
        // add remaining arguments
        r = mk_app(r, rest0);

        buffer<expr> ctx0_buffer;
        to_buffer(prgs[0].m_context, ctx0_buffer);
        r = Fun(m_additional_context, Fun(ctx0_buffer, r));
        return r;
    }

    expr compile_brec_on(buffer<program> & prgs) {
        lean_assert(!prgs.empty());
        buffer<unsigned> arg_pos;
        if (!find_rec_args(prgs, arg_pos)) {
            throw_error(sstream() << "invalid recursive equations, "
                        << "failed to find recursive arguments that are structurally smaller "
                        << "(possible solution: use well-founded recursion)");
        }
        move_params(prgs, arg_pos);
        buffer<expr> rs;
        for (unsigned i = 0; i < prgs.size(); i++) {
            if (i > 0)
                rs.push_back(mlocal_type(prgs[i].m_fn));
            // Remark: this loop is very hackish.
            // We are "compiling" the code prgs.size() times!
            // This is wasteful. We should rewrite this.
            std::swap(prgs[0], prgs[i]);
            std::swap(arg_pos[0], arg_pos[i]);
            rs.push_back(compile_brec_on_core(prgs, arg_pos));
            std::swap(prgs[0], prgs[i]);
            std::swap(arg_pos[0], arg_pos[i]);
        }

        if (rs.size() > 1)
            return mk_equations_result(rs.size(), rs.data());
        else
            return rs[0];
    }

    expr compile_wf(buffer<program> & /* prgs */) {
        // TODO(Leo)
        return expr();
    }


public:
    equation_compiler_fn(type_checker & tc, io_state const & ios, expr const & meta, expr const & meta_type):
        m_tc(tc), m_ios(ios), m_meta(meta), m_meta_type(meta_type) {
        get_app_args(m_meta, m_global_context);
    }

    expr operator()(expr eqns) {
        check_limitations(eqns);
        buffer<program> prgs;
        initialize(eqns, prgs);
        m_init_prgs.append(prgs);
        if (is_recursive(prgs)) {
            if (is_wf_equations(eqns)) {
                return compile_wf(prgs);
            } else {
                return compile_brec_on(prgs);
            }
        } else {
            lean_assert(prgs.size() == 1);
            return compile_pat_match(prgs[0], 0);
        }
    }
};

expr compile_equations(type_checker & tc, io_state const & ios, expr const & eqns,
                       expr const & meta, expr const & meta_type) {
    return equation_compiler_fn(tc, ios, meta, meta_type)(eqns);
}
}
