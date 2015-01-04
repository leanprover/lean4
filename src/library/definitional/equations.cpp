/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
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
#include "library/generic_exception.h"
#include "library/kernel_serializer.h"
#include "library/io_state_stream.h"
#include "library/annotation.h"
#include "library/util.h"
#include "library/locals.h"
#include "library/tactic/inversion_tactic.h"

namespace lean {
static name * g_equations_name    = nullptr;
static name * g_equation_name     = nullptr;
static name * g_decreasing_name   = nullptr;
static name * g_inaccessible_name = nullptr;
static std::string * g_equations_opcode  = nullptr;
static std::string * g_equation_opcode   = nullptr;
static std::string * g_decreasing_opcode = nullptr;

[[ noreturn ]] static void throw_eqs_ex() { throw exception("unexpected occurrence of 'equations' expression"); }
[[ noreturn ]] static void throw_eq_ex() { throw exception("unexpected occurrence of 'equation' expression"); }

class equations_macro_cell : public macro_definition_cell {
    unsigned m_num_fns;
public:
    equations_macro_cell(unsigned num_fns):m_num_fns(num_fns) {}
    virtual name get_name() const { return *g_equations_name; }
    virtual pair<expr, constraint_seq> get_type(expr const &, extension_context &) const { throw_eqs_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_eqs_ex(); }
    virtual void write(serializer & s) const { s << *g_equations_opcode << m_num_fns; }
    unsigned get_num_fns() const { return m_num_fns; }
};

class equation_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_equation_name; }
    virtual pair<expr, constraint_seq> get_type(expr const &, extension_context &) const {
        expr dummy = mk_Prop();
        return mk_pair(dummy, constraint_seq());
    }
    virtual optional<expr> expand(expr const &, extension_context &) const {
        expr dummy = mk_Type();
        return some_expr(dummy);
    }
    virtual void write(serializer & s) const { s.write_string(*g_equation_opcode); }
};

class decreasing_macro_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 2)
            throw exception("invalid 'decreasing' expression, incorrect number of arguments");
    }
public:
    decreasing_macro_cell() {}
    virtual name get_name() const { return *g_decreasing_name; }
    virtual pair<expr, constraint_seq> get_type(expr const & m, extension_context & ctx) const {
        check_macro(m);
        return ctx.infer_type(macro_arg(m, 0));
    }
    virtual optional<expr> expand(expr const & m, extension_context &) const {
        check_macro(m);
        return some_expr(macro_arg(m, 0));
    }
    virtual void write(serializer & s) const { s.write_string(*g_decreasing_opcode); }
};

static macro_definition * g_equation   = nullptr;
static macro_definition * g_decreasing = nullptr;

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
    lean_assert(std::all_of(eqs, eqs+num_eqs, is_lambda_equation));
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

void initialize_equations() {
    g_equations_name    = new name("equations");
    g_equation_name     = new name("equation");
    g_decreasing_name   = new name("decreasing");
    g_inaccessible_name = new name("innaccessible");
    g_equation          = new macro_definition(new equation_macro_cell());
    g_decreasing        = new macro_definition(new decreasing_macro_cell());
    g_equations_opcode  = new std::string("Eqns");
    g_equation_opcode   = new std::string("Eqn");
    g_decreasing_opcode = new std::string("Decr");
    register_annotation(*g_inaccessible_name);
    register_macro_deserializer(*g_equations_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    unsigned num_fns;
                                    d >> num_fns;
                                    if (num == 0 || num_fns == 0)
                                        throw corrupted_stream_exception();
                                    if (!is_lambda_equation(args[num-1])) {
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
    register_macro_deserializer(*g_decreasing_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 2)
                                        throw corrupted_stream_exception();
                                    return mk_decreasing(args[0], args[1]);
                                });
}

void finalize_equations() {
    delete g_equation_opcode;
    delete g_equations_opcode;
    delete g_decreasing_opcode;
    delete g_equation;
    delete g_decreasing;
    delete g_equations_name;
    delete g_equation_name;
    delete g_decreasing_name;
    delete g_inaccessible_name;
}

class equation_compiler_fn {
    type_checker &   m_tc;
    io_state const & m_ios;
    expr             m_meta;
    expr             m_meta_type;
    bool             m_relax;
    buffer<expr>     m_global_context;
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
    [[ noreturn ]] static void throw_error(expr const & src, pp_fn const & fn) { throw_generic_exception(src, fn); }
    [[ noreturn ]] void throw_error(sstream const & ss) const { throw_generic_exception(ss, m_meta); }

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
        program(program const & p, list<optional<name>> const & new_s, list<eqn> const & new_e):
            program(p.m_fn, p.m_context, new_s, new_e, p.m_type) {}
        program(program const & p, list<expr> const & ctx):
            program(p.m_fn, ctx, p.m_var_stack, p.m_eqns, p.m_type) {}
        program() {}
        expr const & get_var(name const & n) const {
            for (expr const & v : m_context) {
                if (mlocal_name(v) == n)
                    return v;
            }
            lean_unreachable();
        }
    };

#ifdef LEAN_DEBUG
    // For debugging purposes: checks whether all local constants occurring in \c e
    // are in local_ctx or m_global_context
    bool check_ctx(expr const & e, list<expr> const & context, list<expr> const & local_context) const {
        for_each(e, [&](expr const & e, unsigned) {
                if (is_local(e) &&
                    !(contains_local(e, local_context) ||
                      contains_local(e, context) ||
                      contains_local(e, m_global_context) ||
                      contains_local(e, m_fns))) {
                    lean_unreachable();
                    return false;
                }
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

    // Initialize the variable stack for each function that needs
    // to be compiled.
    // This method assumes m_fns has been already initialized.
    // This method also initialized the buffer prg, but the eqns
    // field of each program is not initialized by it.
    void initialize_var_stack(buffer<program> & prgs) {
        lean_assert(!m_fns.empty());
        lean_assert(prgs.empty());
        for (expr const & fn : m_fns) {
            buffer<expr> args;
            expr r_type       = to_telescope(mlocal_type(fn), args);
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

    // Validate/normalize the given pattern.
    // It stores in reachable_vars any variable that does not occur
    // in inaccessible terms.
    expr validate_pattern(expr pat, name_set & reachable_vars) {
        if (is_inaccessible(pat))
            return pat;
        if (is_local(pat)) {
            reachable_vars.insert(mlocal_name(pat));
            return pat;
        }
        expr new_pat = whnf(pat);
        if (is_local(new_pat)) {
            reachable_vars.insert(mlocal_name(new_pat));
            return new_pat;
        }
        buffer<expr> pat_args;
        expr const & fn = get_app_args(new_pat, pat_args);
        if (auto in = is_constructor(fn)) {
            unsigned num_params = *inductive::get_num_params(env(), *in);
            for (unsigned i = num_params; i < pat_args.size(); i++)
                pat_args[i] = validate_pattern(pat_args[i], reachable_vars);
            return mk_app(fn, pat_args);
        } else {
            throw validate_exception(pat);
        }
    }

    // Validate/normalize the patterns associated with the given lhs.
    // The lhs is only used to report errors.
    // It stores in reachable_vars any variable that does not occur
    // in inaccessible terms.
    void validate_patterns(expr const & lhs, buffer<expr> & patterns, name_set & reachable_vars) {
        for (expr & pat : patterns) {
            try {
                pat = validate_pattern(pat, reachable_vars);
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
        initialize_fns(eqns);
        initialize_var_stack(prg);
        buffer<expr> eqs;
        to_equations(eqns, eqs);
        buffer<buffer<eqn>> res_eqns;
        res_eqns.resize(m_fns.size());
        for (expr eq : eqs) {
            for (expr const & fn : m_fns)
                eq = instantiate(binding_body(eq), fn);
            buffer<expr> local_ctx;
            eq = fun_to_telescope(eq, local_ctx);
            expr const & lhs = equation_lhs(eq);
            expr const & rhs = equation_rhs(eq);
            buffer<expr> patterns;
            expr const & fn  = get_app_args(lhs, patterns);
            name_set reachable_vars;
            validate_patterns(lhs, patterns, reachable_vars);
            for (expr const & v : local_ctx) {
                // every variable in the local_ctx must be "reachable".
                if (!reachable_vars.contains(mlocal_name(v))) {
                    throw_error(lhs, [=](formatter const & fmt) {
                            format r("invalid equation left-hand-side, variable '");
                            r += format(local_pp_name(v));
                            r += format("' only occurs in inaccessible terms in the following equation left-hand-side");
                            r += pp_indent_expr(fmt, lhs);
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

    // Return true iff the next pattern in all equations is a constructor
    bool is_constructor_transition(program const & p) const {
        for (eqn const & e : p.m_eqns) {
            lean_assert(e.m_patterns);
            if (!is_constructor(get_app_fn(head(e.m_patterns))))
                return false;
        }
        return true;
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

    // Replace local constant \c from with \c to in the expression \c e.
    static expr replace(expr const & e, expr const & from, expr const & to) {
        return instantiate(abstract_local(e, from), to);
    }

    static expr replace(expr const & e, name const & from, expr const & to) {
        return instantiate(abstract_local(e, from), to);
    }

    static expr replace(expr const & e, name_map<expr> const & subst) {
        expr r = e;
        subst.for_each([&](name const & l, expr const & v) {
                r = replace(r, l, v);
            });
        return r;
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
                    list<expr> new_local_ctx = e.m_local_context;
                    new_local_ctx      = remove(new_local_ctx, p);
                    new_local_ctx      = map(new_local_ctx, [&](expr const & l) { return replace(l, p, x); });
                    auto new_patterns  = map(tail(e.m_patterns), [&](expr const & p2) { return replace(p2, p, x); });
                    auto new_rhs       = replace(e.m_rhs, p, x);
                    new_eqs.emplace_back(new_local_ctx, new_patterns, new_rhs);
                } else {
                    new_eqs.emplace_back(e.m_local_context, tail(e.m_patterns), e.m_rhs);
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
    program to_program(expr const & fn, goal const & g, unsigned nvars, list<optional<name>> const & new_var_stack, inversion::implementation_list const & imps) {
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

    expr compile_constructor(program const & p) {
        expr h                    = p.get_var(*head(p.m_var_stack));
        goal g                    = to_goal(p);
        auto imps                 = to_implementation_list(p);
        if (auto r = apply(env(), ios(), m_tc, g, h, imps)) {
            substitution subst       = r->m_subst;
            list<list<expr>> args    = r->m_args;
            list<rename_map> rn_maps = r->m_renames;
            list<inversion::implementation_list> imps_list = r->m_implementation_lists;
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
                                                         [&](optional<name> const & n) {
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
                subst.assign(new_g.get_name(), new_g.abstract(t));
            }
            expr t = subst.instantiate_all(g.get_meta());
            // out() << "RESULT: " << t << "\n";
            return t;
        } else {
            throw_error(sstream() << "patter matching failed");
        }
    }

    expr compile_complete(program const & /* p */) {
        // The next pattern of every equation is a constructor or variable.
        // We split the equations where the next pattern is a variable into cases.
        // That is, we are reducing this case to the compile_constructor case.

        // TODO(Leo)
        return expr();
    }

    expr compile_core(program const & p) {
        lean_assert(check_program(p));
        // out() << "compile_core step\n";
        // display(p);
        // out() << "------------------\n";
        if (p.m_var_stack) {
            if (!head(p.m_var_stack)) {
                return compile_skip(p);
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
                throw_error(sstream() << "invalid non-exhaustive set of recursive equations");
            }
        }
    }

    expr compile_pat_match(program const & p) {
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
                get_app_args(I, args);
                return
                    all_distinct_locals(nindices, args.end() - nindices) &&
                    std::all_of(args.end() - nindices, args.end(), [&](expr const & idx) { return contains_local(idx, ctx); });
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

    expr compile_brec_on(buffer<program> & prgs) {
        lean_assert(!prgs.empty());
        buffer<unsigned> arg_pos;
        if (!find_rec_args(prgs, arg_pos)) {
            throw_error(sstream() << "invalid recursive equations, failed to find recursive arguments that are structurally smaller "
                        << "(possible solution: use well-founded recursion)");
        }

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

        // Distribute parameters of the ith program intro three groups:
        //    indices, major premise (arg), and remaining arguments (rest)
        auto distribute_context = [&](unsigned i, buffer<expr> & indices, expr & arg, buffer<expr> & rest) {
            program const & p      = prgs[i];
            arg                    = get_rec_arg(i);
            list<expr> const & ctx = p.m_context;
            buffer<expr> arg_args;
            get_app_args(mlocal_type(arg), arg_args);
            lean_assert(nparams <= arg_args.size());
            indices.append(arg_args.size() - nparams, arg_args.data() + nparams);
            for (expr const & l : ctx) {
                if (mlocal_name(l) != mlocal_name(arg) && !contains_local(l, indices))
                    rest.push_back(l);
            }
        };

        // Compute the resulting universe level for brec_on
        auto get_brec_on_result_level = [&]() -> level {
            buffer<expr> indices, rest;
            expr arg;
            distribute_context(0, indices, arg, rest);
            expr r_type = Pi(indices, prgs[0].m_type);
            return sort_level(m_tc.ensure_type(r_type).first);
        };

        level rlvl          = get_brec_on_result_level();
        levels brec_on_lvls = cons(rlvl, const_levels(I0));
        expr brec_on        = mk_constant(name{const_name(I0), "brec_on"}, brec_on_lvls);
        buffer<expr> params;
        // add parameters
        for (unsigned i = 0; i < nparams; i++) {
            params.push_back(a0_type_args[i]);
            brec_on = mk_app(brec_on, a0_type_args[i]);
        }

        buffer<expr> Cs; // brec_on "motives"
        buffer<buffer<expr>> C_args_buffer;
        for (inductive::inductive_decl const & decl : decls) {
            name const & I_name = inductive::inductive_decl_name(decl);
            expr C;
            C_args_buffer.push_back(buffer<expr>());
            buffer<expr> & C_args = C_args_buffer.back();
            if (optional<unsigned> p_idx = get_prg_for(I_name)) {
                buffer<expr> indices, rest; expr arg;
                distribute_context(*p_idx, indices, arg, rest);
                expr type = Pi(rest, prgs[*p_idx].m_type);
                C_args.append(indices);
                C_args.push_back(arg);
                C = Fun(C_args, type);
            } else {
                expr type = whnf(infer_type(brec_on));
                expr d    = binding_domain(type);
                expr unit = mk_constant("unit", rlvl);
                to_telescope_ext(d, C_args);
                C = Fun(C_args, unit);
            }
            brec_on = mk_app(brec_on, C);
            Cs.push_back(C);
        }

        // add functionals
        unsigned i = 0;
        for (inductive::inductive_decl const & decl : decls) {
            name const & I_name = inductive::inductive_decl_name(decl);
            expr below = mk_constant(name{I_name, "below"}, brec_on_lvls);
            below      = mk_app(mk_app(below, params), Cs);
            expr F;
            buffer<expr> & C_args = C_args_buffer[i];
            if (optional<unsigned> p_idx = get_prg_for(I_name)) {
                program & prg_i = prgs[*p_idx];
                buffer<expr> indices, rest; expr arg;
                distribute_context(*p_idx, indices, arg, rest);
                below           = mk_app(mk_app(below, indices), arg);
                expr b          = mk_local(mk_fresh_name(), "b", below, binder_info());
                buffer<expr> new_ctx;
                new_ctx.append(indices);
                new_ctx.push_back(arg);
                new_ctx.push_back(b);
                new_ctx.append(rest);
                prg_i.m_context = to_list(new_ctx);
                // TODO(Leo): replace recursive calls with "b" applications
                F               = compile_pat_match(prg_i);
            } else {
                expr star    = mk_constant(name{"unit", "star"}, rlvl);
                buffer<expr> F_args;
                F_args.append(C_args);
                below        = mk_app(below, F_args);
                F_args.push_back(mk_local(mk_fresh_name(), "b", below, binder_info()));
                F = Fun(F_args, star);
            }
            brec_on = mk_app(brec_on, F);
            i++;
        }

        // out() << "brec_on: " << brec_on << "\n";

        return brec_on;
    }

    expr compile_wf(buffer<program> & /* prgs */) {
        // TODO(Leo)
        return expr();
    }


public:
    equation_compiler_fn(type_checker & tc, io_state const & ios, expr const & meta, expr const & meta_type, bool relax):
        m_tc(tc), m_ios(ios), m_meta(meta), m_meta_type(meta_type), m_relax(relax) {
        get_app_args(m_meta, m_global_context);
    }

    expr operator()(expr eqns) {
        check_limitations(eqns);
        // out() << "Equations:\n" << eqns << "\n";
        buffer<program> prgs;
        initialize(eqns, prgs);
        if (is_recursive(prgs)) {
            if (is_wf_equations(eqns)) {
                return compile_wf(prgs);
            } else {
                return compile_brec_on(prgs);
            }
        } else {
            lean_assert(prgs.size() == 1);
            return compile_pat_match(prgs[0]);
        }
    }
};

expr compile_equations(type_checker & tc, io_state const & ios, expr const & eqns,
                       expr const & meta, expr const & meta_type, bool relax) {
    return equation_compiler_fn(tc, ios, meta, meta_type, relax)(eqns);
}
}
