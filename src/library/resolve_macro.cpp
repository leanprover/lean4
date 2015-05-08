/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/interrupt.h"
#include "kernel/expr.h"
#include "kernel/justification.h"
#include "kernel/kernel_exception.h"
#include "kernel/free_vars.h"
#include "library/kernel_bindings.h"
#include "library/kernel_serializer.h"
#include "library/bin_app.h"
#include "library/constants.h"

namespace lean {
static name * g_resolve_macro_name    = nullptr;
static std::string * g_resolve_opcode = nullptr;
// Declarations used by the resolve_macro
static expr * g_or                    = nullptr;
static expr * g_not                   = nullptr;
static expr * g_false                 = nullptr;
static expr * g_or_elim               = nullptr;
static expr * g_or_intro_left         = nullptr;
static expr * g_or_intro_right        = nullptr;
static expr * g_absurd_elim           = nullptr;
static expr * g_var_0                 = nullptr;
/**
   \brief Resolve macro encodes a simple propositional resolution step.
   It takes three arguments:
            - t  : Prop
            - H1 : ( ... ∨ t ∨ ...)
            - H2 : ( ... ∨ (¬ t) ∨ ...)

   The resultant type is the propositional resolvent of the clauses proved by H1 and H2.
   For example:
            (resolve l ((A ∨ l) ∨ B) ((C ∨ A) ∨ (¬ l))) : (A ∨ (B ∨ C))

   The macro assumes the environment contains the declarations
            or (a b : Prop) : Prop
            not (a : Prop) : Prop
            false : Prop

   It also assumes that the symbol 'or' is opaque. 'not' and 'false' do not need to be opaque.

   The macro can be expanded into a term built using
            or.elim {a b c : Prop} (H1 : a ∨ b) (H2 : a → c) (H3 : b → c) : c
            or_intro_left {a : Prop} (H : a) (b : Prop) : a ∨ b
            or_intro_right {b : Prop} (a : Prop) (H : b) : a ∨ b
            absurd_elim {a : Prop} (b : Prop) (H1 : a) (H2 : ¬ a) : b
   Thus, the environment must also contain these declarations.

   Note that there is no classical reasoning being used. Thus, the macro can be used even
   in an environment where the classical axioms were not imported.

   When inferring the type, the macro will put literals in weak head normal form.
   It needs to do that to be able to check whether a term is a nested-or or not.

   The macro also assumes the literals occurring in the types of H1 and H2 are not
   metavariables.

   The resolve macro is mainly used by automation that produces resolution proofs.
   It may be used also by users to avoid tedious steps.
*/
class resolve_macro_definition_cell : public macro_definition_cell {
    simple_delayed_justification m_dummy_jst;
public:
    resolve_macro_definition_cell():m_dummy_jst([] { return mk_justification("resolve macro"); }) {
        // the delayed_justification may be accessed by different threads, thus we force its initialization.
        m_dummy_jst.get();
    }

    // The following const cast is say because we already initialized the delayed justification in the constructor.
    delayed_justification & jst() const { return const_cast<simple_delayed_justification&>(m_dummy_jst); }

    static void check_num_args(environment const & env, expr const & m) {
        lean_assert(is_macro(m));
        if (macro_num_args(m) != 3)
            throw_kernel_exception(env, "invalid number of arguments for resolve macro", m);
    }

    // ----------------------------------------------
    // Begin of resolve_macro get_type implementation
    // This section of code is trusted when the environment has trust_level == 1

    bool is_def_eq(expr const & l1, expr const & l2, extension_context & ctx) const {
        auto r = ctx.is_def_eq(l1, l2, jst());
        return r.first && !r.second;
    }

    expr whnf(expr const & e, extension_context & ctx) const {
        auto r = ctx.whnf(e);
        if (r.second)
            throw_kernel_exception(ctx.env(), "invalid resolve macro, constraints were generated while computing whnf", e);
        return r.first;
    }

    expr infer_type(expr const & e, extension_context & ctx, bool infer_only) const {
        auto r = ctx.check_type(e, infer_only);
        if (r.second)
            throw_kernel_exception(ctx.env(), "invalid resolve macro, constraints were generated while inferring type", e);
        return r.first;
    }

    /** \brief Return true if \c ls already contains a literal that is definitionally equal to \c l */
    bool already_contains(expr const & l, buffer<expr> const & ls, extension_context & ctx) const {
        for (expr const & old_l : ls) {
            if (is_def_eq(l, old_l, ctx))
                return true;
        }
        return false;
    }

    bool is_or(expr const & a, expr & lhs, expr & rhs) const { return is_bin_app(a, *g_or, lhs, rhs); }

    bool collect(expr const & lhs, expr const & rhs, expr const & l, buffer<expr> & R, extension_context & ctx) const {
        bool r1 = collect(lhs, l, R, ctx);
        bool r2 = collect(rhs, l, R, ctx);
        return r1 || r2;
    }

    bool collect(expr cls, expr const & l, buffer<expr> & R, extension_context & ctx) const {
        check_system("resolve macro");
        expr lhs, rhs;
        if (is_or(cls, lhs, rhs)) {
            return collect(lhs, rhs, l, R, ctx);
        } else {
            cls = whnf(cls, ctx);
            if (is_or(cls, lhs, rhs)) {
                return collect(lhs, rhs, l, R, ctx);
            } else if (is_def_eq(cls, l, ctx)) {
                return true; // found literal l
            } else {
                if (!already_contains(cls, R, ctx))
                    R.push_back(cls);
                return false;
            }
        }
    }

    expr mk_resolvent(environment const & env, extension_context & ctx, expr const & m,
                      expr const & l, expr const & not_l, expr const C1, expr const & C2) const {
        buffer<expr> R; // resolvent
        if (!collect(C1, l, R, ctx))
            throw_kernel_exception(env, "invalid resolve macro, positive literal was not found", m);
        if (!collect(C2, not_l, R, ctx))
            throw_kernel_exception(env, "invalid resolve macro, negative literal was not found", m);
        return mk_bin_rop(*g_or, *g_false, R.size(), R.data());
    }

    virtual pair<expr, constraint_seq> check_type(expr const & m, extension_context & ctx, bool infer_only) const {
        environment const & env = ctx.env();
        check_num_args(env, m);
        if (!infer_only)
            infer_type(macro_arg(m, 0), ctx, infer_only);
        expr l     = whnf(macro_arg(m, 0), ctx);
        expr not_l = whnf(mk_app(*g_not, l), ctx);
        expr C1    = infer_type(macro_arg(m, 1), ctx, infer_only);
        expr C2    = infer_type(macro_arg(m, 2), ctx, infer_only);
        return mk_pair(mk_resolvent(env, ctx, m, l, not_l, C1, C2), constraint_seq());
    }

    // End of resolve_macro get_type implementation
    // ----------------------------------------------

    // The following methods are not part of the TRUSTED code base
    // They are used when we set trust_level = 0.
    // In this case, the type checker invokes expand to double check that get_type
    // and the result returned by expand have the same type.

    virtual optional<expr> expand(expr const & m, extension_context & ctx) const {
        environment const & env = ctx.env();
        check_num_args(env, m);
        expr l     = whnf(macro_arg(m, 0), ctx);
        expr not_l = whnf(mk_app(*g_not, l), ctx);
        expr H1    = macro_arg(m, 1);
        expr H2    = macro_arg(m, 2);
        expr C1    = infer_type(H1, ctx, true);
        expr C2    = infer_type(H2, ctx, true);
        expr R     = mk_resolvent(env, ctx, m, l, not_l, C1, C2);
        return some_expr(mk_or_elim_tree1(l, not_l, C1, H1, C2, H2, R, ctx));
    }

    bool is_or_app(expr const & a) const { return is_bin_app(a, *g_or); }

    /** \brief Given l : H, and R == (or ... l ...), create a proof term for R using or_intro_left and or_intro_right */
    expr mk_or_intro(expr const & l, expr const & H, expr const & R, extension_context & ctx) const {
        check_system("resolve macro");
        if (is_or_app(R)) {
            expr lhs = app_arg(app_fn(R));
            expr rhs = app_arg(R);
            // or_intro_left {a : Prop} (H : a) (b : Prop) : a ∨ b
            // or_intro_right {b : Prop} (a : Prop) (H : b) : a ∨ b
            if (is_def_eq(l, lhs, ctx)) {
                return mk_app(*g_or_intro_left, l, H, rhs);
            } else if (is_def_eq(l, rhs, ctx)) {
                return mk_app(*g_or_intro_right, l, lhs, H);
            } else {
                return mk_app(*g_or_intro_right, rhs, lhs, mk_or_intro(l, H, rhs, ctx));
            }
        } else if (is_def_eq(l, R, ctx)) {
            return H;
        } else {
            throw_kernel_exception(ctx.env(), "bug in resolve macro");
        }
    }

    static expr lift(expr const & e) { return lift_free_vars(e, 1); }

    /**
       \brief Given
                  C1 : H1,  where C1 contains l
                  C2 : H2,  where C2 contains not_l
        Return a proof of the resolvent R of C1 and C2
    */
    expr mk_or_elim_tree1(expr const & l, expr const & not_l, expr C1, expr const & H1, expr const & C2, expr const & H2,
                          expr const & R, extension_context & ctx) const {
        check_system("resolve macro");
        expr lhs, rhs;
        if (is_or(C1, lhs, rhs)) {
            return mk_or_elim_tree1(l, not_l, lhs, rhs, H1, C2, H2, R, ctx);
        } else {
            C1 = whnf(C1, ctx);
            if (is_or(C1, lhs, rhs)) {
                return mk_or_elim_tree1(l, not_l, lhs, rhs, H1, C2, H2, R, ctx);
            } else if (is_def_eq(C1, l, ctx)) {
                return mk_or_elim_tree2(C1, H1, not_l, C2, H2, R, ctx);
            } else {
                return mk_or_intro(C1, H1, R, ctx);
            }
        }
    }

    /**
       \brief Given
                  (or lhs1 rhs1) : H1,  where lhs1 or rhs1 contain l
                  C2 : H2,              where C2 contains not_l
        Return a proof of the resolvent R of C1 and C2
    */
    expr mk_or_elim_tree1(expr const & l, expr const & not_l, expr const & lhs1, expr const & rhs1, expr const & H1,
                          expr const & C2, expr const & H2, expr const & R, extension_context & ctx) const {
        expr l_1     = lift(l);
        expr not_l_1 = lift(not_l);
        expr lhs1_1  = lift(lhs1);
        expr rhs1_1  = lift(rhs1);
        expr C2_1    = lift(C2);
        expr H2_1    = lift(H2);
        expr R_1     = lift(R);
        // or_elim {a b c : Prop} (H1 : a ∨ b) (H2 : a → c) (H3 : b → c) : c
        return mk_app({*g_or_elim,
                    lhs1, rhs1, R, H1,
                    mk_lambda("H2", lhs1, mk_or_elim_tree1(l_1, not_l_1, lhs1_1, *g_var_0, C2_1, H2_1, R_1, ctx)),
                    mk_lambda("H3", rhs1, mk_or_elim_tree1(l_1, not_l_1, rhs1_1, *g_var_0, C2_1, H2_1, R_1, ctx))});
    }

    /**
       Given
             l  : H
             C2 : H2, where C2 contains not_l
       produce a proof for R
    */
    expr mk_or_elim_tree2(expr const & l, expr const & H, expr const & not_l, expr C2, expr const & H2,
                          expr const & R, extension_context & ctx) const {
        check_system("resolve macro");
        expr lhs, rhs;
        if (is_or(C2, lhs, rhs)) {
            return mk_or_elim_tree2(l, H, not_l, lhs, rhs, H2, R, ctx);
        } else {
            C2 = whnf(C2, ctx);
            if (is_or(C2, lhs, rhs)) {
                return mk_or_elim_tree2(l, H, not_l, lhs, rhs, H2, R, ctx);
            } else if (is_def_eq(C2, not_l, ctx)) {
                // absurd_elim {a : Prop} (b : Prop) (H1 : a) (H2 : ¬ a) : b
                return mk_app(*g_absurd_elim, l, R, H, H2);
            } else {
                return mk_or_intro(C2, H2, R, ctx);
            }
        }
    }

    /**
       Given
             l              : H
             (or lhs2 rhs2) : H2,    where lhs2 or rhs2 contain not_l
       produce a proof for R
    */
    expr mk_or_elim_tree2(expr const & l, expr const & H, expr const & not_l,
                          expr const & lhs2, expr const & rhs2, expr const & H2,
                          expr const & R, extension_context & ctx) const {
        expr l_1     = lift(l);
        expr H_1     = lift(H);
        expr not_l_1 = lift(not_l);
        expr lhs2_1  = lift(lhs2);
        expr rhs2_1  = lift(rhs2);
        expr R_1     = lift(R);
        // or_elim {a b c : Prop} (H1 : a ∨ b) (H2 : a → c) (H3 : b → c) : c
        return mk_app({*g_or_elim,
                    lhs2, rhs2, R, H2,
                    mk_lambda("H2", lhs2, mk_or_elim_tree2(l_1, H_1, not_l_1, lhs2_1, *g_var_0, R_1, ctx)),
                    mk_lambda("H3", rhs2, mk_or_elim_tree2(l_1, H_1, not_l_1, rhs2_1, *g_var_0, R_1, ctx))});
    }

    virtual name get_name() const { return *g_resolve_macro_name; }
    /** \brief Resolve is a very simple macro, we can trust its implementation most of the time. */
    virtual unsigned trust_level() const { return 0; }
    virtual void write(serializer & s) const { s.write_string(*g_resolve_opcode); }
};

static macro_definition * g_resolve_macro_definition = nullptr;

expr mk_resolve_macro(expr const & l, expr const & H1, expr const & H2) {
    expr args[3] = {l, H1, H2};
    return mk_macro(*g_resolve_macro_definition, 3, args);
}

void initialize_resolve_macro() {
    g_resolve_macro_name = new name("resolve");
    g_resolve_opcode = new std::string("Res");
    g_or = new expr(Const(get_or_name()));
    g_not = new expr(Const(get_not_name()));
    g_false = new expr(Const(get_false_name()));
    g_or_elim = new expr(Const(get_or_elim_name()));
    g_or_intro_left = new expr(Const(get_or_intro_left_name()));
    g_or_intro_right = new expr(Const(get_or_intro_right_name()));
    g_absurd_elim = new expr(Const(get_absurd_name()));
    g_var_0 = new expr(mk_var(0));
    g_resolve_macro_definition = new macro_definition(new resolve_macro_definition_cell());
    register_macro_deserializer(*g_resolve_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 3)
                                        throw corrupted_stream_exception();
                                    return mk_resolve_macro(args[0], args[1], args[2]);
                                });
}

void finalize_resolve_macro() {
    delete g_resolve_macro_definition;
    delete g_var_0;
    delete g_absurd_elim;
    delete g_or_intro_right;
    delete g_or_intro_left;
    delete g_or_elim;
    delete g_false;
    delete g_not;
    delete g_or;
    delete g_resolve_opcode;
    delete g_resolve_macro_name;
}

static int mk_resolve_macro(lua_State * L) { return push_expr(L, mk_resolve_macro(to_expr(L, 1), to_expr(L, 2), to_expr(L, 3))); }
void open_resolve_macro(lua_State * L) {  SET_GLOBAL_FUN(mk_resolve_macro, "resolve_macro"); }
}
