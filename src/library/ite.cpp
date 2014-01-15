/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/builtin.h"
#include "kernel/abstract.h"
#include "kernel/decl_macros.h"
#include "library/ite.h"
#include "library/if_then_else_decls.cpp"
#include "library/kernel_bindings.h"

namespace lean {
// =======================================
// If-then-else builtin operator
static name   g_ite_name("ite");
static format g_ite_fmt(g_ite_name);
/**
   \brief Semantic attachment for if-then-else operator with type
   <code>Pi (A : Type), Bool -> A -> A -> A</code>
*/
class ite_fn_value : public value {
    expr m_type;
    static expr mk_type() {
        expr A    = Const("A");
        // Pi (A: Type), bool -> A -> A -> A
        return Pi({A, TypeU}, Bool >> (A >> (A >> A)));
    }
public:
    ite_fn_value():m_type(mk_type()) {}
    virtual ~ite_fn_value() {}
    virtual expr get_type() const { return m_type; }
    virtual name get_name() const { return g_ite_name; }
    virtual optional<expr> normalize(unsigned num_args, expr const * args) const {
        if (num_args == 5 && is_bool_value(args[2]) && is_value(args[3]) && is_value(args[4])) {
            if (to_bool(args[2]))
                return some_expr(args[3]); // if A true a b  --> a
            else
                return some_expr(args[4]); // if A false a b --> b
        } else {
            return none_expr();
        }
    }
    virtual void write(serializer & s) const { s << "ite"; }
};
MK_BUILTIN(ite_fn, ite_fn_value);
MK_IS_BUILTIN(is_ite_fn, mk_ite_fn());
static register_builtin_fn ite_blt("ite", []() { return mk_ite_fn(); });
static value::register_deserializer_fn ite_ds("ite", [](deserializer & ) { return mk_ite_fn(); });
// =======================================

void import_ite(environment const & env, io_state const & ios) {
    env->import("if_then_else", ios);
}

static int expr_mk_ite(lua_State * L) {
    return push_expr(L, mk_ite(to_expr(L, 1), to_expr(L, 2), to_expr(L, 3), to_expr(L, 4)));
}

void open_ite(lua_State * L) {
    SET_GLOBAL_FUN(expr_mk_ite,  "mk_ite");
}
}
