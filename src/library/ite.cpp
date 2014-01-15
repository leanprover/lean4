/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/builtin.h"
#include "kernel/abstract.h"
#include "kernel/decl_macros.h"
#include "library/if_then_else_decls.h"
#include "library/if_then_else_decls.cpp"

namespace lean {
// =======================================
// If-then-else builtin operator
static name   g_if_name("ite");
static format g_if_fmt(g_if_name);
/**
   \brief Semantic attachment for if-then-else operator with type
   <code>Pi (A : Type), Bool -> A -> A -> A</code>
*/
class if_fn_value : public value {
    expr m_type;
    static expr mk_type() {
        expr A    = Const("A");
        // Pi (A: Type), bool -> A -> A -> A
        return Pi({A, TypeU}, Bool >> (A >> (A >> A)));
    }
public:
    if_fn_value():m_type(mk_type()) {}
    virtual ~if_fn_value() {}
    virtual expr get_type() const { return m_type; }
    virtual name get_name() const { return g_if_name; }
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
MK_BUILTIN(if_fn, if_fn_value);
MK_IS_BUILTIN(is_if_fn, mk_if_fn());
static register_builtin_fn if_blt("ite", []() { return mk_if_fn(); });
static value::register_deserializer_fn if_ds("ite", [](deserializer & ) { return mk_if_fn(); });
// =======================================

void import_ite(environment const & env, io_state const & ios) {
    env->import("if_then_else", ios);
}
}
