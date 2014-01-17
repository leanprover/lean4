/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/kernel.h"
#include "kernel/environment.h"
#include "kernel/abstract.h"
#include "kernel/io_state.h"
#include "kernel/decl_macros.h"
#include "kernel/kernel_decls.cpp"

namespace lean {
// =======================================
// Bultin universe variables m and u
static level u_lvl(name("U"));
expr const TypeU = Type(u_lvl);
// =======================================

// =======================================
// Boolean Type
expr const Bool = mk_Bool();
expr mk_bool_type() { return mk_Bool(); }
bool is_bool(expr const & t) { return is_Bool(t); }
// =======================================

// =======================================
// Boolean values True and False
static name g_true_name("true");
static name g_false_name("false");
static name g_true_u_name("\u22A4"); // ⊤
static name g_false_u_name("\u22A5"); // ⊥
/**
   \brief Semantic attachments for Boolean values.
*/
class bool_value_value : public value {
    bool m_val;
public:
    bool_value_value(bool v):m_val(v) {}
    virtual ~bool_value_value() {}
    virtual expr get_type() const { return Bool; }
    virtual name get_name() const { return m_val ? g_true_name : g_false_name; }
    virtual name get_unicode_name() const { return m_val ? g_true_u_name : g_false_u_name; }
    // LCOV_EXCL_START
    virtual bool operator==(value const & other) const {
        // This method is unreachable because there is only one copy of True and False in the system,
        // and they have different hashcodes.
        bool_value_value const * _other = dynamic_cast<bool_value_value const*>(&other);
        return _other && _other->m_val == m_val;
    }
    // LCOV_EXCL_STOP
    virtual void write(serializer & s) const { s << (m_val ? "true" : "false"); }
    bool get_val() const { return m_val; }
};
expr const True  = mk_value(*(new bool_value_value(true)));
expr const False = mk_value(*(new bool_value_value(false)));
static register_builtin_fn true_blt("true", []() { return  True; });
static register_builtin_fn false_blt("false", []() { return False; });
static value::register_deserializer_fn true_ds("true", [](deserializer & ) { return True; });
static value::register_deserializer_fn false_ds("false", [](deserializer & ) { return False; });

expr mk_bool_value(bool v) {
    return v ? True : False;
}
bool is_bool_value(expr const & e) {
    return is_value(e) && dynamic_cast<bool_value_value const *>(&to_value(e)) != nullptr;
}
bool to_bool(expr const & e) {
    lean_assert(is_bool_value(e));
    return static_cast<bool_value_value const &>(to_value(e)).get_val();
}
bool is_true(expr const & e) {
    return is_bool_value(e) && to_bool(e);
}
bool is_false(expr const & e) {
    return is_bool_value(e) && !to_bool(e);
}
// =======================================

// =======================================
// Equality
static name   g_eq_name("eq");
static format g_eq_fmt(g_eq_name);
/**
   \brief Semantic attachment for if-then-else operator with type
   <code>Pi (A : Type), Bool -> A -> A -> A</code>
*/
class eq_fn_value : public value {
    expr m_type;
    static expr mk_type() {
        expr A    = Const("A");
        // Pi (A: TypeU), A -> A -> Bool
        return Pi({A, TypeU}, (A >> (A >> Bool)));
    }
public:
    eq_fn_value():m_type(mk_type()) {}
    virtual ~eq_fn_value() {}
    virtual expr get_type() const { return m_type; }
    virtual name get_name() const { return g_eq_name; }
    virtual optional<expr> normalize(unsigned num_args, expr const * args) const {
        if (num_args == 4 && is_value(args[2]) && is_value(args[3]) && typeid(to_value(args[2])) == typeid(to_value(args[3]))) {
            return some_expr(mk_bool_value(args[2] == args[3]));
        } else {
            return none_expr();
        }
    }
    virtual void write(serializer & s) const { s << "eq"; }
};
MK_BUILTIN(eq_fn, eq_fn_value);
MK_IS_BUILTIN(is_eq_fn, mk_eq_fn());
static register_builtin_fn eq_blt("eq", []() { return mk_eq_fn(); });
static value::register_deserializer_fn eq_ds("eq", [](deserializer & ) { return mk_eq_fn(); });
// =======================================


void import_kernel(environment const & env, io_state const & ios) {
    env->import("kernel", ios);
}
}
