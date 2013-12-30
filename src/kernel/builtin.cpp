/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/builtin.h"
#include "kernel/environment.h"
#include "kernel/abstract.h"

#ifndef LEAN_DEFAULT_LEVEL_SEPARATION
#define LEAN_DEFAULT_LEVEL_SEPARATION 512
#endif

namespace lean {
// =======================================
// Bultin universe variables m and u
static level m_lvl(name("M"));
static level u_lvl(name("U"));
expr const TypeM = Type(m_lvl);
expr const TypeU = Type(u_lvl);
// =======================================

// =======================================
// Boolean Type
MK_CONSTANT(Bool, "Bool");
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
expr read_true(deserializer & ) { return True; }
expr read_false(deserializer & ) { return False; }
static value::register_deserializer_fn true_ds("true", read_true);
static value::register_deserializer_fn false_ds("false", read_false);
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
// If-then-else builtin operator
static name   g_if_name("if");
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
        if (num_args == 5 && is_bool_value(args[2])) {
            if (to_bool(args[2]))
                return some_expr(args[3]); // if A true a b  --> a
            else
                return some_expr(args[4]); // if A false a b --> b
        } else {
            return none_expr();
        }
    }
    virtual void write(serializer & s) const { s << "if"; }
};
MK_BUILTIN(if_fn, if_fn_value);
expr read_if(deserializer & ) { return mk_if_fn(); }
static value::register_deserializer_fn if_ds("if", read_if);
MK_IS_BUILTIN(is_if_fn, mk_if_fn());
// =======================================

MK_CONSTANT(implies_fn, name("implies"));
MK_CONSTANT(iff_fn,     name("iff"));
MK_CONSTANT(and_fn,     name("and"));
MK_CONSTANT(or_fn,      name("or"));
MK_CONSTANT(not_fn,     name("not"));
MK_CONSTANT(forall_fn,  name("forall"));
MK_CONSTANT(exists_fn,  name("exists"));
MK_CONSTANT(homo_eq_fn, name("eq"));
// Axioms
MK_CONSTANT(mp_fn,          name("MP"));
MK_CONSTANT(discharge_fn,   name("Discharge"));
MK_CONSTANT(case_fn,        name("Case"));
MK_CONSTANT(refl_fn,        name("Refl"));
MK_CONSTANT(subst_fn,       name("Subst"));
MK_CONSTANT(eta_fn,         name("Eta"));
MK_CONSTANT(imp_antisym_fn, name("ImpAntisym"));
MK_CONSTANT(abst_fn,        name("Abst"));

MK_CONSTANT(htrans_fn,      name("HTrans"));
MK_CONSTANT(hsymm_fn,       name("HSymm"));

void import_kernel(environment const & env) {
    env->import_builtin
        ("kernel",
         [&]() {
            env->add_var(Bool_name, Type());
            env->add_uvar(uvar_name(m_lvl), level() + LEAN_DEFAULT_LEVEL_SEPARATION);
            env->add_uvar(uvar_name(u_lvl), m_lvl + LEAN_DEFAULT_LEVEL_SEPARATION);
            env->add_builtin(mk_bool_value(true));
            env->add_builtin(mk_bool_value(false));
            env->add_builtin(mk_if_fn());
        });
}
}
