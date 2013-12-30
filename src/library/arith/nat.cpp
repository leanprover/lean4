/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/abstract.h"
#include "kernel/environment.h"
#include "kernel/value.h"
#include "kernel/io_state.h"
#include "kernel/decl_macros.h"
#include "library/kernel_bindings.h"
#include "library/arith/nat.h"

namespace lean {
MK_CONSTANT(Nat, "Nat");
expr const Nat = mk_Nat();
expr mk_nat_type() { return mk_Nat(); }

class nat_value_value : public value {
    mpz m_val;
protected:
    virtual bool lt(value const & other) const {
        return m_val < static_cast<nat_value_value const &>(other).m_val;
    }
public:
    nat_value_value(mpz const & v):m_val(v) { lean_assert(v >= 0); }
    virtual ~nat_value_value() {}
    virtual expr get_type() const { return Nat; }
    virtual name get_name() const { return name{"Nat", "numeral"}; }
    virtual bool operator==(value const & other) const {
        nat_value_value const * _other = dynamic_cast<nat_value_value const*>(&other);
        return _other && _other->m_val == m_val;
    }
    virtual void display(std::ostream & out) const { out << m_val; }
    virtual format pp() const { return format(m_val); }
    virtual format pp(bool, bool) const { return pp(); }
    virtual unsigned hash() const { return m_val.hash(); }
    virtual int push_lua(lua_State * L) const { return push_mpz(L, m_val); }
    mpz const & get_num() const { return m_val; }
    virtual void write(serializer & s) const { s << "nat" << m_val; }
};
expr mk_nat_value(mpz const & v) {
    return mk_value(*(new nat_value_value(v)));
}
static value::register_deserializer_fn nat_value_ds("nat", [](deserializer & d) { return mk_nat_value(read_mpz(d)); });
static register_builtin_fn nat_value_blt(name({"Nat", "numeral"}), []() { return mk_nat_value(mpz(0)); }, true);

bool is_nat_value(expr const & e) {
    return is_value(e) && dynamic_cast<nat_value_value const *>(&to_value(e)) != nullptr;
}

mpz const & nat_value_numeral(expr const & e) {
    lean_assert(is_nat_value(e));
    return static_cast<nat_value_value const &>(to_value(e)).get_num();
}

/**
   \brief Template for semantic attachments that are binary operators of
   the form Nat -> Nat -> Nat
*/
template<char const * Name, typename F>
class nat_bin_op : public const_value {
public:
    nat_bin_op():const_value(name("Nat", Name), Nat >> (Nat >> Nat)) {}
    virtual optional<expr> normalize(unsigned num_args, expr const * args) const {
        if (num_args == 3 && is_nat_value(args[1]) && is_nat_value(args[2])) {
            return some_expr(mk_nat_value(F()(nat_value_numeral(args[1]), nat_value_numeral(args[2]))));
        } else {
            return none_expr();
        }
    }
    virtual void write(serializer & s) const { s << (std::string("nat_") + Name); }
};

constexpr char nat_add_name[] = "add";
/** \brief Evaluator for + : Nat -> Nat -> Nat */
struct nat_add_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 + v2; }; };
typedef nat_bin_op<nat_add_name, nat_add_eval> nat_add_value;
MK_BUILTIN(nat_add_fn, nat_add_value);
static value::register_deserializer_fn nat_add_ds("nat_add", [](deserializer & ) { return mk_nat_add_fn(); });
static register_builtin_fn nat_add_blt(name({"Nat", "add"}), []() { return mk_nat_add_fn(); });

constexpr char nat_mul_name[] = "mul";
/** \brief Evaluator for * : Nat -> Nat -> Nat */
struct nat_mul_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 * v2; }; };
typedef nat_bin_op<nat_mul_name, nat_mul_eval> nat_mul_value;
MK_BUILTIN(nat_mul_fn, nat_mul_value);
static value::register_deserializer_fn nat_mul_ds("nat_mul", [](deserializer & ) { return mk_nat_mul_fn(); });
static register_builtin_fn nat_mul_blt(name({"Nat", "mul"}), []() { return mk_nat_mul_fn(); });

/**
   \brief Semantic attachment for less than or equal to operator with type
   <code>Nat -> Nat -> Bool</code>
*/
class nat_le_value : public const_value {
public:
    nat_le_value():const_value(name{"Nat", "le"}, Nat >> (Nat >> Bool)) {}
    virtual optional<expr> normalize(unsigned num_args, expr const * args) const {
        if (num_args == 3 && is_nat_value(args[1]) && is_nat_value(args[2])) {
            return some_expr(mk_bool_value(nat_value_numeral(args[1]) <= nat_value_numeral(args[2])));
        } else {
            return none_expr();
        }
    }
    virtual void write(serializer & s) const { s << "nat_le"; }
};
MK_BUILTIN(nat_le_fn, nat_le_value);
static value::register_deserializer_fn nat_le_ds("nat_le", [](deserializer & ) { return mk_nat_le_fn(); });
static register_builtin_fn nat_le_blt(name({"Nat", "le"}), []() { return mk_nat_le_fn(); });

MK_CONSTANT(nat_ge_fn,  name({"Nat", "ge"}));
MK_CONSTANT(nat_lt_fn,  name({"Nat", "lt"}));
MK_CONSTANT(nat_gt_fn,  name({"Nat", "gt"}));
MK_CONSTANT(nat_id_fn,  name({"Nat", "id"}));

void import_nat(environment const & env) {
    io_state ios;
    env->import("nat", ios);
}

static int mk_nat_value(lua_State * L) {
    mpz v = to_mpz_ext(L, 1);
    if (v < 0)
        throw exception("arg #1 must be non-negative");
    return push_expr(L, mk_nat_value(v));
}

void open_nat(lua_State * L) {
    SET_GLOBAL_FUN(mk_nat_value,     "mk_nat_value");
    SET_GLOBAL_FUN(mk_nat_value,     "nVal");
}
}
