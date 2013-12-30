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
#include "library/kernel_bindings.h"
#include "library/arith/int.h"
#include "library/arith/nat.h"

namespace lean {
MK_CONSTANT(Int, "Int");
expr const Int = mk_Int();
expr mk_int_type() { return mk_Int(); }

class int_value_value : public value {
    mpz m_val;
protected:
    virtual bool lt(value const & other) const {
        return m_val < static_cast<int_value_value const &>(other).m_val;
    }
public:
    int_value_value(mpz const & v):m_val(v) {}
    virtual ~int_value_value() {}
    virtual expr get_type() const { return Int; }
    virtual name get_name() const { return name{"Int", "numeral"}; }
    virtual bool operator==(value const & other) const {
        int_value_value const * _other = dynamic_cast<int_value_value const*>(&other);
        return _other && _other->m_val == m_val;
    }
    virtual void display(std::ostream & out) const { out << m_val; }
    virtual format pp() const { return pp(false, false); }
    virtual format pp(bool unicode, bool coercion) const {
        if (coercion && m_val >= 0)
            return format{to_value(mk_nat_to_int_fn()).pp(unicode, coercion), space(), format(m_val)};
        else
            return format(m_val);
    }
    virtual unsigned hash() const { return m_val.hash(); }
    virtual int push_lua(lua_State * L) const { return push_mpz(L, m_val); }
    mpz const & get_num() const { return m_val; }
    virtual void write(serializer & s) const { s << "int" << m_val; }
};

expr mk_int_value(mpz const & v) {
    return mk_value(*(new int_value_value(v)));
}
expr read_int_value(deserializer & d) { return mk_int_value(read_mpz(d)); }
static value::register_deserializer_fn int_value_ds("int", read_int_value);
static register_available_builtin_fn g_int_value(name({"Int", "numeral"}), []() { return mk_int_value(mpz(0)); }, true);

bool is_int_value(expr const & e) {
    return is_value(e) && dynamic_cast<int_value_value const *>(&to_value(e)) != nullptr;
}

mpz const & int_value_numeral(expr const & e) {
    lean_assert(is_int_value(e));
    return static_cast<int_value_value const &>(to_value(e)).get_num();
}

/**
   \brief Template for semantic attachments that are binary operators of
   the form Int -> Int -> Int
*/
template<char const * Name, typename F>
class int_bin_op : public const_value {
public:
    int_bin_op():const_value(name("Int", Name), Int >> (Int >> Int)) {}
    virtual optional<expr> normalize(unsigned num_args, expr const * args) const {
        if (num_args == 3 && is_int_value(args[1]) && is_int_value(args[2])) {
            return some_expr(mk_int_value(F()(int_value_numeral(args[1]), int_value_numeral(args[2]))));
        } else {
            return none_expr();
        }
    }
    virtual void write(serializer & s) const { s << (std::string("int_") + Name); }
};

constexpr char int_add_name[] = "add";
struct int_add_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 + v2; }; };
typedef int_bin_op<int_add_name, int_add_eval> int_add_value;
MK_BUILTIN(int_add_fn, int_add_value);
expr read_int_add(deserializer & ) { return mk_int_add_fn(); }
static value::register_deserializer_fn int_add_ds("int_add", read_int_add);
static register_available_builtin_fn g_int_add_value(name({"Int", "add"}), []() { return mk_int_add_fn(); });

constexpr char int_mul_name[] = "mul";
struct int_mul_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 * v2; }; };
typedef int_bin_op<int_mul_name, int_mul_eval> int_mul_value;
MK_BUILTIN(int_mul_fn, int_mul_value);
expr read_int_mul(deserializer & ) { return mk_int_mul_fn(); }
static value::register_deserializer_fn int_mul_ds("int_mul", read_int_mul);
static register_available_builtin_fn g_int_mul_value(name({"Int", "mul"}), []() { return mk_int_mul_fn(); });

constexpr char int_div_name[] = "div";
struct int_div_eval {
    mpz operator()(mpz const & v1, mpz const & v2) {
        if (v2.is_zero())
            return v2;
        else
            return v1 / v2;
    };
};
typedef int_bin_op<int_div_name, int_div_eval> int_div_value;
MK_BUILTIN(int_div_fn, int_div_value);
expr read_int_div(deserializer & ) { return mk_int_div_fn(); }
static value::register_deserializer_fn int_div_ds("int_div", read_int_div);
static register_available_builtin_fn g_int_div_value(name({"Int", "div"}), []() { return mk_int_div_fn(); });

class int_le_value : public const_value {
public:
    int_le_value():const_value(name{"Int", "le"}, Int >> (Int >> Bool)) {}
    virtual optional<expr> normalize(unsigned num_args, expr const * args) const {
        if (num_args == 3 && is_int_value(args[1]) && is_int_value(args[2])) {
            return some_expr(mk_bool_value(int_value_numeral(args[1]) <= int_value_numeral(args[2])));
        } else {
            return none_expr();
        }
    }
    virtual void write(serializer & s) const { s << "int_le"; }
};
MK_BUILTIN(int_le_fn, int_le_value);
expr read_int_le(deserializer & ) { return mk_int_le_fn(); }
static value::register_deserializer_fn int_le_ds("int_le", read_int_le);
static register_available_builtin_fn g_int_le_value(name({"Int", "le"}), []() { return mk_int_le_fn(); });

MK_CONSTANT(int_sub_fn, name({"Int", "sub"}));
MK_CONSTANT(int_neg_fn, name({"Int", "neg"}));
MK_CONSTANT(int_mod_fn, name({"Int", "mod"}));
MK_CONSTANT(int_divides_fn, name({"Int", "divides"}));
MK_CONSTANT(int_abs_fn, name({"Int", "abs"}));
MK_CONSTANT(int_ge_fn, name({"Int", "ge"}));
MK_CONSTANT(int_lt_fn, name({"Int", "lt"}));
MK_CONSTANT(int_gt_fn, name({"Int", "gt"}));

/**
   \brief Semantic attachment for the Nat to Int coercion.
*/
class nat_to_int_value : public const_value {
public:
    nat_to_int_value():const_value("nat_to_int", Nat >> Int) {}
    virtual optional<expr> normalize(unsigned num_args, expr const * args) const {
        if (num_args == 2 && is_nat_value(args[1])) {
            return some_expr(mk_int_value(nat_value_numeral(args[1])));
        } else {
            return none_expr();
        }
    }
    virtual void write(serializer & s) const { s << "nat_to_int"; }
};
MK_BUILTIN(nat_to_int_fn, nat_to_int_value);
expr read_nat_to_int(deserializer & ) { return mk_nat_to_int_fn(); }
static value::register_deserializer_fn nat_to_int_ds("nat_to_int", read_nat_to_int);
register_available_builtin_fn g_n2i_value(name({"nat_to_int"}), []() { return mk_nat_to_int_fn(); });

MK_CONSTANT(nat_sub_fn, name({"Nat", "sub"}));
MK_CONSTANT(nat_neg_fn, name({"Nat", "neg"}));

void import_int(environment const & env) {
    io_state ios;
    env->import("int", ios);
}

static int mk_int_value(lua_State * L) {
    return push_expr(L, mk_int_value(to_mpz_ext(L, 1)));
}

void open_int(lua_State * L) {
    SET_GLOBAL_FUN(mk_int_value,     "mk_int_value");
    SET_GLOBAL_FUN(mk_int_value,     "iVal");
}
}
