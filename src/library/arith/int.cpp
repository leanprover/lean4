/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/environment.h"
#include "library/arith/int.h"
#include "library/arith/nat.h"
#include "library/arith/num_type.h"

namespace lean {
/**
   \brief Semantic attachment for Int type.
*/
class int_type_value : public num_type_value {
public:
    int_type_value():num_type_value("Int", "\u2124") /* ℤ */ {}
};
expr const Int = mk_value(*(new int_type_value()));
expr mk_int_type() { return Int; }

class int_value_value : public value {
    mpz m_val;
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
    virtual format pp() const { return format(m_val); }
    virtual format pp(bool ) const { return pp(); }
    virtual unsigned hash() const { return m_val.hash(); }
    mpz const & get_num() const { return m_val; }
};

expr mk_int_value(mpz const & v) {
    return mk_value(*(new int_value_value(v)));
}

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
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3 && is_int_value(args[1]) && is_int_value(args[2])) {
            r = mk_int_value(F()(int_value_numeral(args[1]), int_value_numeral(args[2])));
            return true;
        } else {
            return false;
        }
    }
};

constexpr char int_add_name[] = "add";
struct int_add_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 + v2; }; };
typedef int_bin_op<int_add_name, int_add_eval> int_add_value;
MK_BUILTIN(int_add_fn, int_add_value);

constexpr char int_mul_name[] = "mul";
struct int_mul_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 * v2; }; };
typedef int_bin_op<int_mul_name, int_mul_eval> int_mul_value;
MK_BUILTIN(int_mul_fn, int_mul_value);

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

class int_le_value : public const_value {
public:
    int_le_value():const_value(name{"Int", "le"}, Int >> (Int >> Bool)) {}
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3 && is_int_value(args[1]) && is_int_value(args[2])) {
            r = mk_bool_value(int_value_numeral(args[1]) <= int_value_numeral(args[2]));
            return true;
        } else {
            return false;
        }
    }
};
MK_BUILTIN(int_le_fn, int_le_value);

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
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 2 && is_nat_value(args[1])) {
            r = mk_int_value(nat_value_numeral(args[1]));
            return true;
        } else {
            return false;
        }
    }
};
MK_BUILTIN(nat_to_int_fn, nat_to_int_value);

MK_CONSTANT(nat_sub_fn, name({"Nat", "sub"}));
MK_CONSTANT(nat_neg_fn, name({"Nat", "neg"}));

void import_int(environment & env) {
    if (env.find_object(to_value(Int).get_name()))
        return;
    import_nat(env);
    expr i_i  = Int >> Int;
    expr ii_b = Int >> (Int >> Bool);
    expr ii_i = Int >> (Int >> Int);
    expr x    = Const("x");
    expr y    = Const("y");

    env.add_builtin(Int);
    env.add_builtin_set(iVal(0));
    env.add_builtin(mk_int_add_fn());
    env.add_builtin(mk_int_mul_fn());
    env.add_builtin(mk_int_div_fn());
    env.add_builtin(mk_int_le_fn());
    env.add_builtin(mk_nat_to_int_fn());

    env.add_definition(int_sub_fn_name, ii_i, Fun({{x, Int}, {y, Int}}, iAdd(x, iMul(iVal(-1), y))));
    env.add_definition(int_neg_fn_name, i_i, Fun({x, Int}, iMul(iVal(-1), x)));
    env.add_definition(int_mod_fn_name, ii_i, Fun({{x, Int}, {y, Int}}, iSub(x, iMul(y, iDiv(x, y)))));
    env.add_definition(int_divides_fn_name, ii_b, Fun({{x, Int}, {y, Int}}, Eq(iMod(y, x), iVal(0))));
    env.add_definition(int_ge_fn_name, ii_b,  Fun({{x, Int}, {y, Int}}, iLe(y, x)));
    env.add_definition(int_lt_fn_name, ii_b,  Fun({{x, Int}, {y, Int}}, Not(iLe(y, x))));
    env.add_definition(int_gt_fn_name, ii_b,  Fun({{x, Int}, {y, Int}}, Not(iLe(x, y))));
    env.add_definition(int_abs_fn_name, i_i, Fun({x, Int}, iIf(iLe(iVal(0), x), x, iNeg(x))));

    env.add_definition(nat_sub_fn_name, Nat >> (Nat >> Int), Fun({{x, Nat}, {y, Nat}}, iSub(n2i(x), n2i(y))));
    env.add_definition(nat_neg_fn_name, Nat >> Int, Fun({x, Nat}, iNeg(n2i(x))));
}
}
