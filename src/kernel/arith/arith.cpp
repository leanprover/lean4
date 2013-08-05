/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "builtin.h"
#include "arith.h"
#include "environment.h"

namespace lean {

class int_type_value : public value {
public:
    static char const * g_kind;
    virtual ~int_type_value() {}
    char const * kind() const { return g_kind; }
    virtual expr get_type() const { return type(level()); }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const { return false; }
    virtual bool operator==(value const & other) const { return other.kind() == kind(); }
    virtual void display(std::ostream & out) const { out << "int"; }
    virtual format pp() const { return format("int"); }
    virtual unsigned hash() const { return 41; }
};

char const * int_type_value::g_kind = "int";

MK_BUILTIN(int_type, int_type_value);

class int_value_value : public value {
    mpz m_val;
public:
    static char const * g_kind;
    int_value_value(mpz const & v):m_val(v) {}
    virtual ~int_value_value() {}
    char const * kind() const { return g_kind; }
    virtual expr get_type() const { return int_type(); }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const { return false; }
    virtual bool operator==(value const & other) const {
        return other.kind() == kind() && m_val == static_cast<int_value_value const &>(other).m_val;
    }
    virtual void display(std::ostream & out) const { out << m_val; }
    virtual format pp() const { return format(m_val); }
    virtual unsigned hash() const { return m_val.hash(); }
    mpz const & get_num() const { return m_val; }
};

char const * int_value_value::g_kind = "int_num";

expr int_value(mpz const & v) {
    return to_expr(*(new int_value_value(v)));
}

bool is_int_value(expr const & e) {
    return is_value(e) && to_value(e).kind() == int_value_value::g_kind;
}

mpz const & int_value_numeral(expr const & e) {
    lean_assert(is_int_value(e));
    return static_cast<int_value_value const &>(to_value(e)).get_num();
}

template<char const * Name, unsigned Hash, typename F>
class int_bin_op : public value {
public:
    static char const * g_kind;
    virtual ~int_bin_op() {}
    char const * kind() const { return g_kind; }
    virtual expr get_type() const {
        static thread_local expr r;
        if (!r)
            r = arrow(int_type(), arrow(int_type(), int_type()));
        return r;
    }
    virtual bool operator==(value const & other) const { return other.kind() == kind(); }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3 && is_int_value(args[1]) && is_int_value(args[2])) {
            r = int_value(F()(int_value_numeral(args[1]), int_value_numeral(args[2])));
            return true;
        } else {
            return false;
        }
    }
    virtual void display(std::ostream & out) const { out << Name; }
    virtual format pp() const { return format(Name); }
    virtual unsigned hash() const { return Hash; }
};

template<char const * Name, unsigned Hash, typename F> char const * int_bin_op<Name, Hash, F>::g_kind = Name;

constexpr char int_add_name[] = "+";
struct int_add_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 + v2; }; };
typedef int_bin_op<int_add_name, 43, int_add_eval> int_add_value;
MK_BUILTIN(int_add, int_add_value);

constexpr char int_sub_name[] = "-";
struct int_sub_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 - v2; }; };
typedef int_bin_op<int_sub_name, 47, int_sub_eval> int_sub_value;
MK_BUILTIN(int_sub, int_sub_value);

constexpr char int_mul_name[] = "*";
struct int_mul_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 * v2; }; };
typedef int_bin_op<int_mul_name, 53, int_mul_eval> int_mul_value;
MK_BUILTIN(int_mul, int_mul_value);

constexpr char int_div_name[] = "div";
struct int_div_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 / v2; }; };
typedef int_bin_op<int_div_name, 61, int_div_eval> int_div_value;
MK_BUILTIN(int_div, int_div_value);

class int_leq_value : public value {
public:
    static char const * g_kind;
    virtual ~int_leq_value() {}
    char const * kind() const { return g_kind; }
    virtual expr get_type() const {
        static thread_local expr r;
        if (!r)
            r = arrow(int_type(), arrow(int_type(), bool_type()));
        return r;
    }
    virtual bool operator==(value const & other) const { return other.kind() == kind(); }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3 && is_int_value(args[1]) && is_int_value(args[2])) {
            r = bool_value(int_value_numeral(args[1]) <= int_value_numeral(args[2]));
            return true;
        } else {
            return false;
        }
    }
    virtual void display(std::ostream & out) const { out << "<="; }
    virtual format pp() const { return format("<="); }
    virtual unsigned hash() const { return 67; }
};
char const * int_leq_value::g_kind = "<=";
MK_BUILTIN(int_leq, int_leq_value);

MK_CONSTANT(int_geq, name(name("int"), "geq"));
MK_CONSTANT(int_lt,  name(name("int"), "lt"));
MK_CONSTANT(int_gt,  name(name("int"), "gt"));

void add_int_theory(environment & env) {
    expr p = arrow(int_type(), arrow(int_type(), bool_type()));
    env.add_definition(int_geq_name_obj, p, lambda("x", int_type(), lambda("y", int_type(), app(int_leq(), var(0), var(1)))));
}

}
