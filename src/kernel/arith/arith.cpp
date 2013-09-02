/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "builtin.h"
#include "arith.h"
#include "abstract.h"
#include "environment.h"

namespace lean {

class int_type_value : public value {
public:
    virtual ~int_type_value() {}
    virtual expr get_type() const { return Type(); }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const { return false; }
    virtual bool operator==(value const & other) const { return dynamic_cast<int_type_value const*>(&other) != nullptr; }
    virtual void display(std::ostream & out) const { out << "Int"; }
    virtual format pp() const { return format("Int"); }
    virtual unsigned hash() const { return 41; }
};
expr const Int = mk_value(*(new int_type_value()));
expr mk_int_type() { return Int; }

class int_value_value : public value {
    mpz m_val;
public:
    int_value_value(mpz const & v):m_val(v) {}
    virtual ~int_value_value() {}
    virtual expr get_type() const { return Int; }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const { return false; }
    virtual bool operator==(value const & other) const {
        int_value_value const * _other = dynamic_cast<int_value_value const*>(&other);
        return _other && _other->m_val == m_val;
    }
    virtual void display(std::ostream & out) const { out << m_val; }
    virtual format pp() const { return format(m_val); }
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

template<char const * Name, unsigned Hash, typename F>
class int_bin_op : public value {
    expr m_type;
public:
    int_bin_op() {
        m_type = Int >> (Int >> Int);
    }
    virtual ~int_bin_op() {}
    virtual expr get_type() const { return m_type; }
    virtual bool operator==(value const & other) const { return dynamic_cast<int_bin_op const*>(&other) != nullptr; }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3 && is_int_value(args[1]) && is_int_value(args[2])) {
            r = mk_int_value(F()(int_value_numeral(args[1]), int_value_numeral(args[2])));
            return true;
        } else {
            return false;
        }
    }
    virtual void display(std::ostream & out) const { out << Name; }
    virtual format pp() const { return format(Name); }
    virtual unsigned hash() const { return Hash; }
};

constexpr char int_add_name[] = "+";
struct int_add_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 + v2; }; };
typedef int_bin_op<int_add_name, 43, int_add_eval> int_add_value;
MK_BUILTIN(int_add_fn, int_add_value);

constexpr char int_sub_name[] = "-";
struct int_sub_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 - v2; }; };
typedef int_bin_op<int_sub_name, 47, int_sub_eval> int_sub_value;
MK_BUILTIN(int_sub_fn, int_sub_value);

constexpr char int_mul_name[] = "*";
struct int_mul_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 * v2; }; };
typedef int_bin_op<int_mul_name, 53, int_mul_eval> int_mul_value;
MK_BUILTIN(int_mul_fn, int_mul_value);

constexpr char int_div_name[] = "div";
struct int_div_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 / v2; }; };
typedef int_bin_op<int_div_name, 61, int_div_eval> int_div_value;
MK_BUILTIN(int_div_fn, int_div_value);

class int_le_value : public value {
    expr m_type;
public:
    int_le_value() {
        m_type = Int >> (Int >> Bool);
    }
    virtual ~int_le_value() {}
    virtual expr get_type() const { return m_type; }
    virtual bool operator==(value const & other) const { return dynamic_cast<int_le_value const*>(&other) != nullptr; }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3 && is_int_value(args[1]) && is_int_value(args[2])) {
            r = mk_bool_value(int_value_numeral(args[1]) <= int_value_numeral(args[2]));
            return true;
        } else {
            return false;
        }
    }
    virtual void display(std::ostream & out) const { out << "Le"; }
    virtual format pp() const { return format("Le"); }
    virtual unsigned hash() const { return 67; }
};
MK_BUILTIN(int_le_fn, int_le_value);

MK_CONSTANT(int_ge_fn, name(name("int"), "Ge"));
MK_CONSTANT(int_lt_fn, name(name("int"), "Lt"));
MK_CONSTANT(int_gt_fn, name(name("int"), "Gt"));

void add_int_theory(environment & env) {
    expr p    = Int >> (Int >> Bool);
    expr x    = Const("x");
    expr y    = Const("y");
    env.add_definition(int_ge_fn_name, p, Fun({{x, Int}, {y, Int}}, iLe(y, x)));
}
}
