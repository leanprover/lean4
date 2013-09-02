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
/** \brief Base class for Nat, Int and Real types */
class num_type_value : public value {
    name m_name;
public:
    num_type_value(char const * name):m_name(name) {}
    virtual ~num_type_value() {}
    virtual expr get_type() const { return Type(); }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const { return false; }
    virtual void display(std::ostream & out) const { out << m_name; }
    virtual format pp() const { return format(m_name); }
    virtual unsigned hash() const { return m_name.hash(); }
};

// =======================================
// Natural numbers
class nat_type_value : public num_type_value {
public:
    nat_type_value():num_type_value("Nat") {}
    virtual bool operator==(value const & other) const { return dynamic_cast<nat_type_value const*>(&other) != nullptr; }
};
expr const Nat = mk_value(*(new nat_type_value()));
expr mk_nat_type() { return Nat; }

class nat_value_value : public value {
    mpz m_val;
public:
    nat_value_value(mpz const & v):m_val(v) { lean_assert(v >= 0); }
    virtual ~nat_value_value() {}
    virtual expr get_type() const { return Nat; }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const { return false; }
    virtual bool operator==(value const & other) const {
        nat_value_value const * _other = dynamic_cast<nat_value_value const*>(&other);
        return _other && _other->m_val == m_val;
    }
    virtual void display(std::ostream & out) const { out << m_val; }
    virtual format pp() const { return format(m_val); }
    virtual unsigned hash() const { return m_val.hash(); }
    mpz const & get_num() const { return m_val; }
};

expr mk_nat_value(mpz const & v) {
    return mk_value(*(new nat_value_value(v)));
}

bool is_nat_value(expr const & e) {
    return is_value(e) && dynamic_cast<nat_value_value const *>(&to_value(e)) != nullptr;
}

mpz const & nat_value_numeral(expr const & e) {
    lean_assert(is_nat_value(e));
    return static_cast<nat_value_value const &>(to_value(e)).get_num();
}

template<char const * Name, typename F>
class nat_bin_op : public value {
    expr     m_type;
    name     m_name;
public:
    nat_bin_op() {
        m_type = Nat >> (Nat >> Nat);
        m_name = name("Nat", Name);
    }
    virtual ~nat_bin_op() {}
    virtual expr get_type() const { return m_type; }
    virtual bool operator==(value const & other) const { return dynamic_cast<nat_bin_op const*>(&other) != nullptr; }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3 && is_nat_value(args[1]) && is_nat_value(args[2])) {
            r = mk_nat_value(F()(nat_value_numeral(args[1]), nat_value_numeral(args[2])));
            return true;
        } else {
            return false;
        }
    }
    virtual void display(std::ostream & out) const { out << m_name; }
    virtual format pp() const { return format(m_name); }
    virtual unsigned hash() const { return m_name.hash(); }
};

constexpr char nat_add_name[] = "add";
struct nat_add_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 + v2; }; };
typedef nat_bin_op<nat_add_name, nat_add_eval> nat_add_value;
MK_BUILTIN(nat_add_fn, nat_add_value);

constexpr char nat_mul_name[] = "mul";
struct nat_mul_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 * v2; }; };
typedef nat_bin_op<nat_mul_name, nat_mul_eval> nat_mul_value;
MK_BUILTIN(nat_mul_fn, nat_mul_value);

class nat_le_value : public value {
    expr m_type;
    name m_name;
public:
    nat_le_value() {
        m_type = Nat >> (Nat >> Bool);
        m_name = name{"Nat", "le"};
    }
    virtual ~nat_le_value() {}
    virtual expr get_type() const { return m_type; }
    virtual bool operator==(value const & other) const { return dynamic_cast<nat_le_value const*>(&other) != nullptr; }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3 && is_nat_value(args[1]) && is_nat_value(args[2])) {
            r = mk_bool_value(nat_value_numeral(args[1]) <= nat_value_numeral(args[2]));
            return true;
        } else {
            return false;
        }
    }
    virtual void display(std::ostream & out) const { out << m_name; }
    virtual format pp() const { return format(m_name); }
    virtual unsigned hash() const { return m_name.hash(); }
};
MK_BUILTIN(nat_le_fn, nat_le_value);

MK_CONSTANT(nat_ge_fn, name(name("Nat"), "ge"));
MK_CONSTANT(nat_lt_fn, name(name("Nat"), "lt"));
MK_CONSTANT(nat_gt_fn, name(name("Nat"), "gt"));
// =======================================

// =======================================
// Integers
class int_type_value : public num_type_value {
public:
    int_type_value():num_type_value("Int") {}
    virtual bool operator==(value const & other) const { return dynamic_cast<int_type_value const*>(&other) != nullptr; }
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

template<char const * Name, typename F>
class int_bin_op : public value {
    expr     m_type;
    name     m_name;
public:
    int_bin_op() {
        m_type = Int >> (Int >> Int);
        m_name = name("Int", Name);
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
    virtual void display(std::ostream & out) const { out << m_name; }
    virtual format pp() const { return format(m_name); }
    virtual unsigned hash() const { return m_name.hash(); }
};

constexpr char int_add_name[] = "add";
struct int_add_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 + v2; }; };
typedef int_bin_op<int_add_name, int_add_eval> int_add_value;
MK_BUILTIN(int_add_fn, int_add_value);

constexpr char int_sub_name[] = "sub";
struct int_sub_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 - v2; }; };
typedef int_bin_op<int_sub_name, int_sub_eval> int_sub_value;
MK_BUILTIN(int_sub_fn, int_sub_value);

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

class int_le_value : public value {
    expr m_type;
    name m_name;
public:
    int_le_value() {
        m_type = Int >> (Int >> Bool);
        m_name = name{"Int", "le"};
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
    virtual void display(std::ostream & out) const { out << m_name; }
    virtual format pp() const { return format(m_name); }
    virtual unsigned hash() const { return m_name.hash(); }
};
MK_BUILTIN(int_le_fn, int_le_value);
MK_CONSTANT(int_ge_fn, name(name("Int"), "ge"));
MK_CONSTANT(int_lt_fn, name(name("Int"), "lt"));
MK_CONSTANT(int_gt_fn, name(name("Int"), "gt"));

class nat_to_int_value : public value {
    expr m_type;
    name m_name;
public:
    nat_to_int_value() {
        m_type = Nat >> Int;
        m_name = "nat_to_int";
    }
    virtual ~nat_to_int_value() {}
    virtual expr get_type() const { return m_type; }
    virtual bool operator==(value const & other) const { return dynamic_cast<nat_to_int_value const*>(&other) != nullptr; }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 2 && is_nat_value(args[1])) {
            r = mk_int_value(nat_value_numeral(args[1]));
            return true;
        } else {
            return false;
        }
    }
    virtual void display(std::ostream & out) const { out << m_name; }
    virtual format pp() const { return format(m_name); }
    virtual unsigned hash() const { return m_name.hash(); }
};
MK_BUILTIN(nat_to_int_fn, nat_to_int_value);

// =======================================

void add_int_theory(environment & env) {
    expr p_ii = Int >> (Int >> Bool);
    expr p_nn = Nat >> (Nat >> Bool);
    expr x    = Const("x");
    expr y    = Const("y");

    env.add_definition(nat_ge_fn_name, p_nn, Fun({{x, Nat}, {y, Nat}}, nLe(y, x)));
    env.add_definition(nat_lt_fn_name, p_nn, Fun({{x, Nat}, {y, Nat}}, Not(nLe(y, x))));
    env.add_definition(nat_gt_fn_name, p_nn, Fun({{x, Nat}, {y, Nat}}, Not(nLe(x, y))));

    env.add_definition(int_ge_fn_name, p_ii, Fun({{x, Int}, {y, Int}}, iLe(y, x)));
    env.add_definition(int_lt_fn_name, p_ii, Fun({{x, Int}, {y, Int}}, Not(iLe(y, x))));
    env.add_definition(int_gt_fn_name, p_ii, Fun({{x, Int}, {y, Int}}, Not(iLe(x, y))));
}
}
