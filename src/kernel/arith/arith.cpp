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

MK_CONSTANT(nat_ge_fn, name({"Nat", "ge"}));
MK_CONSTANT(nat_lt_fn, name({"Nat", "lt"}));
MK_CONSTANT(nat_gt_fn, name({"Nat", "gt"}));
MK_CONSTANT(nat_sub_fn, name({"Nat", "sub"}));
MK_CONSTANT(nat_neg_fn, name({"Nat", "neg"}));
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

MK_CONSTANT(int_sub_fn, name({"Int", "sub"}));
MK_CONSTANT(int_neg_fn, name({"Int", "neg"}));
MK_CONSTANT(int_mod_fn, name({"Int", "mod"}));
MK_CONSTANT(int_ge_fn, name({"Int", "ge"}));
MK_CONSTANT(int_lt_fn, name({"Int", "lt"}));
MK_CONSTANT(int_gt_fn, name({"Int", "gt"}));
// =======================================

// =======================================
// Reals
class real_type_value : public num_type_value {
public:
    real_type_value():num_type_value("Real") {}
    virtual bool operator==(value const & other) const { return dynamic_cast<real_type_value const*>(&other) != nullptr; }
};
expr const Real = mk_value(*(new real_type_value()));
expr mk_real_type() { return Real; }

class real_value_value : public value {
    mpq m_val;
public:
    real_value_value(mpq const & v):m_val(v) {}
    virtual ~real_value_value() {}
    virtual expr get_type() const { return Real; }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const { return false; }
    virtual bool operator==(value const & other) const {
        real_value_value const * _other = dynamic_cast<real_value_value const*>(&other);
        return _other && _other->m_val == m_val;
    }
    virtual void display(std::ostream & out) const { out << m_val; }
    virtual format pp() const { return format(m_val); }
    virtual unsigned hash() const { return m_val.hash(); }
    mpq const & get_num() const { return m_val; }
};

expr mk_real_value(mpq const & v) {
    return mk_value(*(new real_value_value(v)));
}

bool is_real_value(expr const & e) {
    return is_value(e) && dynamic_cast<real_value_value const *>(&to_value(e)) != nullptr;
}

mpq const & real_value_numeral(expr const & e) {
    lean_assert(is_real_value(e));
    return static_cast<real_value_value const &>(to_value(e)).get_num();
}

template<char const * Name, typename F>
class real_bin_op : public value {
    expr     m_type;
    name     m_name;
public:
    real_bin_op() {
        m_type = Real >> (Real >> Real);
        m_name = name("Real", Name);
    }
    virtual ~real_bin_op() {}
    virtual expr get_type() const { return m_type; }
    virtual bool operator==(value const & other) const { return dynamic_cast<real_bin_op const*>(&other) != nullptr; }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3 && is_real_value(args[1]) && is_real_value(args[2])) {
            r = mk_real_value(F()(real_value_numeral(args[1]), real_value_numeral(args[2])));
            return true;
        } else {
            return false;
        }
    }
    virtual void display(std::ostream & out) const { out << m_name; }
    virtual format pp() const { return format(m_name); }
    virtual unsigned hash() const { return m_name.hash(); }
};

constexpr char real_add_name[] = "add";
struct real_add_eval { mpq operator()(mpq const & v1, mpq const & v2) { return v1 + v2; }; };
typedef real_bin_op<real_add_name, real_add_eval> real_add_value;
MK_BUILTIN(real_add_fn, real_add_value);

constexpr char real_mul_name[] = "mul";
struct real_mul_eval { mpq operator()(mpq const & v1, mpq const & v2) { return v1 * v2; }; };
typedef real_bin_op<real_mul_name, real_mul_eval> real_mul_value;
MK_BUILTIN(real_mul_fn, real_mul_value);

constexpr char real_div_name[] = "div";
struct real_div_eval {
    mpq operator()(mpq const & v1, mpq const & v2) {
        if (v2.is_zero())
            return v2;
        else
            return v1 / v2;
    };
};
typedef real_bin_op<real_div_name, real_div_eval> real_div_value;
MK_BUILTIN(real_div_fn, real_div_value);

class real_le_value : public value {
    expr m_type;
    name m_name;
public:
    real_le_value() {
        m_type = Real >> (Real >> Bool);
        m_name = name{"Real", "le"};
    }
    virtual ~real_le_value() {}
    virtual expr get_type() const { return m_type; }
    virtual bool operator==(value const & other) const { return dynamic_cast<real_le_value const*>(&other) != nullptr; }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3 && is_real_value(args[1]) && is_real_value(args[2])) {
            r = mk_bool_value(real_value_numeral(args[1]) <= real_value_numeral(args[2]));
            return true;
        } else {
            return false;
        }
    }
    virtual void display(std::ostream & out) const { out << m_name; }
    virtual format pp() const { return format(m_name); }
    virtual unsigned hash() const { return m_name.hash(); }
};
MK_BUILTIN(real_le_fn, real_le_value);

MK_CONSTANT(real_sub_fn, name({"Real", "sub"}));
MK_CONSTANT(real_neg_fn, name({"Real", "neg"}));
MK_CONSTANT(real_ge_fn, name({"Real", "ge"}));
MK_CONSTANT(real_lt_fn, name({"Real", "lt"}));
MK_CONSTANT(real_gt_fn, name({"Real", "gt"}));

MK_CONSTANT(exp_fn, name("exp"));
MK_CONSTANT(log_fn, name("log"));

MK_CONSTANT(real_pi, name("\u03C0")); // lower case pi
MK_CONSTANT(sin_fn, name("sin"));
MK_CONSTANT(cos_fn, name("cos"));
MK_CONSTANT(tan_fn, name("tan"));
MK_CONSTANT(cot_fn, name("cot"));
MK_CONSTANT(sec_fn, name("sec"));
MK_CONSTANT(csc_fn, name("csc"));

MK_CONSTANT(sinh_fn, name("sinh"));
MK_CONSTANT(cosh_fn, name("cosh"));
MK_CONSTANT(tanh_fn, name("tanh"));
MK_CONSTANT(coth_fn, name("coth"));
MK_CONSTANT(sech_fn, name("sech"));
MK_CONSTANT(csch_fn, name("csch"));
// =======================================

// =======================================
// Coercions
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

class int_to_real_value : public value {
    expr m_type;
    name m_name;
public:
    int_to_real_value() {
        m_type = Int >> Real;
        m_name = "int_to_real";
    }
    virtual ~int_to_real_value() {}
    virtual expr get_type() const { return m_type; }
    virtual bool operator==(value const & other) const { return dynamic_cast<int_to_real_value const*>(&other) != nullptr; }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 2 && is_int_value(args[1])) {
            r = mk_real_value(mpq(int_value_numeral(args[1])));
            return true;
        } else {
            return false;
        }
    }
    virtual void display(std::ostream & out) const { out << m_name; }
    virtual format pp() const { return format(m_name); }
    virtual unsigned hash() const { return m_name.hash(); }
};
MK_BUILTIN(int_to_real_fn,  int_to_real_value);
MK_CONSTANT(nat_to_real_fn, name("nat_to_real"));
// =======================================

void add_arith_theory(environment & env) {
    expr nn_b = Nat >> (Nat >> Bool);
    expr ii_b = Int >> (Int >> Bool);
    expr ii_i = Int >> (Int >> Int);
    expr rr_b = Real >> (Real >> Bool);
    expr rr_r = Real >> (Real >> Real);
    expr i_i  = Int >> Int;
    expr r_r  = Real >> Real;
    expr x    = Const("x");
    expr y    = Const("y");

    env.add_definition(nat_ge_fn_name, nn_b, Fun({{x, Nat}, {y, Nat}}, nLe(y, x)));
    env.add_definition(nat_lt_fn_name, nn_b, Fun({{x, Nat}, {y, Nat}}, Not(nLe(y, x))));
    env.add_definition(nat_gt_fn_name, nn_b, Fun({{x, Nat}, {y, Nat}}, Not(nLe(x, y))));

    env.add_definition(int_sub_fn_name, ii_i, Fun({{x, Int}, {y, Int}}, iAdd(x, iMul(mk_int_value(-1), y))));
    env.add_definition(int_neg_fn_name, i_i, Fun({x, Int}, iMul(mk_int_value(-1), x)));
    env.add_definition(int_mod_fn_name, ii_i, Fun({{x, Int}, {y, Int}}, iSub(x, iMul(y, iDiv(x, y)))));
    env.add_definition(int_ge_fn_name, ii_b,  Fun({{x, Int}, {y, Int}}, iLe(y, x)));
    env.add_definition(int_lt_fn_name, ii_b,  Fun({{x, Int}, {y, Int}}, Not(iLe(y, x))));
    env.add_definition(int_gt_fn_name, ii_b,  Fun({{x, Int}, {y, Int}}, Not(iLe(x, y))));

    env.add_definition(nat_sub_fn_name, Nat >> (Nat >> Int), Fun({{x, Nat}, {y, Nat}}, iSub(n2i(x), n2i(y))));
    env.add_definition(nat_neg_fn_name, Nat >> Int, Fun({x, Nat}, iNeg(n2i(x))));

    env.add_definition(real_sub_fn_name, rr_r, Fun({{x, Real}, {y, Real}}, rAdd(x, rMul(mk_real_value(-1), y))));
    env.add_definition(real_neg_fn_name, r_r, Fun({x, Real}, rMul(mk_real_value(-1), x)));
    env.add_definition(real_ge_fn_name, rr_b,  Fun({{x, Real}, {y, Real}}, rLe(y, x)));
    env.add_definition(real_lt_fn_name, rr_b,  Fun({{x, Real}, {y, Real}}, Not(rLe(y, x))));
    env.add_definition(real_gt_fn_name, rr_b,  Fun({{x, Real}, {y, Real}}, Not(rLe(x, y))));

    env.add_var(exp_fn_name, r_r);
    env.add_var(log_fn_name, r_r);

    env.add_var(real_pi_name, Real);
    env.add_definition(name("pi"), Real, mk_real_pi()); // alias for pi
    env.add_var(sin_fn_name, r_r);
    env.add_definition(cos_fn_name, r_r, Fun({x,Real}, Sin(rSub(x, rDiv(mk_real_pi(), mk_real_value(2))))));
    env.add_definition(tan_fn_name, r_r, Fun({x,Real}, rDiv(Sin(x), Cos(x))));
    env.add_definition(cot_fn_name, r_r, Fun({x,Real}, rDiv(Cos(x), Sin(x))));
    env.add_definition(sec_fn_name, r_r, Fun({x,Real}, rDiv(mk_real_value(1), Cos(x))));
    env.add_definition(csc_fn_name, r_r, Fun({x,Real}, rDiv(mk_real_value(1), Sin(x))));

    env.add_definition(sinh_fn_name, r_r, Fun({x, Real}, rDiv(rSub(mk_real_value(1), Exp(rMul(mk_real_value(-2), x))),
                                                              rMul(mk_real_value(2), Exp(rNeg(x))))));
    env.add_definition(cosh_fn_name, r_r, Fun({x, Real}, rDiv(rAdd(mk_real_value(1), Exp(rMul(mk_real_value(-2), x))),
                                                              rMul(mk_real_value(2), Exp(rNeg(x))))));
    env.add_definition(tanh_fn_name, r_r, Fun({x,Real}, rDiv(Sinh(x), Cosh(x))));
    env.add_definition(coth_fn_name, r_r, Fun({x,Real}, rDiv(Cosh(x), Sinh(x))));
    env.add_definition(sech_fn_name, r_r, Fun({x,Real}, rDiv(mk_real_value(1), Cosh(x))));
    env.add_definition(csch_fn_name, r_r, Fun({x,Real}, rDiv(mk_real_value(1), Sinh(x))));

    env.add_definition(nat_to_real_fn_name, Nat >> Real, Fun({x, Nat}, i2r(n2i(x))));
}
}
