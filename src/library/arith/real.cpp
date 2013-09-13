/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/environment.h"
#include "library/arith/real.h"
#include "library/arith/int.h"
#include "library/arith/nat.h"
#include "library/arith/num_type.h"

namespace lean {
class real_type_value : public num_type_value {
public:
    real_type_value():num_type_value("Real", "\u211D") /* ℝ */ {}
};
expr const Real = mk_value(*(new real_type_value()));
expr mk_real_type() { return Real; }

/**
   \brief Semantic attachment for "Real" values.
   It is actually for rational values. We should eventually rename it to
   rat_value_value
*/
class real_value_value : public value {
    mpq m_val;
public:
    real_value_value(mpq const & v):m_val(v) {}
    virtual ~real_value_value() {}
    virtual expr get_type() const { return Real; }
    virtual name get_name() const { return name{"Real", "numeral"}; }
    virtual bool operator==(value const & other) const {
        real_value_value const * _other = dynamic_cast<real_value_value const*>(&other);
        return _other && _other->m_val == m_val;
    }
    virtual void display(std::ostream & out) const { out << m_val; }
    virtual format pp() const { return format(m_val); }
    virtual format pp(bool unicode) const { return pp(); }
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

/**
   \brief Template for semantic attachments that are binary operators of
   the form Real -> Real -> Real
*/
template<char const * Name, typename F>
class real_bin_op : public const_value {
public:
    real_bin_op():const_value(name("Real", Name), Real >> (Real >> Real)) {}
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3 && is_real_value(args[1]) && is_real_value(args[2])) {
            r = mk_real_value(F()(real_value_numeral(args[1]), real_value_numeral(args[2])));
            return true;
        } else {
            return false;
        }
    }
};

constexpr char real_add_name[] = "add";
/** \brief Evaluator for + : Real -> Real -> Real */
struct real_add_eval { mpq operator()(mpq const & v1, mpq const & v2) { return v1 + v2; }; };
typedef real_bin_op<real_add_name, real_add_eval> real_add_value;
MK_BUILTIN(real_add_fn, real_add_value);

constexpr char real_mul_name[] = "mul";
/** \brief Evaluator for * : Real -> Real -> Real */
struct real_mul_eval { mpq operator()(mpq const & v1, mpq const & v2) { return v1 * v2; }; };
typedef real_bin_op<real_mul_name, real_mul_eval> real_mul_value;
MK_BUILTIN(real_mul_fn, real_mul_value);

constexpr char real_div_name[] = "div";
/** \brief Evaluator for / : Real -> Real -> Real */
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

/**
   \brief Semantic attachment for less than or equal to operator with type
   <code>Real -> Real -> Bool</code>
*/
class real_le_value : public const_value {
public:
    real_le_value():const_value(name{"Real", "le"}, Real >> (Real >> Bool)) {}
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3 && is_real_value(args[1]) && is_real_value(args[2])) {
            r = mk_bool_value(real_value_numeral(args[1]) <= real_value_numeral(args[2]));
            return true;
        } else {
            return false;
        }
    }
};
MK_BUILTIN(real_le_fn, real_le_value);

MK_CONSTANT(real_sub_fn, name({"Real", "sub"}));
MK_CONSTANT(real_neg_fn, name({"Real", "neg"}));
MK_CONSTANT(real_abs_fn, name({"Real", "abs"}));
MK_CONSTANT(real_ge_fn, name({"Real", "ge"}));
MK_CONSTANT(real_lt_fn, name({"Real", "lt"}));
MK_CONSTANT(real_gt_fn, name({"Real", "gt"}));

void import_real(environment & env) {
    if (env.find_object(to_value(Real).get_name()))
        return;
    expr rr_b = Real >> (Real >> Bool);
    expr rr_r = Real >> (Real >> Real);
    expr r_r  = Real >> Real;
    expr x    = Const("x");
    expr y    = Const("y");

    env.add_builtin(Real);
    env.add_builtin_set(rVal(0));
    env.add_builtin(mk_real_add_fn());
    env.add_builtin(mk_real_mul_fn());
    env.add_builtin(mk_real_div_fn());
    env.add_builtin(mk_real_le_fn());

    env.add_definition(real_sub_fn_name, rr_r, Fun({{x, Real}, {y, Real}}, rAdd(x, rMul(rVal(-1), y))));
    env.add_definition(real_neg_fn_name, r_r,  Fun({x, Real}, rMul(rVal(-1), x)));
    env.add_definition(real_abs_fn_name, r_r,  Fun({x, Real}, rIf(rLe(rVal(0), x), x, rNeg(x))));
    env.add_definition(real_ge_fn_name, rr_b,  Fun({{x, Real}, {y, Real}}, rLe(y, x)));
    env.add_definition(real_lt_fn_name, rr_b,  Fun({{x, Real}, {y, Real}}, Not(rLe(y, x))));
    env.add_definition(real_gt_fn_name, rr_b,  Fun({{x, Real}, {y, Real}}, Not(rLe(x, y))));
}

class int_to_real_value : public const_value {
public:
    int_to_real_value():const_value("int_to_real", Int >> Real) {}
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 2 && is_int_value(args[1])) {
            r = mk_real_value(mpq(int_value_numeral(args[1])));
            return true;
        } else {
            return false;
        }
    }
};
MK_BUILTIN(int_to_real_fn,  int_to_real_value);
MK_CONSTANT(nat_to_real_fn, name("nat_to_real"));

void import_int_to_real_coercions(environment & env) {
    if (env.find_object(to_value(mk_int_to_real_fn()).get_name()))
        return;
    import_int(env);
    import_real(env);

    env.add_builtin(mk_int_to_real_fn());
    expr x    = Const("x");
    env.add_definition(nat_to_real_fn_name, Nat >> Real, Fun({x, Nat}, i2r(n2i(x))));
}
}
