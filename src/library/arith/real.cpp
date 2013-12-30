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
#include "library/arith/real.h"
#include "library/arith/int.h"
#include "library/arith/nat.h"

namespace lean {
MK_CONSTANT(Real, "Real");
expr const Real = mk_Real();
expr mk_real_type() { return mk_Real(); }

/**
   \brief Semantic attachment for "Real" values.
   It is actually for rational values. We should eventually rename it to
   rat_value_value
*/
class real_value_value : public value {
    mpq m_val;
protected:
    virtual bool lt(value const & other) const {
        return m_val < static_cast<real_value_value const &>(other).m_val;
    }
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
    virtual format pp() const { return pp(false, false); }
    virtual format pp(bool, bool coercion) const {
        if (coercion)
            return format{format(const_name(mk_nat_to_real_fn())), space(), format(m_val)};
        else
            return format(m_val);
    }
    virtual unsigned hash() const { return m_val.hash(); }
    virtual int push_lua(lua_State * L) const { return push_mpq(L, m_val); }
    mpq const & get_num() const { return m_val; }
    virtual void write(serializer & s) const { s << "real" << m_val; }
};

expr mk_real_value(mpq const & v) {
    return mk_value(*(new real_value_value(v)));
}
expr read_real_value(deserializer & d) { return mk_real_value(read_mpq(d)); }
static value::register_deserializer_fn real_value_ds("real", read_real_value);
static register_available_builtin_fn g_real_value(name({"Real", "numeral"}), []() { return mk_real_value(mpq(0)); }, true);

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
    virtual optional<expr> normalize(unsigned num_args, expr const * args) const {
        if (num_args == 3 && is_real_value(args[1]) && is_real_value(args[2])) {
            return some_expr(mk_real_value(F()(real_value_numeral(args[1]), real_value_numeral(args[2]))));
        } else {
            return none_expr();
        }
    }
    virtual void write(serializer & s) const { s << (std::string("real_") + Name); }
};

constexpr char real_add_name[] = "add";
/** \brief Evaluator for + : Real -> Real -> Real */
struct real_add_eval { mpq operator()(mpq const & v1, mpq const & v2) { return v1 + v2; }; };
typedef real_bin_op<real_add_name, real_add_eval> real_add_value;
MK_BUILTIN(real_add_fn, real_add_value);
expr read_real_add(deserializer & ) { return mk_real_add_fn(); }
static value::register_deserializer_fn real_add_ds("real_add", read_real_add);
static register_available_builtin_fn g_real_add_value(name({"Real", "add"}), []() { return mk_real_add_fn(); });


constexpr char real_mul_name[] = "mul";
/** \brief Evaluator for * : Real -> Real -> Real */
struct real_mul_eval { mpq operator()(mpq const & v1, mpq const & v2) { return v1 * v2; }; };
typedef real_bin_op<real_mul_name, real_mul_eval> real_mul_value;
MK_BUILTIN(real_mul_fn, real_mul_value);
expr read_real_mul(deserializer & ) { return mk_real_mul_fn(); }
static value::register_deserializer_fn real_mul_ds("real_mul", read_real_mul);
static register_available_builtin_fn g_real_mul_value(name({"Real", "mul"}), []() { return mk_real_mul_fn(); });

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
expr read_real_div(deserializer & ) { return mk_real_div_fn(); }
static value::register_deserializer_fn real_div_ds("real_div", read_real_div);
static register_available_builtin_fn g_real_div_value(name({"Real", "div"}), []() { return mk_real_div_fn(); });

/**
   \brief Semantic attachment for less than or equal to operator with type
   <code>Real -> Real -> Bool</code>
*/
class real_le_value : public const_value {
public:
    real_le_value():const_value(name{"Real", "le"}, Real >> (Real >> Bool)) {}
    virtual optional<expr> normalize(unsigned num_args, expr const * args) const {
        if (num_args == 3 && is_real_value(args[1]) && is_real_value(args[2])) {
            return some_expr(mk_bool_value(real_value_numeral(args[1]) <= real_value_numeral(args[2])));
        } else {
            return none_expr();
        }
    }
    virtual void write(serializer & s) const { s << "real_le"; }
};
MK_BUILTIN(real_le_fn, real_le_value);
expr read_real_le(deserializer & ) { return mk_real_le_fn(); }
static value::register_deserializer_fn real_le_ds("real_le", read_real_le);
static register_available_builtin_fn g_real_le_value(name({"Real", "le"}), []() { return mk_real_le_fn(); });

class int_to_real_value : public const_value {
public:
    int_to_real_value():const_value("int_to_real", Int >> Real) {}
    virtual optional<expr> normalize(unsigned num_args, expr const * args) const {
        if (num_args == 2 && is_int_value(args[1])) {
            return some_expr(mk_real_value(mpq(int_value_numeral(args[1]))));
        } else {
            return none_expr();
        }
    }
    virtual void write(serializer & s) const { s << "int_to_real"; }
};
MK_BUILTIN(int_to_real_fn,  int_to_real_value);
expr read_int_to_real(deserializer & ) { return mk_int_to_real_fn(); }
static value::register_deserializer_fn int_to_real_ds("int_to_real", read_int_to_real);
static register_available_builtin_fn g_int_to_real_value("int_to_real", []() { return mk_int_to_real_fn(); });

MK_CONSTANT(real_sub_fn, name({"Real", "sub"}));
MK_CONSTANT(real_neg_fn, name({"Real", "neg"}));
MK_CONSTANT(real_abs_fn, name({"Real", "abs"}));
MK_CONSTANT(real_ge_fn, name({"Real", "ge"}));
MK_CONSTANT(real_lt_fn, name({"Real", "lt"}));
MK_CONSTANT(real_gt_fn, name({"Real", "gt"}));
MK_CONSTANT(nat_to_real_fn, name("nat_to_real"));

void import_real(environment const & env) {
    io_state ios;
    env->import("real", ios);
}

static int mk_real_value(lua_State * L) {
    return push_expr(L, mk_real_value(to_mpq_ext(L, 1)));
}

void open_real(lua_State * L) {
    SET_GLOBAL_FUN(mk_real_value,    "mk_real_value");
    SET_GLOBAL_FUN(mk_real_value,    "rVal");
}
}
