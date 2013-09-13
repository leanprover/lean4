/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/environment.h"
#include "library/arith/nat.h"
#include "library/arith/numtype.h"

namespace lean {
class nat_type_value : public num_type_value {
public:
    nat_type_value():num_type_value("Nat", "\u2115") /* ℕ */ {}
};
expr const Nat = mk_value(*(new nat_type_value()));
expr mk_nat_type() { return Nat; }

class nat_value_value : public value {
    mpz m_val;
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
    virtual format pp(bool unicode) const { return pp(); }
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
class nat_bin_op : public const_value {
public:
    nat_bin_op():const_value(name("Nat", Name), Nat >> (Nat >> Nat)) {}
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3 && is_nat_value(args[1]) && is_nat_value(args[2])) {
            r = mk_nat_value(F()(nat_value_numeral(args[1]), nat_value_numeral(args[2])));
            return true;
        } else {
            return false;
        }
    }
};

constexpr char nat_add_name[] = "add";
struct nat_add_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 + v2; }; };
typedef nat_bin_op<nat_add_name, nat_add_eval> nat_add_value;
MK_BUILTIN(nat_add_fn, nat_add_value);

constexpr char nat_mul_name[] = "mul";
struct nat_mul_eval { mpz operator()(mpz const & v1, mpz const & v2) { return v1 * v2; }; };
typedef nat_bin_op<nat_mul_name, nat_mul_eval> nat_mul_value;
MK_BUILTIN(nat_mul_fn, nat_mul_value);

class nat_le_value : public const_value {
public:
    nat_le_value():const_value(name{"Nat", "le"}, Nat >> (Nat >> Bool)) {}
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3 && is_nat_value(args[1]) && is_nat_value(args[2])) {
            r = mk_bool_value(nat_value_numeral(args[1]) <= nat_value_numeral(args[2]));
            return true;
        } else {
            return false;
        }
    }
};
MK_BUILTIN(nat_le_fn, nat_le_value);

MK_CONSTANT(nat_ge_fn,  name({"Nat", "ge"}));
MK_CONSTANT(nat_lt_fn,  name({"Nat", "lt"}));
MK_CONSTANT(nat_gt_fn,  name({"Nat", "gt"}));
MK_CONSTANT(nat_id_fn,  name({"Nat", "id"}));

void import_nat(environment & env) {
    if (env.find_object(to_value(Nat).get_name()))
        return;
    expr nn_b = Nat >> (Nat >> Bool);
    expr x    = Const("x");
    expr y    = Const("y");

    env.add_builtin(Nat);
    env.add_builtin_set(nVal(0));
    env.add_builtin(mk_nat_add_fn());
    env.add_builtin(mk_nat_mul_fn());
    env.add_builtin(mk_nat_le_fn());

    env.add_definition(nat_ge_fn_name, nn_b, Fun({{x, Nat}, {y, Nat}}, nLe(y, x)));
    env.add_definition(nat_lt_fn_name, nn_b, Fun({{x, Nat}, {y, Nat}}, Not(nLe(y, x))));
    env.add_definition(nat_gt_fn_name, nn_b, Fun({{x, Nat}, {y, Nat}}, Not(nLe(x, y))));
    env.add_definition(nat_id_fn_name, Nat >> Nat, Fun({x, Nat}, x));
}
}
