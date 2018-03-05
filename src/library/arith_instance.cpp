/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/arith_instance.h"
#include "library/num.h"

namespace lean {
// TODO(Leo): pre compute arith_instance_info for nat, int and real

arith_instance_info_ptr mk_arith_instance_info(expr const & type, level const & lvl) {
    return std::make_shared<arith_instance_info>(type, lvl);
}

arith_instance::arith_instance(type_context_old & ctx, expr const & type, level const & level):
    m_ctx(&ctx), m_info(mk_arith_instance_info(type, level)) {}

arith_instance::arith_instance(type_context_old & ctx, expr const & type):
    m_ctx(&ctx) {
    set_type(type);
}

void arith_instance::set_type(expr const & type) {
    if (optional<level> lvl = dec_level(get_level(*m_ctx, type)))
        m_info = mk_arith_instance_info(type, *lvl);
    else
        throw exception("failed to infer universe level");
}

expr arith_instance::mk_op(name const & op, name const & s, optional<expr> & r) {
    if (r) return *r;
    if (m_ctx) {
        expr inst_type = mk_app(mk_constant(s, m_info->m_levels), m_info->m_type);
        if (auto inst = m_ctx->mk_class_instance(inst_type)) {
            r = mk_app(mk_constant(op, m_info->m_levels), m_info->m_type, *inst);
            return *r;
        }
    }
    throw exception(sstream() << "failed to synthesize '" << s << "'");
}

expr arith_instance::mk_structure(name const & s, optional<expr> & r) {
    if (r) return *r;
    if (m_ctx) {
        expr inst_type = mk_app(mk_constant(s, m_info->m_levels), m_info->m_type);
        if (auto inst = m_ctx->mk_class_instance(inst_type)) {
            r = *inst;
            return *r;
        }
    }
    throw exception(sstream() << "failed to synthesize '" << s << "'");
}

expr arith_instance::mk_bit1() {
    if (!m_info->m_bit1)
        m_info->m_bit1 = mk_app(mk_constant(get_bit1_name(), m_info->m_levels), m_info->m_type, mk_has_one(), mk_has_add());
    return *m_info->m_bit1;
}

expr arith_instance::mk_zero() { return mk_op(get_has_zero_zero_name(), get_has_zero_name(), m_info->m_zero); }
expr arith_instance::mk_one() { return mk_op(get_has_one_one_name(), get_has_one_name(), m_info->m_one); }
expr arith_instance::mk_add() { return mk_op(get_has_add_add_name(), get_has_add_name(), m_info->m_add); }
expr arith_instance::mk_sub() { return mk_op(get_has_sub_sub_name(), get_has_sub_name(), m_info->m_sub); }
expr arith_instance::mk_neg() { return mk_op(get_has_neg_neg_name(), get_has_neg_name(), m_info->m_neg); }
expr arith_instance::mk_mul() { return mk_op(get_has_mul_mul_name(), get_has_mul_name(), m_info->m_mul); }
expr arith_instance::mk_div() { return mk_op(get_has_div_div_name(), get_has_div_name(), m_info->m_div); }
expr arith_instance::mk_inv() { return mk_op(get_has_inv_inv_name(), get_has_inv_name(), m_info->m_inv); }
expr arith_instance::mk_lt() { return mk_op(get_has_lt_lt_name(), get_has_lt_name(), m_info->m_lt); }
expr arith_instance::mk_le() { return mk_op(get_has_le_le_name(), get_has_le_name(), m_info->m_le); }

expr arith_instance::mk_bit0() { return mk_op(get_bit0_name(), get_has_add_name(), m_info->m_bit0); }

expr arith_instance::mk_partial_order() { return mk_structure(get_partial_order_name(), m_info->m_partial_order); }
expr arith_instance::mk_add_comm_semigroup() { return mk_structure(get_add_comm_semigroup_name(), m_info->m_add_comm_semigroup); }
expr arith_instance::mk_monoid() { return mk_structure(get_monoid_name(), m_info->m_monoid); }
expr arith_instance::mk_add_monoid() { return mk_structure(get_add_monoid_name(), m_info->m_add_monoid); }
expr arith_instance::mk_add_group() { return mk_structure(get_add_group_name(), m_info->m_add_group); }
expr arith_instance::mk_add_comm_group() { return mk_structure(get_add_comm_group_name(), m_info->m_add_comm_group); }
expr arith_instance::mk_distrib() { return mk_structure(get_distrib_name(), m_info->m_distrib); }
expr arith_instance::mk_mul_zero_class() { return mk_structure(get_mul_zero_class_name(), m_info->m_mul_zero_class); }
expr arith_instance::mk_semiring() { return mk_structure(get_semiring_name(), m_info->m_semiring); }
expr arith_instance::mk_linear_ordered_semiring() { return mk_structure(get_linear_ordered_semiring_name(), m_info->m_linear_ordered_semiring); }
expr arith_instance::mk_ring() { return mk_structure(get_ring_name(), m_info->m_ring); }
expr arith_instance::mk_linear_ordered_ring() { return mk_structure(get_linear_ordered_ring_name(), m_info->m_linear_ordered_ring); }
expr arith_instance::mk_field() { return mk_structure(get_field_name(), m_info->m_field); }

expr arith_instance::mk_pos_num(mpz const & n) {
    lean_assert(n > 0);
    if (n == 1)
        return mk_one();
    else if (n % mpz(2) == 1)
        return mk_app(mk_bit1(), mk_pos_num(n/2));
    else
        return mk_app(mk_bit0(), mk_pos_num(n/2));
}

expr arith_instance::mk_num(mpz const & n) {
    if (n < 0) {
        return mk_app(mk_neg(), mk_pos_num(0 - n));
    } else if (n == 0) {
        return mk_zero();
    } else {
        return mk_pos_num(n);
    }
}

expr arith_instance::mk_num(mpq const & q) {
    mpz numer = q.get_numerator();
    mpz denom = q.get_denominator();
    lean_assert(denom >= 0);
    if (denom == 1 || numer == 0) {
        return mk_num(numer);
    } else if (numer > 0) {
        return mk_app(mk_div(), mk_num(numer), mk_num(denom));
    } else {
        return mk_app(mk_neg(), mk_app(mk_div(), mk_num(neg(numer)), mk_num(denom)));
    }
}

bool arith_instance::is_nat() {
    return is_constant(m_info->m_type, get_nat_name());
}

optional<mpq> arith_instance::eval(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    if (!is_constant(f)) {
        throw exception("cannot find num of nonconstant");
    } else if (const_name(f) == get_has_add_add_name() && args.size() == 4) {
        if (auto r1 = eval(args[2]))
        if (auto r2 = eval(args[3]))
            return optional<mpq>(*r1 + *r2);
    } else if (const_name(f) == get_has_mul_mul_name() && args.size() == 4) {
        if (auto r1 = eval(args[2]))
        if (auto r2 = eval(args[3]))
            return optional<mpq>(*r1 * *r2);
    } else if (const_name(f) == get_has_sub_sub_name() && args.size() == 4) {
        if (auto r1 = eval(args[2]))
        if (auto r2 = eval(args[3]))  {
            if (is_nat() && *r2 > *r1)
                return optional<mpq>(0);
            else
                return optional<mpq>(*r1 - *r2);
        }
    } else if (const_name(f) == get_has_div_div_name() && args.size() == 4) {
        if (auto r1 = eval(args[2]))
        if (auto r2 = eval(args[3]))  {
            if (is_nat())
                return optional<mpq>(); // not supported yet
            else if (*r2 == 0)
                return optional<mpq>(); // division by zero, add support for x/0 = 0
            else
                return optional<mpq>(*r1 / *r2);
        }
    } else if (const_name(f) == get_has_neg_neg_name() && args.size() == 3) {
        if (auto r1 = eval(args[2]))
            return optional<mpq>(neg(*r1));
    } else if (auto r = to_num(e)) {
        return optional<mpq>(*r);
    }
    return optional<mpq>();
}
}
