/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr.h"
#include "library/type_context.h"

namespace lean {

class arith_instance_info {
    type_context * m_tctx_ptr;

    expr m_type;
    level m_level;

    // For boolean queries
    optional<bool> m_is_field, m_is_discrete_field, m_is_comm_ring, m_is_linear_ordered_comm_ring;
    optional<bool> m_is_comm_semiring, m_is_linear_ordered_semiring, m_is_add_group;

    optional<bool> m_has_cyclic_numerals;
    mpz m_numeral_bound;

    // Partial applications
    expr m_zero, m_one;
    expr m_bit0, m_bit1;
    expr m_add, m_mul, m_div, m_sub, m_neg;
    expr m_eq, m_lt, m_le;

    bool null(expr const & e) { return e == expr(); }

    arith_instance_info(expr const & type, level const & l);

    friend void initialize_concrete_arith_instance_infos();
    friend arith_instance_info & get_arith_instance_info_for(type_context & tctx, expr const & type);

public:
    arith_instance_info(type_context & tctx, expr const & type);
    arith_instance_info(type_context & tctx, expr const & type, level const & l);

    expr get_type() const { return m_type; }

    bool is_add_group();
    bool is_comm_semiring();
    bool is_comm_ring();
    bool is_linear_ordered_semiring();
    bool is_linear_ordered_comm_ring();
    bool is_field();
    bool is_discrete_field();
    optional<mpz> has_cyclic_numerals();

    expr get_zero();
    expr get_one();
    expr get_bit0();
    expr get_bit1();
    expr get_add();
    expr get_mul();
    expr get_sub();
    expr get_div();
    expr get_neg();
    expr get_eq();
    expr get_le();
    expr get_lt();
};

enum class concrete_arith_type { NAT, INT, REAL };
optional<concrete_arith_type> is_concrete_arith_type(expr const & type);

arith_instance_info & get_arith_instance_info_for(concrete_arith_type type);
arith_instance_info & get_arith_instance_info_for(type_context & tctx, expr const & type);

void initialize_arith_instance_manager();
void finalize_arith_instance_manager();

}
