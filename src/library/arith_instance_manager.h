/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include <memory>
#include "kernel/expr.h"
#include "library/type_context.h"

namespace lean {

class arith_instance_info {
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

    friend void initialize_concrete_arith_instance_infos();

public:
    arith_instance_info(expr const & type, level const & l);

    expr get_type() const { return m_type; }

    expr get_eq();

    bool is_add_group(type_context * tctx_ptr = nullptr);
    bool is_comm_semiring(type_context * tctx_ptr = nullptr);
    bool is_comm_ring(type_context * tctx_ptr = nullptr);
    bool is_linear_ordered_semiring(type_context * tctx_ptr = nullptr);
    bool is_linear_ordered_comm_ring(type_context * tctx_ptr = nullptr);
    bool is_field(type_context * tctx_ptr = nullptr);
    bool is_discrete_field(type_context * tctx_ptr = nullptr);
    optional<mpz> has_cyclic_numerals(type_context * tctx_ptr = nullptr);

    expr get_zero(type_context * tctx_ptr = nullptr);
    expr get_one(type_context * tctx_ptr = nullptr);
    expr get_bit0(type_context * tctx_ptr = nullptr);
    expr get_bit1(type_context * tctx_ptr = nullptr);
    expr get_add(type_context * tctx_ptr = nullptr);
    expr get_mul(type_context * tctx_ptr = nullptr);
    expr get_sub(type_context * tctx_ptr = nullptr);
    expr get_div(type_context * tctx_ptr = nullptr);
    expr get_neg(type_context * tctx_ptr = nullptr);
    expr get_le(type_context * tctx_ptr = nullptr);
    expr get_lt(type_context * tctx_ptr = nullptr);
};

typedef std::shared_ptr<arith_instance_info> arith_instance_info_ref;

enum class concrete_arith_type { NAT, INT, REAL };
optional<concrete_arith_type> is_concrete_arith_type(expr const & type);

arith_instance_info_ref get_arith_instance_info_for(concrete_arith_type type);
arith_instance_info_ref get_arith_instance_info_for(type_context & tctx, expr const & type);

void initialize_arith_instance_manager();
void finalize_arith_instance_manager();

}
