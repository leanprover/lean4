/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/numerics/mpq.h"
#include "library/type_context.h"

namespace lean {
/*
   Given a type `α`, this structure stores instances and partial
   applications for arithmetic-related instances.  The data is
   constructed "on demand" by the helper class `arith_instance`.

   The current design allows multiple `arith_instance` to share
   the same `arith_instance_info` IF they are all in the same
   execution thread.

   This code is currently used by
   - norm_num (numeric normalizer)
     Remark: the proofs created by `norm_num` try to use the most general
     structure for applying each auxiliary lemma. In retrospect, I think this is overkill.
     In practice, `norm_num` is used only for: `semiring`, `linear_ordered_semiring`, `ring`, `linear_ordered_ring`,
     `field`, `linerar_ordered_field`. Moreover, we want to use the unbundled approach for structures
     such as `monoid` and `group`.

   - It was also used by mpq_macro (which is used only by the SMT2 frontend)
     Remark: the SMT2 frontend was originally built to test the performance of
     a blast tactic that Leo and Daniel were developing. This tactic does not
     exist anymore. Moreover, SMT2 benchmarks are far from ideal for testing
     a system like Lean. AFAICT, nobody uses the SMT2 frontend.
     So, we have deleted `mpq_macro` and the SMT2 frontend. Motivation: less stuff to maintain.

   Plan:

   - Reduce the number of structures used by `norm_num`. We just need to change
     the lemmas used by `norm_num` and adjust the C++ code. An additional motivation
     is that we can replace semi-bundled type classes such as `monoid` and `group` with
     unbundled type classes such as `is_monoid` and `is_group` that are parametrized
     by operations too.
*/
class arith_instance_info {
    friend class arith_instance;
    expr   m_type;
    levels m_levels;

    /* Partial applications */
    optional<expr> m_zero, m_one;
    optional<expr> m_add, m_sub, m_neg;
    optional<expr> m_mul, m_div, m_inv;
    optional<expr> m_lt, m_le;
    optional<expr> m_bit0, m_bit1;

    /* Structures */
    optional<expr> m_partial_order;
    optional<expr> m_add_comm_semigroup;
    optional<expr> m_monoid, m_add_monoid;
    optional<expr> m_add_group, m_add_comm_group;
    optional<expr> m_distrib, m_mul_zero_class;
    optional<expr> m_semiring, m_linear_ordered_semiring;
    optional<expr> m_ring, m_linear_ordered_ring;
    optional<expr> m_field;
public:
    arith_instance_info(expr const & type, level const & lvl):m_type(type), m_levels(lvl) {}
};

typedef std::shared_ptr<arith_instance_info> arith_instance_info_ptr;
arith_instance_info_ptr mk_arith_instance_info(expr const & type, level const & lvl);

class arith_instance {
    type_context_old *          m_ctx;
    arith_instance_info_ptr m_info;

    expr mk_structure(name const & s, optional<expr> & r);
    expr mk_op(name const & op, name const & s, optional<expr> & r);

    expr mk_pos_num(mpz const & n);

public:
    arith_instance(type_context_old & ctx, arith_instance_info_ptr const & info):m_ctx(&ctx), m_info(info) {}
    arith_instance(type_context_old & ctx, expr const & type, level const & level);
    arith_instance(type_context_old & ctx, expr const & type);
    arith_instance(arith_instance_info_ptr const & info):m_ctx(nullptr), m_info(info) {}
    arith_instance(type_context_old & ctx):m_ctx(&ctx) {}

    void set_info(arith_instance_info_ptr const & info) { m_info = info; }
    /* The following method creates a fresh `arith_instance_info` for the given type.

       Missing optimization: it should do nothing if `type` is and `m_info->m_type`
       are equal. */
    void set_type(expr const & type);

    expr const & get_type() const { return m_info->m_type; }
    levels const & get_levels() const { return m_info->m_levels; }

    bool is_nat();

    expr mk_zero();
    expr mk_one();
    expr mk_add();
    expr mk_sub();
    expr mk_neg();
    expr mk_mul();
    expr mk_div();
    expr mk_inv();
    expr mk_lt();
    expr mk_le();

    expr mk_bit0();
    expr mk_bit1();

    expr mk_has_zero() { return app_arg(mk_zero()); }
    expr mk_has_one() { return app_arg(mk_one()); }
    expr mk_has_add() { return app_arg(mk_add()); }
    expr mk_has_sub() { return app_arg(mk_sub()); }
    expr mk_has_neg() { return app_arg(mk_neg()); }
    expr mk_has_mul() { return app_arg(mk_mul()); }
    expr mk_has_div() { return app_arg(mk_div()); }
    expr mk_has_inv() { return app_arg(mk_inv()); }
    expr mk_has_lt() { return app_arg(mk_lt()); }
    expr mk_has_le() { return app_arg(mk_le()); }

    expr mk_partial_order();
    expr mk_add_comm_semigroup();
    expr mk_monoid();
    expr mk_add_monoid();
    expr mk_add_group();
    expr mk_add_comm_group();
    expr mk_distrib();
    expr mk_mul_zero_class();
    expr mk_semiring();
    expr mk_linear_ordered_semiring();
    expr mk_ring();
    expr mk_linear_ordered_ring();
    expr mk_field();

    expr mk_num(mpz const & n);
    expr mk_num(mpq const & n);

    optional<mpq> eval(expr const & e);
};
};
