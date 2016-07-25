/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "util/sstream.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include "library/num.h"
#include "library/util.h"
#include "library/cache_helper.h"
#include "library/arith_instance_manager.h"

namespace lean {

static arith_instance_info * g_nat_instance_info  = nullptr;
static arith_instance_info * g_int_instance_info  = nullptr;
static arith_instance_info * g_real_instance_info = nullptr;

class arith_instance_info_cache {
private:
    environment m_env;
    expr_struct_map<arith_instance_info> m_cache;
public:
    environment const & env() const { return m_env; }
    expr_struct_map<arith_instance_info> & get_cache() { return m_cache; }
    arith_instance_info_cache(environment const & env): m_env(env) {}
};

typedef transparencyless_cache_compatibility_helper<arith_instance_info_cache> arith_instance_info_cache_helper;
MK_THREAD_LOCAL_GET_DEF(arith_instance_info_cache_helper, get_aiich);

static expr_struct_map<arith_instance_info> & get_arith_instance_info_cache_for(type_context const & tctx) {
    return get_aiich().get_cache_for(tctx).get_cache();
}

arith_instance_info::arith_instance_info(type_context & tctx, expr const & type):
    m_tctx_ptr(&tctx), m_type(type) { m_level = get_level(*m_tctx_ptr, type);}

arith_instance_info::arith_instance_info(type_context & tctx, expr const & type, level const & l):
    m_tctx_ptr(&tctx), m_type(type), m_level(l) {}

arith_instance_info::arith_instance_info(expr const & type, level const & l):
    m_type(type), m_level(l) {}

bool arith_instance_info::is_add_group() {
    if (m_is_add_group) {
        return *m_is_add_group;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_add_group_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_is_add_group = optional<bool>(true);
            return true;
        } else {
            m_is_add_group = optional<bool>(false);
            return false;
        }
    }
}

bool arith_instance_info::is_comm_semiring() {
    if (m_is_comm_semiring) {
        return *m_is_comm_semiring;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_comm_semiring_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_is_comm_semiring = optional<bool>(true);
            return true;
        } else {
            m_is_comm_semiring = optional<bool>(false);
            return false;
        }
    }
}

bool arith_instance_info::is_comm_ring() {
    if (m_is_comm_ring) {
        return *m_is_comm_ring;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_comm_ring_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_is_comm_ring = optional<bool>(true);
            return true;
        } else {
            m_is_comm_ring = optional<bool>(false);
            return false;
        }
    }
}

bool arith_instance_info::is_linear_ordered_semiring() {
    if (m_is_linear_ordered_semiring) {
        return *m_is_linear_ordered_semiring;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_linear_ordered_semiring_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_is_linear_ordered_semiring = optional<bool>(true);
            return true;
        } else {
            m_is_linear_ordered_semiring = optional<bool>(false);
            return false;
        }
    }
}

bool arith_instance_info::is_linear_ordered_comm_ring() {
    if (m_is_linear_ordered_comm_ring) {
        return *m_is_linear_ordered_comm_ring;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_linear_ordered_comm_ring_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_is_linear_ordered_comm_ring = optional<bool>(true);
            return true;
        } else {
            m_is_linear_ordered_comm_ring = optional<bool>(false);
            return false;
        }
    }
}

bool arith_instance_info::is_field() {
    if (m_is_field) {
        return *m_is_field;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_field_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_is_field = optional<bool>(true);
            return true;
        } else {
            m_is_field = optional<bool>(false);
            return false;
        }
    }
}

bool arith_instance_info::is_discrete_field() {
    if (m_is_discrete_field) {
        return *m_is_discrete_field;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_discrete_field_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_is_discrete_field = optional<bool>(true);
            return true;
        } else {
            m_is_discrete_field = optional<bool>(false);
            return false;
        }
    }
}

optional<mpz> arith_instance_info::has_cyclic_numerals() {
    if (!m_has_cyclic_numerals) {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_cyclic_numerals_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_has_cyclic_numerals = optional<bool>(true);
            expr bound = m_tctx_ptr->whnf(mk_app(mk_constant(get_cyclic_numerals_bound_name(), {m_level}), m_type, *inst));
            if (auto n = to_num(bound)) {
                m_numeral_bound = *n;
                return optional<mpz>(m_numeral_bound);
            } else {
                throw exception(sstream() << "bound in [cyclic_numerals " << m_type << "] must whnf to a numeral\n");
            }
        } else {
            m_has_cyclic_numerals = optional<bool>(false);
            return optional<mpz>();
        }
    } else if (*m_has_cyclic_numerals) {
        return optional<mpz>(m_numeral_bound);
    } else {
        lean_assert(!(*m_has_cyclic_numerals));
        return optional<mpz>();
    }
}

expr arith_instance_info::get_zero() {
    if (!null(m_zero)) {
        return m_zero;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_has_zero_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_zero = mk_app(mk_constant(get_zero_name(), {m_level}), m_type, *inst);
            return m_zero;
        } else {
            throw exception(sstream() << "cannot synthesize [has_zero " << m_type << "]\n");
        }
    }
}

expr arith_instance_info::get_one() {
    if (!null(m_one)) {
        return m_one;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_has_one_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_one = mk_app(mk_constant(get_one_name(), {m_level}), m_type, *inst);
            return m_one;
        } else {
            throw exception(sstream() << "cannot synthesize [has_one " << m_type << "]\n");
        }
    }
}

expr arith_instance_info::get_bit0() {
    if (!null(m_bit0)) {
        return m_bit0;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_has_add_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_bit0 = mk_app(mk_constant(get_bit0_name(), {m_level}), m_type, *inst);
            return m_bit0;
        } else {
            throw exception(sstream() << "cannot synthesize [has_add " << m_type << "]\n");
        }
    }
}

// TODO(dhs): for instances that are used for more than one getter, cache the instances in the structure as well
expr arith_instance_info::get_bit1() {
    if (!null(m_bit1)) {
        return m_bit1;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type1 = mk_app(mk_constant(get_has_one_name(), {m_level}), m_type);
        if (auto inst1 = m_tctx_ptr->mk_class_instance(inst_type1)) {
            expr inst_type2 = mk_app(mk_constant(get_has_add_name(), {m_level}), m_type);
            if (auto inst2 = m_tctx_ptr->mk_class_instance(inst_type2)) {
                m_bit1 = mk_app(mk_constant(get_bit1_name(), {m_level}), m_type, *inst1, *inst2);
                return m_bit1;
            } else {
                throw exception(sstream() << "cannot synthesize [has_add " << m_type << "]\n");
            }
        } else {
            throw exception(sstream() << "cannot synthesize [has_one " << m_type << "]\n");
        }
    }
}

expr arith_instance_info::get_add() {
    if (!null(m_add)) {
        return m_add;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_has_add_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_add = mk_app(mk_constant(get_add_name(), {m_level}), m_type, *inst);
            return m_add;
        } else {
            throw exception(sstream() << "cannot synthesize [has_add " << m_type << "]\n");
        }
    }
}

expr arith_instance_info::get_mul() {
    if (!null(m_mul)) {
        return m_mul;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_has_mul_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_mul = mk_app(mk_constant(get_mul_name(), {m_level}), m_type, *inst);
            return m_mul;
        } else {
            throw exception(sstream() << "cannot synthesize [has_mul " << m_type << "]\n");
        }
    }
}

expr arith_instance_info::get_sub() {
    if (!null(m_sub)) {
        return m_sub;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_has_sub_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_sub = mk_app(mk_constant(get_sub_name(), {m_level}), m_type, *inst);
            return m_sub;
        } else {
            throw exception(sstream() << "cannot synthesize [has_sub " << m_type << "]\n");
        }
    }
}

expr arith_instance_info::get_div() {
    if (!null(m_div)) {
        return m_div;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_has_div_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_div = mk_app(mk_constant(get_div_name(), {m_level}), m_type, *inst);
            return m_div;
        } else {
            throw exception(sstream() << "cannot synthesize [has_div " << m_type << "]\n");
        }
    }
}

expr arith_instance_info::get_neg() {
    if (!null(m_neg)) {
        return m_neg;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_has_neg_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_neg = mk_app(mk_constant(get_neg_name(), {m_level}), m_type, *inst);
            return m_neg;
        } else {
            throw exception(sstream() << "cannot synthesize [has_neg " << m_type << "]\n");
        }
    }
}

expr arith_instance_info::get_eq() { return mk_app(mk_constant(get_eq_name(), {m_level}), m_type); }

expr arith_instance_info::get_lt() {
    if (!null(m_lt)) {
        return m_lt;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_has_lt_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_lt = mk_app(mk_constant(get_lt_name(), {m_level}), m_type, *inst);
            return m_lt;
        } else {
            throw exception(sstream() << "cannot synthesize [has_lt " << m_type << "]\n");
        }
    }
}

expr arith_instance_info::get_le() {
    if (!null(m_le)) {
        return m_le;
    } else {
        lean_assert(m_tctx_ptr);
        expr inst_type = mk_app(mk_constant(get_has_le_name(), {m_level}), m_type);
        if (auto inst = m_tctx_ptr->mk_class_instance(inst_type)) {
            m_le = mk_app(mk_constant(get_le_name(), {m_level}), m_type, *inst);
            return m_le;
        } else {
            throw exception(sstream() << "cannot synthesize [has_le " << m_type << "]\n");
        }
    }
}

// Setup and teardown
void initialize_concrete_arith_instance_infos() {
    // nats
    expr nat = mk_constant(get_nat_name());
    g_nat_instance_info = new arith_instance_info(nat, mk_level_one());
    g_nat_instance_info->m_is_field                            = optional<bool>(false);
    g_nat_instance_info->m_is_discrete_field                   = optional<bool>(false);
    g_nat_instance_info->m_is_comm_ring                        = optional<bool>(false);
    g_nat_instance_info->m_is_linear_ordered_comm_ring         = optional<bool>(false);
    g_nat_instance_info->m_is_comm_semiring                    = optional<bool>(true);
    g_nat_instance_info->m_is_linear_ordered_semiring          = optional<bool>(true);
    g_nat_instance_info->m_is_add_group                        = optional<bool>(false);

    g_nat_instance_info->m_has_cyclic_numerals                 = optional<bool>(false);

    g_nat_instance_info->m_zero    = mk_app({mk_constant(get_zero_name(), {mk_level_one()}), nat, mk_constant(get_nat_has_zero_name())});
    g_nat_instance_info->m_one     = mk_app({mk_constant(get_one_name(), {mk_level_one()}),  nat, mk_constant(get_nat_has_one_name())});
    g_nat_instance_info->m_bit0    = mk_app({mk_constant(get_bit0_name(), {mk_level_one()}), nat, mk_constant(get_nat_has_add_name())});
    g_nat_instance_info->m_bit1    = mk_app({mk_constant(get_bit1_name(), {mk_level_one()}), nat, mk_constant(get_nat_has_one_name()), mk_constant(get_nat_has_add_name())});

    g_nat_instance_info->m_add     = mk_app({mk_constant(get_add_name(), {mk_level_one()}), nat, mk_constant(get_nat_has_add_name())});
    g_nat_instance_info->m_mul     = mk_app({mk_constant(get_mul_name(), {mk_level_one()}), nat, mk_constant(get_nat_has_mul_name())});
    g_nat_instance_info->m_div     = mk_app({mk_constant(get_div_name(), {mk_level_one()}), nat, mk_constant(get_nat_has_div_name())});
    g_nat_instance_info->m_sub     = mk_app({mk_constant(get_sub_name(), {mk_level_one()}), nat, mk_constant(get_nat_has_sub_name())});
    g_nat_instance_info->m_neg     = mk_app({mk_constant(get_neg_name(), {mk_level_one()}), nat, mk_constant(get_nat_has_neg_name())});

    g_nat_instance_info->m_lt      = mk_app({mk_constant(get_lt_name(), {mk_level_one()}), nat, mk_constant(get_nat_has_lt_name())});
    g_nat_instance_info->m_le      = mk_app({mk_constant(get_le_name(), {mk_level_one()}), nat, mk_constant(get_nat_has_le_name())});

    // ints
    expr z = mk_constant(get_int_name());
    g_int_instance_info = new arith_instance_info(z, mk_level_one());
    g_int_instance_info->m_is_field                            = optional<bool>(false);
    g_int_instance_info->m_is_discrete_field                   = optional<bool>(false);
    g_int_instance_info->m_is_comm_ring                        = optional<bool>(true);
    g_int_instance_info->m_is_linear_ordered_comm_ring         = optional<bool>(true);
    g_int_instance_info->m_is_comm_semiring                    = optional<bool>(true);
    g_int_instance_info->m_is_linear_ordered_semiring          = optional<bool>(true);
    g_int_instance_info->m_is_add_group                        = optional<bool>(true);

    g_int_instance_info->m_has_cyclic_numerals                 = optional<bool>(false);

    g_int_instance_info->m_zero    = mk_app({mk_constant(get_zero_name(), {mk_level_one()}), z, mk_constant(get_int_has_zero_name())});
    g_int_instance_info->m_one     = mk_app({mk_constant(get_one_name(), {mk_level_one()}),  z, mk_constant(get_int_has_one_name())});
    g_int_instance_info->m_bit0    = mk_app({mk_constant(get_bit0_name(), {mk_level_one()}), z, mk_constant(get_int_has_add_name())});
    g_int_instance_info->m_bit1    = mk_app({mk_constant(get_bit1_name(), {mk_level_one()}), z, mk_constant(get_int_has_one_name()), mk_constant(get_int_has_add_name())});

    g_int_instance_info->m_add     = mk_app({mk_constant(get_add_name(), {mk_level_one()}), z, mk_constant(get_int_has_add_name())});
    g_int_instance_info->m_mul     = mk_app({mk_constant(get_mul_name(), {mk_level_one()}), z, mk_constant(get_int_has_mul_name())});
    g_int_instance_info->m_div     = mk_app({mk_constant(get_div_name(), {mk_level_one()}), z, mk_constant(get_int_has_div_name())});
    g_int_instance_info->m_sub     = mk_app({mk_constant(get_sub_name(), {mk_level_one()}), z, mk_constant(get_int_has_sub_name())});
    g_int_instance_info->m_neg     = mk_app({mk_constant(get_neg_name(), {mk_level_one()}), z, mk_constant(get_int_has_neg_name())});

    g_int_instance_info->m_lt      = mk_app({mk_constant(get_lt_name(), {mk_level_one()}), z, mk_constant(get_int_has_lt_name())});
    g_int_instance_info->m_le      = mk_app({mk_constant(get_le_name(), {mk_level_one()}), z, mk_constant(get_int_has_le_name())});

    // reals
    expr real = mk_constant(get_real_name());
    g_real_instance_info = new arith_instance_info(real, mk_level_one());
    g_real_instance_info->m_is_field                            = optional<bool>(true);
    g_real_instance_info->m_is_discrete_field                   = optional<bool>(true);
    g_real_instance_info->m_is_comm_ring                        = optional<bool>(true);
    g_real_instance_info->m_is_linear_ordered_comm_ring         = optional<bool>(true);
    g_real_instance_info->m_is_comm_semiring                    = optional<bool>(true);
    g_real_instance_info->m_is_linear_ordered_semiring          = optional<bool>(true);
    g_real_instance_info->m_is_add_group                        = optional<bool>(true);

    g_real_instance_info->m_has_cyclic_numerals                 = optional<bool>(false);

    g_real_instance_info->m_zero    = mk_app({mk_constant(get_zero_name(), {mk_level_one()}), real, mk_constant(get_real_has_zero_name())});
    g_real_instance_info->m_one     = mk_app({mk_constant(get_one_name(), {mk_level_one()}),  real, mk_constant(get_real_has_one_name())});
    g_real_instance_info->m_bit0    = mk_app({mk_constant(get_bit0_name(), {mk_level_one()}), real, mk_constant(get_real_has_add_name())});
    g_real_instance_info->m_bit1    = mk_app({mk_constant(get_bit1_name(), {mk_level_one()}), real, mk_constant(get_real_has_one_name()), mk_constant(get_real_has_add_name())});

    g_real_instance_info->m_add     = mk_app({mk_constant(get_add_name(), {mk_level_one()}), real, mk_constant(get_real_has_add_name())});
    g_real_instance_info->m_mul     = mk_app({mk_constant(get_mul_name(), {mk_level_one()}), real, mk_constant(get_real_has_mul_name())});
    g_real_instance_info->m_div     = mk_app({mk_constant(get_div_name(), {mk_level_one()}), real, mk_constant(get_real_has_div_name())});
    g_real_instance_info->m_sub     = mk_app({mk_constant(get_sub_name(), {mk_level_one()}), real, mk_constant(get_real_has_sub_name())});
    g_real_instance_info->m_neg     = mk_app({mk_constant(get_neg_name(), {mk_level_one()}), real, mk_constant(get_real_has_neg_name())});

    g_real_instance_info->m_lt      = mk_app({mk_constant(get_lt_name(), {mk_level_one()}), real, mk_constant(get_real_has_lt_name())});
    g_real_instance_info->m_le      = mk_app({mk_constant(get_le_name(), {mk_level_one()}), real, mk_constant(get_real_has_le_name())});
}

void finalize_concrete_arith_instance_infos() {
    delete g_real_instance_info;
    delete g_int_instance_info;
    delete g_nat_instance_info;
}

void initialize_arith_instance_manager() {
    initialize_concrete_arith_instance_infos();
}

void finalize_arith_instance_manager() {
    finalize_concrete_arith_instance_infos();
}

// Entry points
arith_instance_info & get_arith_instance_info_for(concrete_arith_type type) {
    switch (type) {
    case concrete_arith_type::NAT:  return *g_nat_instance_info;
    case concrete_arith_type::INT:  return *g_int_instance_info;
    case concrete_arith_type::REAL: return *g_real_instance_info;
    }
    lean_unreachable();
}

optional<concrete_arith_type> is_concrete_arith_type(expr const & type) {
   if (type == mk_constant(get_nat_name()))
       return optional<concrete_arith_type>(concrete_arith_type::NAT);
   if (type == mk_constant(get_int_name()))
       return optional<concrete_arith_type>(concrete_arith_type::INT);
   if (type == mk_constant(get_real_name()))
       return optional<concrete_arith_type>(concrete_arith_type::REAL);
   else
       return optional<concrete_arith_type>();
}

arith_instance_info & get_arith_instance_info_for(type_context & tctx, expr const & type) {
    if (auto ctype = is_concrete_arith_type(type))
        return get_arith_instance_info_for(*ctype);

    expr_struct_map<arith_instance_info> & cache = get_arith_instance_info_cache_for(tctx);
    auto it = cache.find(type);
    if (it != cache.end()) {
        return it->second;
    } else {
        auto result = cache.insert({type, arith_instance_info(tctx, type)});
        lean_assert(result.second);
        return result.first->second;
    }
}

}
