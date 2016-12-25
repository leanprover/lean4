/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <string>
#include "util/sstream.h"
#include "util/hash.h"
#include "library/num.h"
#include "library/util.h"
#include "library/mpq_macro.h"
#include "library/constants.h"
#include "library/kernel_serializer.h"
#include "library/type_context.h"
#include "library/arith_instance_manager.h"

namespace lean {

struct mpq2expr_fn {
    arith_instance_info_ref m_info;

    mpq2expr_fn(arith_instance_info_ref info): m_info(info) {}

    expr operator()(mpq const & q) {
        mpz numer = q.get_numerator();
        if (numer.is_zero())
            return m_info->get_zero();

        mpz denom = q.get_denominator();
        lean_assert(denom > 0);

        bool flip_sign = false;
        if (numer.is_neg()) {
            numer.neg();
            flip_sign = true;
        }

        expr e;
        if (denom == 1) {
            e = pos_mpz_to_expr(numer);
        } else {
            e = mk_app(m_info->get_div(), pos_mpz_to_expr(numer), pos_mpz_to_expr(denom));
        }

        if (flip_sign) {
            return mk_app(m_info->get_neg(), e);
        } else {
            return e;
        }
    }

    expr pos_mpz_to_expr(mpz const & n) {
        lean_assert(n > 0);
        if (n == 1)
            return m_info->get_one();
        if (n % mpz(2) == 1)
            return mk_app(m_info->get_bit1(), pos_mpz_to_expr(n/2));
        else
            return mk_app(m_info->get_bit0(), pos_mpz_to_expr(n/2));
    }
};

static name * g_mpq_macro_name    = nullptr;
static std::string * g_mpq_opcode = nullptr;

class mpq_macro_definition_cell : public macro_definition_cell {
    mpq                 m_q;

    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception(sstream() << "invalid 'mpq' macro, incorrect number of arguments");
        expr const & type = macro_arg(m, 0);
        bool ok_type = is_nat_type(type) || is_int_type(type) || type == mk_constant(get_real_name());
        if (!ok_type)
            throw exception(sstream() << "invalid 'mpq' macro, only nat, int, and real accepted");
    }

public:
    mpq_macro_definition_cell(mpq const & q): m_q(q) {}

    mpq const & get_mpq() const { return m_q; }
    virtual name get_name() const { return *g_mpq_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context &, bool) const {
        check_macro(m);
        return macro_arg(m, 0);
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context &) const {
        check_macro(m);
        expr ty = macro_arg(m, 0);
        concrete_arith_type cty;
        if (ty == mk_constant(get_nat_name()))
            cty = concrete_arith_type::NAT;
        else if (ty == mk_constant(get_int_name()))
            cty = concrete_arith_type::INT;
        else if (ty == mk_constant(get_real_name()))
            cty = concrete_arith_type::REAL;
        else
            throw exception(sstream() << "trying to expand invalid 'mpq' macro");

        return some_expr(mpq2expr_fn(get_arith_instance_info_for(cty))(get_mpq()));
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_mpq_opcode);
        s << m_q;
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<mpq_macro_definition_cell const *>(&other)) {
            return get_mpq() == other_ptr->get_mpq();
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return ::lean::hash(get_name().hash(), m_q.hash());
    }
};

expr mk_mpq_macro(mpq const & q, expr const & type) {
    macro_definition m(new mpq_macro_definition_cell(q));
    return mk_macro(m, 1, &type);
}

bool is_mpq_macro(expr const & e) {
    if (is_macro(e) && dynamic_cast<mpq_macro_definition_cell const *>(macro_def(e).raw()))
        return true;
    else
        return false;
}

bool is_mpq_macro(expr const & e, mpq & q) {
    if (is_macro(e)) {
        if (auto def = dynamic_cast<mpq_macro_definition_cell const *>(macro_def(e).raw())) {
            q = def->get_mpq();
            return true;
        } else {
            return false;
        }
    } else {
        return false;
    }
}

void initialize_mpq_macro() {
    g_mpq_macro_name = new name("mpq");
    g_mpq_opcode     = new std::string("MPQ");
    register_macro_deserializer(*g_mpq_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    mpq q;
                                    d >> q;
                                    return mk_mpq_macro(q, args[0]);
                                });
}

void finalize_mpq_macro() {
    delete g_mpq_macro_name;
    delete g_mpq_opcode;
}

}
