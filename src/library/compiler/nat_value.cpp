/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/numerics/mpz.h"
#include "kernel/expr.h"
#include "library/constants.h"
#include "library/num.h"
#include "library/util.h"
#include "library/kernel_serializer.h"
#include "library/replace_visitor_with_tc.h"

namespace lean {
static name * g_nat_macro         = nullptr;
static std::string * g_nat_opcode = nullptr;

/** \brief Auxiliary macro used during compilation */
class nat_value_macro : public macro_definition_cell {
    mpz m_value;
public:
    nat_value_macro(mpz const & v):m_value(v) {}
    virtual bool lt(macro_definition_cell const & d) const override {
        return m_value < static_cast<nat_value_macro const &>(d).m_value;
    }
    virtual name get_name() const override { return *g_nat_macro; }

    virtual expr check_type(expr const &, abstract_type_context &, bool) const override {
        return mk_nat_type();
    }

    static expr convert(mpz const & n, expr const & one, expr const & add) {
        if (n == 0) {
            return mk_constant(get_nat_zero_name());
        } else if (n == 1) {
            return one;
        } else {
            expr r = convert(n/2, one, add);
            r = mk_app(add, r, r);
            if (n % mpz(2) == 1)
                return mk_app(add, r, one);
            else
                return r;
        }
    }

    virtual optional<expr> expand(expr const &, abstract_type_context &) const override {
        expr one = mk_app(mk_constant(get_nat_succ_name()), mk_constant(get_nat_zero_name()));
        expr add = mk_constant(get_nat_add_name());
        expr r = convert(m_value, one, add);
        return optional<expr>(r);
    }

    virtual unsigned trust_level() const override { return 0; }
    virtual bool operator==(macro_definition_cell const & other) const override {
        nat_value_macro const * other_ptr = dynamic_cast<nat_value_macro const *>(&other);
        return other_ptr && m_value == other_ptr->m_value;
    }
    virtual void display(std::ostream & out) const override {
        out << m_value;
    }
    virtual unsigned hash() const override { return m_value.hash(); }
    virtual void write(serializer & s) const override {
        s << *g_nat_opcode << m_value;
    }
    mpz const & get_value() const { return m_value; }
};

expr mk_nat_value(mpz const & v) {
    return mk_macro(macro_definition(new nat_value_macro(v)));
}

bool is_nat_value(expr const & e) {
    return is_macro(e) && dynamic_cast<nat_value_macro const *>(macro_def(e).raw()) != nullptr;
}

mpz const & get_nat_value_value(expr const & e) {
    lean_assert(is_nat_value(e));
    return static_cast<nat_value_macro const *>(macro_def(e).raw())->get_value();
}

optional<expr> to_nat_value(type_context_old & ctx, expr const & e) {
    if (optional<mpz> v = to_num(e)) {
        expr type = ctx.whnf(ctx.infer(e));
        if (is_nat_type(type)) {
            return some_expr(mk_nat_value(*v));
        }
    }
    return none_expr();
}

class find_nat_values_fn : public replace_visitor_with_tc {
    expr visit_app(expr const & e) override {
        if (auto v = to_nat_value(m_ctx, e))
            return copy_tag(e, expr(*v));
        return replace_visitor_with_tc::visit_app(e);
    }
public:
    find_nat_values_fn(type_context_old & ctx):replace_visitor_with_tc(ctx) {}
};

expr find_nat_values(environment const & env, expr const & e) {
    type_context_old ctx(env, transparency_mode::All);
    return find_nat_values_fn(ctx)(e);
}

void initialize_nat_value() {
    g_nat_macro  = new name("nat_value_macro");
    g_nat_opcode = new std::string("CNatM");
    register_macro_deserializer(*g_nat_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num != 0)
                                        throw corrupted_stream_exception();
                                    mpz v = read_mpz(d);
                                    return mk_nat_value(v);
                                });
}

void finalize_nat_value() {
    delete g_nat_opcode;
    delete g_nat_macro;
}
}
