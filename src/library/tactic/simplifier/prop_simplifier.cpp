/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <string>
#include <algorithm>
#include "util/sexpr/option_declarations.h"
#include "library/kernel_serializer.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/tactic/simplifier/prop_simplifier.h"

#ifndef LEAN_DEFAULT_PROP_SIMPLIFIER_ELIM_AND
#define LEAN_DEFAULT_PROP_SIMPLIFIER_ELIM_AND false
#endif

namespace lean {

// Options
static name * g_prop_simplifier_elim_and = nullptr;

static bool get_prop_simplifier_elim_and(options const & o) {
    return o.get_bool(*g_prop_simplifier_elim_and, LEAN_DEFAULT_PROP_SIMPLIFIER_ELIM_AND);
}

prop_simplifier_options::prop_simplifier_options(options const & o):
    m_elim_and(get_prop_simplifier_elim_and(o)) {}

static name * g_prop_simplifier_macro_name    = nullptr;
static std::string * g_prop_simplifier_opcode = nullptr;

class prop_simplifier_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 2)
            throw exception(sstream() << "invalid 'prop_simplifier' macro, incorrect number of arguments");
    }

public:
    prop_simplifier_macro_definition_cell() {}

    // TODO(dhs): this can be raised once we implement proof generation
    virtual unsigned trust_level() const override { return 2; }

    virtual name get_name() const { return *g_prop_simplifier_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context & tctx, bool infer_only) const {
        check_macro(m);
        return mk_app(mk_constant(get_eq_name(), {mk_level_one()}), mk_Prop(), macro_arg(m, 0), macro_arg(m, 1));
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context & tctx) const {
        check_macro(m);
        throw exception(sstream() << "proof generation for the prop_simplifier macro has not been implemented yet");
        lean_unreachable();
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_prop_simplifier_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<prop_simplifier_macro_definition_cell const *>(&other)) {
            return true;
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return get_name().hash();
    }
};

static expr mk_prop_simplifier_macro(expr const & old_e, expr const & new_e) {
    expr margs[2];
    margs[0] = old_e;
    margs[1] = new_e;
    macro_definition m(new prop_simplifier_macro_definition_cell());
    return mk_macro(m, 2, margs);
}

static simp_result mk_simp_result(expr const & old_e, expr const & new_e) {
    return simp_result(new_e, mk_prop_simplifier_macro(old_e, new_e));
}

// Util
bool is_lt_light_not(expr const & e1, expr const & e2) {
    expr arg1, arg2;
    if (is_not(e1, arg1)) {
        return is_lt_light_not(arg1, e2);
    } else if (is_not(e2, arg2)) {
        return !is_lt_light_not(arg2, e1);
    } else {
        return is_lt(e1, e2, true);
    }
}

// Fast simplification
optional<expr> prop_simplifier::simplify_eq(expr const & eq, expr const & type, expr const & lhs, expr const & rhs) {
    if (m_tctx.is_def_eq(lhs, rhs))
        return some_expr(mk_true());

    if (type != mk_Prop())
        return none_expr();

    expr new_lhs, new_rhs;
    if (is_not(lhs, new_lhs) && is_not(rhs, new_rhs)) {
        return some_expr(mk_app(eq, type, new_lhs, new_rhs));
    }

    if (is_true(lhs))
        return some_expr(rhs);

    if (is_false(lhs)) {
        if (auto r = simplify_not(rhs))
            return r;
        else
            return some_expr(mk_app(mk_constant(get_not_name()), rhs));
    }

    if (is_true(rhs))
        return some_expr(lhs);

    if (is_false(rhs)) {
        if (auto r = simplify_not(lhs))
            return r;
        else
            return some_expr(mk_app(mk_constant(get_not_name()), lhs));
    }

    if (is_not(lhs, new_lhs) && m_tctx.is_def_eq(new_lhs, rhs))
        return some_expr(mk_false());

    if (is_not(rhs, new_rhs) && m_tctx.is_def_eq(new_rhs, lhs))
        return some_expr(mk_false());

    return none_expr();
}

optional<expr> prop_simplifier::simplify_heq(expr const & heq, expr const & type1, expr const & type2, expr const & lhs, expr const & rhs) {
    if (m_tctx.is_def_eq(type1, type2)) {
        levels lvls = const_levels(heq);
        lean_assert(length(lvls) == 2);
        return simplify_eq(mk_constant(get_eq_name(), {head(lvls)}), type1, lhs, rhs);
    }
    return none_expr();
}

optional<expr> prop_simplifier::simplify_iff(expr const & lhs, expr const & rhs) {
    if (m_tctx.is_def_eq(lhs, rhs))
        return some_expr(mk_true());

    expr new_lhs, new_rhs;
    if (is_not(lhs, new_lhs) && is_not(rhs, new_rhs)) {
        return some_expr(mk_app(mk_constant(get_iff_name()), new_lhs, new_rhs));
    }

    if (is_true(lhs))
        return some_expr(rhs);

    if (is_false(lhs)) {
        if (auto r = simplify_not(rhs))
            return r;
        else
            return some_expr(mk_app(mk_constant(get_not_name()), rhs));
    }

    if (is_true(rhs))
        return some_expr(lhs);

    if (is_false(rhs)) {
        if (auto r = simplify_not(lhs))
            return r;
        else
            return some_expr(mk_app(mk_constant(get_not_name()), lhs));
    }

    if (is_not(lhs, new_lhs) && m_tctx.is_def_eq(new_lhs, rhs))
        return some_expr(mk_false());

    if (is_not(rhs, new_rhs) && m_tctx.is_def_eq(new_rhs, lhs))
        return some_expr(mk_false());

    return none_expr();
}

optional<expr> prop_simplifier::simplify_not(expr const & e) {
    expr arg;
    if (is_not(e, arg)) {
        return some_expr(arg);
    } else if (is_true(e)) {
        return some_expr(mk_false());
    } else if (is_false(e)) {
        return some_expr(mk_true());
    }
    buffer<expr> args;
    expr fn = get_app_args(e, args);
    if (is_constant(fn) && const_name(fn) == get_eq_name() && args.size() == 3 && m_tctx.whnf(args[0]) == mk_Prop()) {
        return some_expr(mk_app(fn, mk_Prop(), mk_app(mk_constant(get_not_name()), args[1]), args[2]));
    }
    return none_expr();
}

optional<expr> prop_simplifier::simplify_pi(expr const & dom, expr const & body, bool is_arrow) {
    if (m_tctx.is_def_eq(body, mk_true()))
        return some_expr(mk_true());
    if (m_tctx.is_def_eq(dom, mk_false()))
        return some_expr(mk_true());
    if (is_arrow && m_tctx.is_def_eq(dom, body))
        return some_expr(mk_true());
    return none_expr();
}

optional<expr> prop_simplifier::simplify_ite(expr const & fn, buffer<expr> & args) {
    bool simplified = false;

    expr & c = args[0];
    expr & t = args[3];
    expr & e = args[4];

    // TODO(dhs): add classical transformation for (ite (not c) t e)
    // t and e are propositions? (with a flag?)

    // Note: c is already in whnf
    if (c == mk_true())
        return some_expr(t);

    if (c == mk_false())
        return some_expr(e);

    buffer<expr> x_args;
    expr x_op = get_app_args(t, x_args);

    // Issue: subsingleton instances are not canonized
    // TODO(dhs): ite c (ite c t _) e ==> ite c t e
    // TODO(dhs): ite c t (ite c _ e) ==> ite c t e
    if (is_constant(x_op) && const_name(x_op) == get_ite_name()) {
        expr & t_c = x_args[0];
        expr & t_t = x_args[3];
        if (m_tctx.is_def_eq(c, t_c)) {
            t = t_t;
            simplified = true;
        }
    }

    x_args.clear();
    x_op = get_app_args(e, x_args);

    if (is_constant(x_op) && const_name(x_op) == get_ite_name()) {
        expr & e_c = x_args[0];
        expr & e_e = x_args[4];
        if (m_tctx.is_def_eq(c, e_c)) {
            e = e_e;
            simplified = true;
        }
    }

    if (m_tctx.is_def_eq(t, e))
        return some_expr(t);

    // TODO(dhs): add classical transformations when
    // t and e are propositions? (with a flag?)

    if (simplified)
        return some_expr(mk_app(fn, args));
    else
        return none_expr();
}

optional<expr> prop_simplifier::simplify_and(buffer<expr> & args) {
    bool simplified = false;
    if (!std::is_sorted(args.begin(), args.end(), is_lt_light_not)) {
        std::sort(args.begin(), args.end(), is_lt_light_not);
        simplified = true;
    }

    buffer<expr> new_args;
    expr last_lit, curr_lit;
    bool last_lit_pos = false, curr_lit_pos = false;

    for (unsigned i = 0; i < args.size(); ++i) {
        if (is_false(args[i])) {
            return some_expr(mk_false());
        } else if (is_true(args[i])) {
            simplified = true;
            continue;
        }

        if (is_not(args[i], curr_lit)) {
            curr_lit_pos = false;
        } else {
            curr_lit = args[i];
            curr_lit_pos = true;
        }

        // Note use of structural equality
        if (curr_lit == last_lit) {
            if (last_lit_pos != curr_lit_pos) {
                lean_assert(last_lit_pos);
                return some_expr(mk_false());
            } else {
                simplified = true;
                continue;
            }
        }

        new_args.push_back(args[i]);
        last_lit = curr_lit;
        last_lit_pos = curr_lit_pos;
    }

    switch (new_args.size()) {
    case 0: return some_expr(mk_true());
    case 1: return some_expr(new_args[0]);
    default:
        if (simplified)
            return some_expr(mk_nary_app(mk_constant(get_and_name()), new_args));
        else
            return none_expr();
    }
    lean_unreachable();
}

optional<expr> prop_simplifier::simplify_or(buffer<expr> & args) {
    bool simplified = false;
    if (!std::is_sorted(args.begin(), args.end(), is_lt_light_not)) {
        std::sort(args.begin(), args.end(), is_lt_light_not);
        simplified = true;
    }

    buffer<expr> new_args;
    expr last_lit, curr_lit;
    bool last_lit_pos = false, curr_lit_pos = false;

    for (unsigned i = 0; i < args.size(); ++i) {
        if (is_true(args[i])) {
            return some_expr(mk_true());
        } else if (is_false(args[i])) {
            simplified = true;
            continue;
        }

        if (is_not(args[i], curr_lit)) {
            curr_lit_pos = false;
        } else {
            curr_lit = args[i];
            curr_lit_pos = true;
        }

        if (curr_lit == last_lit) {
            if (last_lit_pos != curr_lit_pos) {
                lean_assert(last_lit_pos);
                return some_expr(mk_true());
            } else {
                simplified = true;
                continue;
            }
        }

        new_args.push_back(args[i]);
        last_lit = curr_lit;
        last_lit_pos = curr_lit_pos;
    }

    switch (new_args.size()) {
    case 0: return some_expr(mk_true());
    case 1: return some_expr(new_args[0]);
    default:
        if (simplified)
            return some_expr(mk_nary_app(mk_constant(get_or_name()), new_args));
        else
            return none_expr();
    }
    lean_unreachable();
}

// Setup and teardown
void initialize_prop_simplifier() {
    // Option names
    g_prop_simplifier_elim_and = new name{"prop_simplifier", "elim_and"};

    // Register options
    register_bool_option(*g_prop_simplifier_elim_and, LEAN_DEFAULT_PROP_SIMPLIFIER_ELIM_AND,
                         "(prop_simplifier) (and a b c) ==> (not (or (not a) (not b) (not c)))");

    // Register macro
    g_prop_simplifier_macro_name = new name("prop_simplifier");
    g_prop_simplifier_opcode     = new std::string("Prop_Simp");
    register_macro_deserializer(*g_prop_simplifier_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num == 2)
                                        return mk_prop_simplifier_macro(args[0], args[1]);
                                    else
                                        throw corrupted_stream_exception();
                                });
}

void finalize_prop_simplifier() {
    // Option names
    delete g_prop_simplifier_elim_and;

    // Macro names
    delete g_prop_simplifier_macro_name;
    delete g_prop_simplifier_opcode;
}

// Entry points
simp_result prop_simplifier::simplify_binary(expr const & old_e) {
    if (is_pi(old_e)) {
        if (auto r = simplify_pi(binding_domain(old_e), binding_body(old_e), is_arrow(old_e)))
            return mk_simp_result(old_e, *r);
        else
            return simp_result(old_e);
    }

    buffer<expr> args;
    expr f = get_app_args(old_e, args);
    if (!is_constant(f))
        return simp_result(old_e);

    name id = const_name(f);

    if (id == get_ite_name() && args.size() == 5) {
        if (auto r = simplify_ite(f, args))
            return mk_simp_result(old_e, *r);
    } else if (id == get_eq_name() && args.size() == 3) {
        if (auto r = simplify_eq(f, args[0], args[1], args[2]))
            return mk_simp_result(old_e, *r);
    } else if (id == get_heq_name() && args.size() == 4) {
        if (auto r = simplify_heq(f, args[0], args[1], args[2], args[3]))
            return mk_simp_result(old_e, *r);
    } else if (id == get_iff_name() && args.size() == 2) {
        if (auto r = simplify_iff(args[0], args[1]))
            return mk_simp_result(old_e, *r);
    } else if (id == get_not_name() && args.size() == 1) {
        if (auto r = simplify_not(args[0]))
            return mk_simp_result(old_e, *r);
    }
    return simp_result(old_e);
}

optional<simp_result> prop_simplifier::simplify_nary(expr const & assoc, expr const & old_e, expr const & op, buffer<expr> & args) {
    if (!is_constant(op))
        return optional<simp_result>();

    name id = const_name(op);
    if (id == get_and_name()) {
        if (auto r = simplify_and(args))
            return optional<simp_result>(mk_simp_result(old_e, *r));
    } else if (id == get_or_name()) {
        if (auto r = simplify_or(args))
            return optional<simp_result>(mk_simp_result(old_e, *r));
    }
    return optional<simp_result>();
}
}
