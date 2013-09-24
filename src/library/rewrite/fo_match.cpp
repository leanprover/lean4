/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <utility>
#include "util/trace.h"
#include "kernel/expr.h"
#include "kernel/context.h"
#include "library/all/all.h"
#include "library/arith/nat.h"
#include "library/arith/arith.h"
#include "library/rewrite/fo_match.h"
#include "library/rewrite/rewrite.h"
#include "library/printer.h"

using std::cout;
using std::endl;

namespace lean {

std::ostream & operator<<(std::ostream & out, subst_map & s) {
    out << "{";
    for (auto it = s.begin(); it != s.end(); it++) {
        out << it->first << " => ";
        out << it->second << "; ";
    }
    out << "}";
    return out;
}

bool fo_match::match_var(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_var : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;);
    unsigned idx = var_idx(p);
    if (idx < o) {
        // Current variable is the one created by lambda inside of pattern
        // and it is *not* a target of pattern matching.
        return p == t;
    } else {
        auto it = s.find(idx);
        if (it != s.end()) {
            // This variable already has an entry in the substitution
            // map. We need to make sure that 't' and s[idx] are the
            // same
            lean_trace("fo_match", tout << "match_var exist:" << idx << " |-> " << it->second << endl;);
            return it->second == t;
        }
        // This variable has no entry in the substituition map. Let's
        // add one.
        s.insert(std::make_pair(idx, t));
        lean_trace("fo_match", tout << "match_var MATCHED : " << s << endl;);
        return true;
    }
}

bool fo_match::match_constant(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_constant : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;);
    return p == t;
}

bool fo_match::match_value(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_value : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;);
    return p == t;
}

bool fo_match::match_app(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_app : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;);
    if (!is_app(t))
        return false;
    unsigned num_p = num_args(p);
    unsigned num_t = num_args(t);
    if (num_p != num_t) {
        return false;
    }

    for (unsigned i = 0; i < num_p; i++) {
        if (!match(arg(p, i), arg(t, i), o, s))
            return false;
    }
    return true;
}

bool fo_match::match_lambda(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_lambda : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;);
    lean_trace("fo_match", tout << "fun (" << abst_name(p) << " : " << abst_domain(p) << "), " << abst_body(p) << endl;);
    if (!is_lambda(t)) {
        return false;
    } else {
        // First match the domain part
        auto p_domain = abst_domain(p);
        auto t_domain = abst_domain(t);
        if (!match(p_domain, t_domain, o, s))
            return false;

        // Then match the body part, increase offset by 1.
        auto p_body = abst_body(p);
        auto t_body = abst_body(t);
        return match(p_domain, t_domain, o + 1, s);
    }
}

bool fo_match::match_pi(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_pi : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;);
    lean_trace("fo_match", tout << "Pi (" << abst_name(p) << " : " << abst_domain(p) << "), " << abst_body(p) << endl;);
    if (!is_pi(t)) {
        return false;
    } else {
        // First match the domain part
        auto p_domain = abst_domain(p);
        auto t_domain = abst_domain(t);
        if (!match(p_domain, t_domain, o, s))
            return false;

        // Then match the body part, increase offset by 1.
        auto p_body = abst_body(p);
        auto t_body = abst_body(t);
        return match(p_domain, t_domain, o + 1, s);
    }
}

bool fo_match::match_type(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_type : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;);
    return p == t;
}

bool fo_match::match_eq(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_eq : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;);
    if (!is_eq(t))
        return false;
    return match(eq_lhs(p), eq_lhs(t), o, s) && match(eq_rhs(p), eq_rhs(t), o, s);
}

bool fo_match::match_let(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_let : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;);
    if (!is_let(t)) {
        return false;
    } else {
        // First match the type part
        auto p_type = let_type(p);
        auto t_type = let_type(t);
        if (!match(p_type, t_type, o, s))
            return false;

        // then match the value part
        auto p_value = let_value(p);
        auto t_value = let_value(t);
        if (!match(p_value, t_value, o, s))
            return false;

        // then match the value part
        auto p_body = let_body(p);
        auto t_body = let_body(t);
        return match(p_body, t_body, o + 1, s);
    }
}
bool fo_match::match_metavar(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_meta : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;);
    return p == t;
}

bool fo_match::match(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;);
    switch (p.kind()) {
    case expr_kind::Var:
        return match_var(p, t, o, s);
    case expr_kind::Constant:
        return match_constant(p, t, o, s);
    case expr_kind::Value:
        return match_value(p, t, o, s);
    case expr_kind::App:
        return match_app(p, t, o, s);
    case expr_kind::Lambda:
        return match_lambda(p, t, o, s);
    case expr_kind::Pi:
        return match_pi(p, t, o, s);
    case expr_kind::Type:
        return match_type(p, t, o, s);
    case expr_kind::Eq:
        return match_eq(p, t, o, s);
    case expr_kind::Let:
        return match_let(p, t, o, s);
    case expr_kind::MetaVar:
        return match_metavar(p, t, o, s);
    }
    lean_unreachable();
    return false;
}
}
