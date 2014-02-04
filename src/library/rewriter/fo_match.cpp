/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <utility>
#include "util/trace.h"
#include "kernel/expr.h"
#include "library/printer.h"
#include "library/arith/nat.h"
#include "library/arith/arith.h"
#include "library/rewriter/fo_match.h"
#include "library/rewriter/rewriter.h"

using std::cout;
using std::endl;

namespace lean {

bool fo_match::match_var(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_var : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;); // LCOV_EXCL_LINE

    unsigned idx = var_idx(p);
    if (idx < o) {
        // Current variable is the one created by lambda inside of pattern
        // and it is *not* a target of pattern matching.
        return p == t;
    } else {
        auto it = s.find(idx - o);
        if (it != s.end()) {
            // This variable already has an entry in the substitution
            // map. We need to make sure that 't' and s[idx] are the
            // same
            lean_trace("fo_match", tout << "match_var exist:" << idx - o << " |-> " << it->second << endl;); // LCOV_EXCL_LINE
            return it->second == t;
        }
        // This variable has no entry in the substituition map. Let's
        // add one.
        s.insert(idx - o, t);
        lean_trace("fo_match", tout << "match_var MATCHED : " << s << endl;); // LCOV_EXCL_LINE
        return true;
    }
}

bool fo_match::match_constant(expr const & p, expr const & t, unsigned, subst_map &) {
    lean_trace("fo_match", tout << "match_constant : (" << p << ", " << t << ")" << endl;); // LCOV_EXCL_LINE
    return p == t;
}

bool fo_match::match_value(expr const & p, expr const & t, unsigned, subst_map &) {
    lean_trace("fo_match", tout << "match_value : (" << p << ", " << t << ")" << endl;); // LCOV_EXCL_LINE
    return p == t;
}

bool fo_match::match_app(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_app : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;); // LCOV_EXCL_LINE
    if (!is_app(t)) {
        lean_trace("fo_match", tout << "match_app : " << t << " is not app." << endl;); // LCOV_EXCL_LINE
        return false;
    }
    unsigned num_p = num_args(p);
    unsigned num_t = num_args(t);
    if (num_p != num_t) {
        lean_trace("fo_match", tout << "match_app : number of arguments does not match"
                                    << "(" << num_p << " <> " << num_t << ")" << endl;); // LCOV_EXCL_LINE
        return false;
    }

    for (unsigned i = 0; i < num_p; i++) {
        if (!match_main(arg(p, i), arg(t, i), o, s))
            return false;
    }
    return true;
}

bool fo_match::match_lambda(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_lambda : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;); // LCOV_EXCL_LINE
    lean_trace("fo_match", tout << "fun (" << abst_name(p) << " : " << abst_domain(p) << "), " << abst_body(p) << endl;); // LCOV_EXCL_LINE
    if (!is_lambda(t)) {
        return false;
    } else {
        // First match the domain part
        auto p_domain = abst_domain(p);
        auto t_domain = abst_domain(t);
        if (!match_main(p_domain, t_domain, o, s))
            return false;

        // Then match the body part, increase offset by 1.
        auto p_body = abst_body(p);
        auto t_body = abst_body(t);
        return match_main(p_body, t_body, o + 1, s);
    }
}

bool fo_match::match_pi(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_pi : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;); // LCOV_EXCL_LINE
    lean_trace("fo_match", tout << "Pi (" << abst_name(p) << " : " << abst_domain(p) << "), " << abst_body(p) << endl;); // LCOV_EXCL_LINE
    if (!is_pi(t)) {
        return false;
    } else {
        // First match the domain part
        auto p_domain = abst_domain(p);
        auto t_domain = abst_domain(t);
        if (!match_main(p_domain, t_domain, o, s))
            return false;

        // Then match the body part, increase offset by 1.
        auto p_body = abst_body(p);
        auto t_body = abst_body(t);
        return match_main(p_body, t_body, o + 1, s);
    }
}

bool fo_match::match_type(expr const & p, expr const & t, unsigned, subst_map &) {
    lean_trace("fo_match", tout << "match_type : (" << p << ", " << t << ")" << endl;); // LCOV_EXCL_LINE
    return p == t;
}

bool fo_match::match_let(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match_let : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;); // LCOV_EXCL_LINE
    if (!is_let(t)) {
        return false;
    } else {
        // First match the type part
        auto p_type = let_type(p);
        auto t_type = let_type(t);
        if (!match_main(p_type, t_type, o, s))
            return false;

        // then match the value part
        auto p_value = let_value(p);
        auto t_value = let_value(t);
        if (!match_main(p_value, t_value, o, s))
            return false;

        // then match the value part
        auto p_body = let_body(p);
        auto t_body = let_body(t);
        return match_main(p_body, t_body, o + 1, s);
    }
}
bool fo_match::match_metavar(expr const & p, expr const & t, unsigned, subst_map &) {
    lean_trace("fo_match", tout << "match_meta : (" << p << ", " << t << ")" << endl;); // LCOV_EXCL_LINE
    return p == t;
}

bool fo_match::match_main(optional<expr> const & p, optional<expr> const & t, unsigned o, subst_map & s) {
    if (p && t)
        return match_main(*p, *t, o, s);
    else
        return !p && !t;
}

bool fo_match::match_main(expr const & p, expr const & t, unsigned o, subst_map & s) {
    lean_trace("fo_match", tout << "match : (" << p << ", " << t << ", " << o << ", " << s << ")" << endl;); // LCOV_EXCL_LINE
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
    case expr_kind::Let:
        return match_let(p, t, o, s);
    case expr_kind::MetaVar:
        return match_metavar(p, t, o, s);
    case expr_kind::Proj: case expr_kind::Pair: case expr_kind::Sigma:
        // TODO(Leo):
        break;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool fo_match::match(expr const & p, expr const & t, unsigned o, subst_map & s) {
    s.push();
    if (match_main(p, t, o, s)) {
        return true;
    } else {
        s.pop();
        return false;
    }
}
}
