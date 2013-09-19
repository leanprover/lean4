/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <utility>
#include "kernel/expr.h"
#include "kernel/context.h"
#include "library/all/all.h"
#include "library/arith/nat.h"
#include "library/arith/arith.h"
#include "library/rewrite/rewrite.h"

namespace lean {


std::ostream & operator<<(std::ostream & out, expr_pair const & p) {
    out << "("
        << p.first << ", "
        << p.second << ")";
    return out;
}

bool fo_match::match_var(context & ctx, expr const & p, expr const & t, subst_map & s) {
    std::cerr << "match_var : ("
              << ctx << " ,"
              << p << ", "
              << t << ", "
//              << s << ")"
              << std::endl;
    s.insert(std::make_pair(var_idx(p), t));
    return true;
}
bool fo_match::match_constant(context & ctx, expr const & p, expr const & t, subst_map & s) {
    std::cerr << "match_constant : ("
              << ctx << " ,"
              << p << ", "
              << t << ", "
//              << s << ")"
              << std::endl;
    if (is_constant(t) && const_name(p) == const_name(t)) {
        return true;
    } else {
        return false;
    }
}
bool fo_match::match_value(context & ctx, expr const & p, expr const & t, subst_map & s) {
    std::cerr << "match_value : ("
              << ctx << " ,"
              << p << ", "
              << t << ", "
//              << s << ")"
              << std::endl;
    if (is_value(t) && to_value(p) == to_value(t)) {
        return true;
    } else {
        return false;
    }
}
bool fo_match::match_app(context & ctx, expr const & p, expr const & t, subst_map & s) {
    std::cerr << "match_app : ("
              << ctx << " ,"
              << p << ", "
              << t << ", "
//              << s << ")"
              << std::endl;
    unsigned num_p = num_args(p);
    unsigned num_t = num_args(p);
    if (num_p != num_t) {
        return false;
    }

    for unsigned i = 0; i <= num_p; i++) {
        if (!match(ctx, arg(p, i), arg(t, i), s))
            return false;
    }
    return true;
}
bool fo_match::match_lambda(context & ctx, expr const & p, expr const & t, subst_map & s) {
    std::cerr << "match_lambda : ("
              << ctx << " ,"
              << p << ", "
              << t << ", "
//              << s << ")"
              << std::endl;
    // TODO(soonho)
    std::cerr << "fun (" << abst_name(p)
              << " : " << abst_domain(p)
              << "), " << abst_body(p) << std::endl;
    if (!is_lambda(t)) {
        return false;
    }

    return true;
}
bool fo_match::match_pi(context & ctx, expr const & p, expr const & t, subst_map & s) {
    std::cerr << "match_pi : ("
              << ctx << " ,"
              << p << ", "
              << t << ", "
//              << s << ")"
              << std::endl;
    // TODO(soonho)
    std::cerr << "Pi (" << abst_name(p)
              << " : " << abst_domain(p)
              << "), " << abst_body(p) << std::endl;
    return true;
}
bool fo_match::match_type(context & ctx, expr const & p, expr const & t, subst_map & s) {
    std::cerr << "match_type : ("
              << ctx << " ,"
              << p << ", "
              << t << ", "
//              << s << ")"
              << std::endl;
    // TODO(soonho)
    return true;
}
bool fo_match::match_eq(context & ctx, expr const & p, expr const & t, subst_map & s) {
    std::cerr << "match_eq : ("
              << ctx << " ,"
              << p << ", "
              << t << ", "
//              << s << ")"
              << std::endl;
    // TODO(soonho)
    return true;
}
bool fo_match::match_let(context & ctx, expr const & p, expr const & t, subst_map & s) {
    std::cerr << "match_let : ("
              << ctx << " ,"
              << p << ", "
              << t << ", "
//              << s << ")"
              << std::endl;
    // TODO(soonho)
    return true;
}
bool fo_match::match_metavar(context & ctx, expr const & p, expr const & t, subst_map & s) {
    std::cerr << "match_meta : ("
              << ctx << " ,"
              << p << ", "
              << t << ", "
//              << s << ")"
              << std::endl;
    // TODO(soonho)
    return true;
}
bool fo_match::match(context & ctx, expr const & p, expr const & t, subst_map & s) {
    std::cerr << "match : ("
              << ctx << " ,"
              << p << ", "
              << t << ", "
//              << s << ")"
              << std::endl;

    switch (p.kind()) {
    case expr_kind::Var:
        return match_var(ctx, p, t, s);
    case expr_kind::Constant:
        return match_constant(ctx, p, t, s);
    case expr_kind::Value:
        return match_value(ctx, p, t, s);
    case expr_kind::App:
        return match_app(ctx, p, t, s);
    case expr_kind::Lambda:
        return match_lambda(ctx, p, t, s);
    case expr_kind::Pi:
        return match_pi(ctx, p, t, s);
    case expr_kind::Type:
        return match_type(ctx, p, t, s);
    case expr_kind::Eq:
        return match_eq(ctx, p, t, s);
    case expr_kind::Let:
        return match_let(ctx, p, t, s);
    case expr_kind::MetaVar:
        return match_metavar(ctx, p, t, s);
    }
}
}
