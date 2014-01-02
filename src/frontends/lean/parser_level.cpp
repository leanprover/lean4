/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/io_state_stream.h"
#include "frontends/lean/parser_imp.h"
namespace lean {
// ==========================================
// Support for parsing levels
static name g_max_name("max");
static name g_cup_name("\u2294");
static name g_plus_name("+");
static unsigned g_level_plus_prec = 10;
static unsigned g_level_cup_prec  = 5;
// ==========================================

/*
   Parse Universe levels
*/
level parser_imp::parse_level_max() {
    auto p = pos();
    next();
    buffer<level> lvls;
    while (curr_is_identifier() || curr_is_nat()) {
        lvls.push_back(parse_level());
    }
    if (lvls.size() < 2)
        throw parser_error("invalid level expression, max must have at least two arguments", p);
    level r = lvls[0];
    for (unsigned i = 1; i < lvls.size(); i++)
        r = max(r, lvls[i]);
    return r;
}

level parser_imp::parse_level_nud_id() {
    name id = curr_name();
    if (id == g_max_name) {
        return parse_level_max();
    } else {
        next();
        return m_env->get_uvar(id);
    }
}

level parser_imp::parse_level_nud_int() {
    auto p  = pos();
    mpz val = curr_num().get_numerator();
    next();
    if (val < 0)
        throw parser_error("invalid level expression, value is negative", p);
    if (!val.is_unsigned_int())
        throw parser_error("invalid level expression, value does not fit in a machine integer", p);
    return level() + val.get_unsigned_int();
}

level parser_imp::parse_level_lparen() {
    next();
    level r = parse_level();
    check_rparen_next("invalid level expression, ')' expected");
    return r;
}

level parser_imp::parse_level_nud() {
    switch (curr()) {
    case scanner::token::Id:        return parse_level_nud_id();
    case scanner::token::IntVal:    return parse_level_nud_int();
    case scanner::token::LeftParen: return parse_level_lparen();
    default:
        throw parser_error("invalid level expression", pos());
    }
}

level parser_imp::parse_level_led_plus(level const & left) {
    auto p = pos();
    next();
    level right = parse_level(g_level_plus_prec);
    if (!is_lift(right) || !lift_of(right).is_bottom())
        throw parser_error("invalid level expression, right hand side of '+' (aka universe lift operator) must be a numeral", p);
    return left + lift_offset(right);
}

level parser_imp::parse_level_led_cup(level const & left) {
    next();
    level right = parse_level(g_level_cup_prec);
    return max(left, right);
}

level parser_imp::parse_level_led(level const & left) {
    switch (curr()) {
    case scanner::token::Id:
        if (curr_name() == g_plus_name)     return parse_level_led_plus(left);
        else if (curr_name() == g_cup_name) return parse_level_led_cup(left);
    default:
        throw parser_error("invalid level expression", pos());
    }
}

unsigned parser_imp::curr_level_lbp() {
    switch (curr()) {
    case scanner::token::Id: {
        name const & id = curr_name();
        if (id == g_plus_name) return g_level_plus_prec;
        else if (id == g_cup_name) return g_level_cup_prec;
        else return 0;
    }
    default: return 0;
    }
}

level parser_imp::parse_level(unsigned rbp) {
    level left = parse_level_nud();
    while (rbp < curr_level_lbp()) {
        left = parse_level_led(left);
    }
    return left;
}
}
