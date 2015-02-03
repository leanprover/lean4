/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/rewrite_tactic.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/parse_tactic_location.h"

namespace lean {
static name parse_rewrite_element_id(parser & p) {
    return p.check_id_next("invalid rewrite tactic step, identifier expected");
}

rewrite_element parse_rewrite_element(parser & p) {
    if (p.curr_is_token(get_slash_tk())) {
        p.next();
        name id = p.check_id_next("invalid unfold rewrite step, identifier expected");
        location loc = parse_tactic_location(p);
        return rewrite_element::mk_unfold(id, loc);
    }
    bool symm = false;
    if (p.curr_is_token(get_sub_tk())) {
        p.next();
        symm = true;
    }
    if (p.curr_is_numeral()) {
        unsigned n = p.parse_small_nat();
        if (p.curr_is_token(get_question_tk())) {
            p.next();
            name id = parse_rewrite_element_id(p);
            location loc = parse_tactic_location(p);
            return rewrite_element::mk_at_most_n(id, n, symm, loc);
        } else if (p.curr_is_token(get_bang_tk())) {
            p.next();
            name id = parse_rewrite_element_id(p);
            location loc = parse_tactic_location(p);
            return rewrite_element::mk_exactly_n(id, n, symm, loc);
        } else {
            name id = parse_rewrite_element_id(p);
            location loc = parse_tactic_location(p);
            return rewrite_element::mk_exactly_n(id, n, symm, loc);
        }
    } else if (p.curr_is_token(get_question_tk())) {
        p.next();
        name id = parse_rewrite_element_id(p);
        location loc = parse_tactic_location(p);
        return rewrite_element::mk_zero_or_more(id, symm, loc);
    } else if (p.curr_is_token(get_bang_tk())) {
        p.next();
        name id = parse_rewrite_element_id(p);
        location loc = parse_tactic_location(p);
        return rewrite_element::mk_one_or_more(id, symm, loc);
    } else {
        name id = parse_rewrite_element_id(p);
        location loc = parse_tactic_location(p);
        return rewrite_element::mk_once(id, symm, loc);
    }
}

expr parse_rewrite_tactic(parser & p) {
    buffer<rewrite_element> elems;
    while (true) {
        bool has_paren = false;
        if (p.curr_is_token(get_lparen_tk())) {
            has_paren = true;
            p.next();
        }
        elems.push_back(parse_rewrite_element(p));
        if (has_paren)
            p.check_token_next(get_rparen_tk(), "invalid rewrite tactic element, ')' expected");
        if (!p.curr_is_token(get_sub_tk()) &&
            !p.curr_is_numeral() &&
            !p.curr_is_token(get_bang_tk()) &&
            !p.curr_is_token(get_question_tk()) &&
            !p.curr_is_token(get_slash_tk()) &&
            !p.curr_is_identifier() &&
            !p.curr_is_token(get_lparen_tk()))
            break;
    }
    return mk_rewrite_tactic_expr(elems);
}
}
