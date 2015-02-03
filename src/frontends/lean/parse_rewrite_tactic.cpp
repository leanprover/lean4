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
name parse_rewrite_element_id(parser & p) {
    return p.check_id_next("invalid rewrite tactic step, identifier expected");
}

rewrite_element parse_rewrite_element(parser & p) {
    if (p.curr_is_token(get_slash_tk())) {
        p.next();
        return rewrite_element::mk_unfold(p.check_id_next("invalid unfold rewrite step, identifier expected"));
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
            return rewrite_element::mk_at_most_n(parse_rewrite_element_id(p), n, symm);
        } else if (p.curr_is_token(get_bang_tk())) {
            p.next();
            return rewrite_element::mk_exactly_n(parse_rewrite_element_id(p), n, symm);
        } else {
            return rewrite_element::mk_exactly_n(parse_rewrite_element_id(p), n, symm);
        }
    } else if (p.curr_is_token(get_question_tk())) {
        p.next();
        return rewrite_element::mk_zero_or_more(parse_rewrite_element_id(p), symm);
    } else if (p.curr_is_token(get_bang_tk())) {
        p.next();
        return rewrite_element::mk_one_or_more(parse_rewrite_element_id(p), symm);
    } else {
        return rewrite_element::mk_once(parse_rewrite_element_id(p), symm);
    }
}

expr parse_rewrite_tactic(parser & p) {
    buffer<rewrite_element> elems;
    while (true) {
        elems.push_back(parse_rewrite_element(p));
        if (!p.curr_is_token(get_sub_tk()) &&
            !p.curr_is_numeral() &&
            !p.curr_is_token(get_bang_tk()) &&
            !p.curr_is_token(get_question_tk()) &&
            !p.curr_is_token(get_slash_tk()) &&
            !p.curr_is_identifier())
            break;
    }
    location loc = parse_tactic_location(p);
    return mk_rewrite_tactic_expr(elems, loc);
}
}
