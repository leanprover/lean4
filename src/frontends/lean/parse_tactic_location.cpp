/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/location.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/parse_tactic_location.h"

namespace lean {
static occurrence parse_occurrence(parser & p) {
    bool is_pos = true;
    if (p.curr_is_token(get_sub_tk())) {
        p.next();
        is_pos = false;
        if (!p.curr_is_token(get_lcurly_tk()))
            throw parser_error("invalid tactic location, '{' expected", p.pos());
    }
    if (p.curr_is_token(get_lcurly_tk())) {
        p.next();
        buffer<unsigned> occs;
        while (true) {
            auto pos   = p.pos();
            unsigned i = p.parse_small_nat();
            if (i == 0)
                throw parser_error("invalid tactic location, first occurrence is 1", pos);
            occs.push_back(i);
            if (!p.curr_is_token(get_comma_tk()))
                break;
            p.next();
        }
        p.check_token_next(get_rcurly_tk(), "invalid tactic location, '}' or ',' expected");
        if (is_pos)
            return occurrence::mk_occurrences(occs);
        else
            return occurrence::mk_except_occurrences(occs);
    } else {
        return occurrence();
    }
}

location parse_tactic_location(parser & p) {
    if (p.curr_is_token(get_at_tk())) {
        p.next();
        if (p.curr_is_token(get_star_tk())) {
            p.next();
            if (p.curr_is_token(get_turnstile_tk())) {
                p.next();
                if (p.curr_is_token(get_star_tk())) {
                    // at * |- *
                    return location::mk_everywhere();
                } else {
                    // at * |-
                    return location::mk_all_hypotheses();
                }
            } else {
                // at *
                return location::mk_everywhere();
            }
        } else if (p.curr_is_token(get_lparen_tk())) {
            p.next();
            buffer<name>       hyps;
            buffer<occurrence> hyp_occs;
            while (true) {
                hyps.push_back(p.get_name_val());
                p.next();
                hyp_occs.push_back(parse_occurrence(p));
                if (!p.curr_is_token(get_comma_tk()))
                    break;
                p.next();
            }
            p.check_token_next(get_rparen_tk(), "invalid tactic location, ')' expected");
            if (p.curr_is_token(get_turnstile_tk())) {
                p.next();
                occurrence goal_occ = parse_occurrence(p);
                return location::mk_at(goal_occ, hyps, hyp_occs);
            } else {
                return location::mk_hypotheses_at(hyps, hyp_occs);
            }
        } else if (p.curr_is_token(get_lcurly_tk()) || p.curr_is_token(get_sub_tk())) {
            occurrence o = parse_occurrence(p);
            return location::mk_goal_at(o);
        } else {
            buffer<name>       hyps;
            buffer<occurrence> hyp_occs;
            hyps.push_back(p.check_id_next("invalid tactic location, identifier expected"));
            hyp_occs.push_back(parse_occurrence(p));
            return location::mk_hypotheses_at(hyps, hyp_occs);
        }
    } else {
        return location::mk_goal_only();
    }
}
}
