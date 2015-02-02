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
    if (p.curr_is_token(get_at_tk())) {
        p.next();
        bool has_pos = false;
        bool has_neg = false;
        buffer<unsigned> occs;
        while (true) {
            if (p.curr_is_token(get_sub_tk())) {
                if (has_pos)
                    throw parser_error("invalid tactic location, cannot mix positive and negative occurrences", p.pos());
                has_neg = true;
                p.next();
                occs.push_back(p.parse_small_nat());
            } else {
                auto pos = p.pos();
                occs.push_back(p.parse_small_nat());
                if (has_neg)
                    throw parser_error("invalid tactic location, cannot mix positive and negative occurrences", pos);
                has_pos = true;
            }
            if (!p.curr_is_token(get_sub_tk()) && !p.curr_is_numeral())
                break;
        }
        if (has_pos)
            return occurrence::mk_occurrences(occs);
        else
            return occurrence::mk_except_occurrences(occs);
    } else {
        return occurrence();
    }
}

location parse_tactic_location(parser & p) {
    if (p.curr_is_token(get_in_tk())) {
        p.next();
        if (p.curr_is_token(get_star_tk())) {
            p.next();
            if (p.curr_is_token(get_turnstile_tk())) {
                p.next();
                if (p.curr_is_token(get_star_tk())) {
                    // in * |- *
                    return location::mk_everywhere();
                } else {
                    // in * |-
                    return location::mk_all_hypotheses();
                }
            } else {
                // in *
                return location::mk_everywhere();
            }
        } else {
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
            if (p.curr_is_token(get_turnstile_tk())) {
                occurrence goal_occ = parse_occurrence(p);
                return location::mk_at(goal_occ, hyps, hyp_occs);
            } else {
                return location::mk_hypotheses_at(hyps, hyp_occs);
            }
        }
    } else if (p.curr_is_token(get_at_tk())) {
        occurrence o = parse_occurrence(p);
        return location::mk_goal_at(o);
    } else {
        return location::mk_goal_only();
    }
}
}
