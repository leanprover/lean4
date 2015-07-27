/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "library/scoped_ext.h"
#include "library/tactic/exact_tactic.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/simplifier/simp_rule_set.h"
#include "library/simplifier/simp_tactic.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/parse_tactic_location.h"
#include "frontends/lean/tokens.h"

namespace lean {
expr parse_simp_tactic(parser & p) {
    buffer<expr>   lemmas;
    buffer<name>   ns;
    buffer<name>   hiding;
    optional<expr> tac;
    while (true) {
        if (p.curr_is_token(get_lbracket_tk())) {
            p.next();
            while (true) {
                if (p.curr_is_identifier()) {
                    auto id_pos = p.pos();
                    name id     = p.get_name_val();
                    p.next();
                    optional<name> real_ns = to_valid_namespace_name(p.env(), id);
                    if (real_ns) {
                        ns.push_back(*real_ns);
                    } else {
                        expr left    = p.id_to_expr(id, id_pos);
                        unsigned rbp = 0;
                        while (rbp < p.curr_expr_lbp()) {
                            left = p.parse_led(left);
                        }
                        lemmas.push_back(left);
                    }
                } else {
                    lemmas.push_back(p.parse_expr());
                }
                if (!p.curr_is_token(get_comma_tk()))
                    break;
                p.next();
            }
            p.check_token_next(get_rbracket_tk(), "invalid 'simp' tactic, ']' expected");
        } else if (p.curr_is_token_or_id(get_hiding_tk())) {
            p.next();
            p.check_token_next(get_lbracket_tk(), "invalid 'simp' tactic, '[' expected");
            while (true) {
                name id = p.check_constant_next("invalid 'simp' tactic, constant expected");
                hiding.push_back(id);
                if (!p.curr_is_token(get_comma_tk()))
                    break;
                p.next();
            }
            p.check_token_next(get_rbracket_tk(), "invalid 'simp' tactic, ']' expected");
        } else if (p.curr_is_token_or_id(get_using_tk())) {
            if (tac)
                throw parser_error("invalid 'simp' tactic, auxiliary tactic was already specified", p.pos());
            p.next();
            tac = p.parse_tactic(get_max_prec());
        } else {
            break;
        }
    }
    location loc = parse_tactic_location(p);

    // Remark: simp_tac is the actual result
    return mk_simp_tactic_expr(lemmas, ns, hiding, tac, loc);
}
}
