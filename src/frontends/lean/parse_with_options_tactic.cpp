/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "library/tactic/with_options_tactic.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/util.h"

namespace lean {
expr parse_with_options_tactic(parser & p) {
    options o;
    p.check_token_next(get_lbracket_tk(), "invalid 'with_options' tactical, '[' expected");
    while (true) {
        auto id_kind = parse_option_name(p, "invalid 'with_options' tactical, identifier (i.e., option name) expected");
        name id       = id_kind.first;
        option_kind k = id_kind.second;
        if (k == BoolOption) {
            if (p.curr_is_token_or_id(get_true_tk()))
                o = o.update(id, true);
            else if (p.curr_is_token_or_id(get_false_tk()))
                o = o.update(id, false);
            else
                throw parser_error("invalid Boolean option value, 'true' or 'false' expected", p.pos());
            p.next();
        } else if (k == StringOption) {
            if (!p.curr_is_string())
                throw parser_error("invalid option value, given option is not a string", p.pos());
            o = o.update(id, p.get_str_val());
            p.next();
        } else if (k == DoubleOption) {
            o = o.update(id, p.parse_double());
        } else if (k == UnsignedOption || k == IntOption) {
            o = o.update(id, p.parse_small_nat());
        } else {
            throw parser_error("invalid option value, 'true', 'false', string, integer or decimal value expected", p.pos());
        }
        if (!p.curr_is_token(get_comma_tk()))
            break;
        p.next();
    }
    p.check_token_next(get_rbracket_tk(), "invalid 'with_options' tactical, ']' expected");
    expr t = p.parse_tactic(get_max_prec());
    return mk_with_options_tactic_expr(o, t);
}
}
