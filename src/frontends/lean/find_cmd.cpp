/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/instantiate.h"
#include "library/unifier.h"
#include "library/type_util.h"
#include "library/reducible.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"

namespace lean {
bool match_pattern(type_checker & tc, expr const & pattern, declaration const & d) {
    name_generator ngen = tc.mk_ngen();
     buffer<level> ls;
    unsigned num_ls = length(d.get_univ_params());
    for (unsigned i = 0; i < num_ls; i++)
        ls.push_back(mk_meta_univ(ngen.next()));
    expr dt        = instantiate_type_univ_params(d, to_list(ls.begin(), ls.end()));

    unsigned num_e = get_expect_num_args(tc, pattern);
    unsigned num_d = get_expect_num_args(tc, dt);
    if (num_e > num_d)
        return false;
    for (unsigned i = 0; i < num_d - num_e; i++) {
        dt         = tc.whnf(dt).first;
        expr local = mk_local(ngen.next(), binding_domain(dt));
        dt         = instantiate(binding_body(dt), local);
    }
    try {
        unifier_config cfg;
        cfg.m_max_steps            = 128;
        cfg.m_cheap                = true;
        cfg.m_ignore_context_check = true;
        auto r = unify(tc.env(), pattern, dt, tc.mk_ngen(), true, substitution(), cfg);
        return static_cast<bool>(r.pull());
    } catch (exception&) {
        return false;
    }
}

static void parse_filters(parser & p, buffer<std::string> & pos_names, buffer<std::string> & neg_names) {
    name plus("+"); name minus("-");
    while (p.curr_is_token(get_comma_tk())) {
        p.next();
        if (p.curr_is_token(plus)) {
            p.next();
            pos_names.push_back(p.check_id_next("invalid find_decl command, identifier expected").to_string());
        } else if (p.curr_is_token(minus)) {
            p.next();
            neg_names.push_back(p.check_id_next("invalid find_decl command, identifier expected").to_string());
        } else {
            pos_names.push_back(p.check_id_next("invalid find_decl command, '+', '-', or identifier expected").to_string());
        }
    }
}

environment find_cmd(parser & p) {
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    buffer<std::string> pos_names, neg_names;
    parse_filters(p, pos_names, neg_names);
    environment env = p.env();
    auto tc = mk_opaque_type_checker(env, p.mk_ngen());
    p.regular_stream() << "find_decl result:\n";
    bool found = false;
    env.for_each_declaration([&](declaration const & d) {
            if (std::all_of(pos_names.begin(), pos_names.end(),
                            [&](std::string const & pos) { return is_part_of(pos, d.get_name()); }) &&
                std::all_of(neg_names.begin(), neg_names.end(),
                            [&](std::string const & neg) { return !is_part_of(neg, d.get_name()); }) &&
                match_pattern(*tc.get(), e, d)) {
                found = true;
                p.regular_stream() << " " << get_decl_short_name(d.get_name(), env) << " : " << d.get_type() << endl;
            }
        });
    if (!found)
        p.regular_stream() << "no matches\n";
    return env;
}

}
