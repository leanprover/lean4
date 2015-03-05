/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sexpr/option_declarations.h"
#include "kernel/instantiate.h"
#include "library/unifier.h"
#include "library/type_util.h"
#include "library/reducible.h"
#include "library/flycheck.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"

#ifndef LEAN_DEFAULT_FIND_MAX_STEPS
#define LEAN_DEFAULT_FIND_MAX_STEPS 128
#endif

#ifndef LEAN_DEFAULT_FIND_EXPENSIVE
#define LEAN_DEFAULT_FIND_EXPENSIVE false
#endif


namespace lean {
static name * g_find_max_steps = nullptr;
static name * g_find_expensive = nullptr;

void initialize_find_cmd() {
    g_find_max_steps = new name{"find_decl", "max_steps"};
    g_find_expensive = new name{"find_decl", "expensive"};
    register_unsigned_option(*g_find_max_steps, LEAN_DEFAULT_FIND_MAX_STEPS,
                         "(find_decl) maximum number of steps to be performed when trying to match the type of a declaration");
    register_bool_option(*g_find_expensive, LEAN_DEFAULT_FIND_EXPENSIVE,
                         "(find_decl) if true, then matcher will unfold definitions, perform reductions, and higher-order matching");
}

void finalize_find_cmd() {
    delete g_find_max_steps;
    delete g_find_expensive;
}

unsigned get_find_max_steps(options const & opts) {
    return opts.get_unsigned(*g_find_max_steps, LEAN_DEFAULT_FIND_MAX_STEPS);
}

bool get_find_expensive(options const & opts) {
    return opts.get_bool(*g_find_expensive, LEAN_DEFAULT_FIND_EXPENSIVE);
}


bool match_pattern(type_checker & tc, expr const & pattern, declaration const & d, unsigned max_steps, bool cheap) {
    name_generator ngen = tc.mk_ngen();
     buffer<level> ls;
    unsigned num_ls = d.get_num_univ_params();
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
        cfg.m_max_steps            = max_steps;
        cfg.m_kind                 = cheap ? unifier_kind::Cheap : unifier_kind::Liberal;
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
    {
        bool save_options = true;
        parser::local_scope scope(p, save_options);
        p.set_option(get_elaborator_ignore_instances_name(), true);
        std::tie(e, ls) = parse_local_expr(p);
    }
    buffer<std::string> pos_names, neg_names;
    parse_filters(p, pos_names, neg_names);
    environment env = p.env();
    auto tc = mk_opaque_type_checker(env, p.mk_ngen());
    flycheck_information info(p.regular_stream());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
    }
    p.regular_stream() << "find_decl result:\n";

    unsigned max_steps = get_find_max_steps(p.get_options());
    bool cheap         = !get_find_expensive(p.get_options());
    bool found = false;
    env.for_each_declaration([&](declaration const & d) {
            if (std::all_of(pos_names.begin(), pos_names.end(),
                            [&](std::string const & pos) { return is_part_of(pos, d.get_name()); }) &&
                std::all_of(neg_names.begin(), neg_names.end(),
                            [&](std::string const & neg) { return !is_part_of(neg, d.get_name()); }) &&
                match_pattern(*tc.get(), e, d, max_steps, cheap)) {
                found = true;
                p.regular_stream() << " " << get_decl_short_name(d.get_name(), env) << " : " << d.get_type() << endl;
            }
        });
    if (!found)
        p.regular_stream() << "no matches\n";
    return env;
}

}
