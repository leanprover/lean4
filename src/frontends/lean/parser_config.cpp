/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/parser_config.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/builtin_cmds.h"
#include "frontends/lean/builtin_tactic_cmds.h"

namespace lean {
parser_config::parser_config() {
    m_tokens      = mk_default_token_table();
    m_nud         = get_builtin_nud_table();
    m_led         = get_builtin_led_table();
    m_cmds        = get_builtin_cmds();
    m_tactic_cmds = get_builtin_tactic_cmds();
}

struct parser_ext : public environment_extension {
    // Configuration for a Pratt's parser
    parser_config m_cfg;
};

struct parser_ext_reg {
    unsigned m_ext_id;
    parser_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<parser_ext>()); }
};
static parser_ext_reg g_ext;
static parser_ext const & get_extension(environment const & env) {
    return static_cast<parser_ext const &>(env.get_extension(g_ext.m_ext_id));
}
static environment update(environment const & env, parser_ext const & ext) {
    return env.update(g_ext.m_ext_id, std::make_shared<parser_ext>(ext));
}
parser_config const & get_parser_config(environment const & env) {
    return get_extension(env).m_cfg;
}
environment update_parser_config(environment const & env, parser_config const & c) {
    parser_ext ext = get_extension(env);
    ext.m_cfg = c;
    return update(env, ext);
}
}
