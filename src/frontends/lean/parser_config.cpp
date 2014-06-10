/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/parser_config.h"

namespace lean {
struct parser_ext : public environment_extension {
    // Configuration for a Pratt's parser
    token_table m_tokens;
    parse_table m_nud;
    parse_table m_led;
    parser_ext() {
        m_tokens = mk_default_token_table();
    }
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

token_table const & get_token_table(environment const & env) {
    return get_extension(env).m_tokens;
}

parse_table const & get_nud_parse_table(environment const & env) {
    return get_extension(env).m_nud;
}

parse_table const & get_led_parse_table(environment const & env) {
    return get_extension(env).m_led;
}

environment update_token_table(environment const & env, token_table const & t) {
    parser_ext ext = get_extension(env);
    ext.m_tokens = t;
    return update(env, ext);
}

environment update_nud_parse_table(environment const & env, parse_table const & t) {
    parser_ext ext = get_extension(env);
    ext.m_nud = t;
    return update(env, ext);
}

environment update_led_parse_table(environment const & env, parse_table const & t) {
    parser_ext ext = get_extension(env);
    ext.m_led = t;
    return update(env, ext);
}

environment update_parse_config(environment const & env, token_table const & tk, parse_table const & nud, parse_table const & led) {
    parser_ext ext = get_extension(env);
    ext.m_tokens = tk;
    ext.m_nud    = nud;
    ext.m_led    = led;
    return update(env, ext);
}
}
