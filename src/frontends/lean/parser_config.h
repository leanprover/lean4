/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/parse_table.h"

namespace lean {
token_table const & get_token_table(environment const & env);
parse_table const & get_nud_parse_table(environment const & env);
parse_table const & get_led_parse_table(environment const & env);

environment update_token_table(environment const & env, token_table const & t);
environment update_nud_parse_table(environment const & env, parse_table const & t);
environment update_led_parse_table(environment const & env, parse_table const & t);
environment update_parse_config(environment const & env, token_table const & tk, parse_table const & nud, parse_table const & led);
}
