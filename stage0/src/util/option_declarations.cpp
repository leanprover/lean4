/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/option_declarations.h"

namespace lean {
void option_declaration::display_value(std::ostream & out, options const & o) const {
    bool contains = false;
    if (o.contains(get_name())) {
/*
        sexpr s = o.get_sexpr(get_name());
        switch (kind()) {
        case BoolOption:
            if (!is_nil(s) && is_bool(s)) {
                out << (to_bool(s) ? "true" : "false");
                contains = true;
            }
            break;
        case IntOption:
            if (!is_nil(s) && is_int(s)) {
                out << to_int(s);
                contains = true;
            }
            break;
        case UnsignedOption:
            if (!is_nil(s) && is_int(s)) {
                out << static_cast<unsigned>(to_int(s));
                contains = true;
            }
            break;
        case StringOption:
            if (!is_nil(s) && is_string(s)) {
                out << to_string(s);
                contains = true;
            }
            break;
        }
*/
    }
    if (!contains)
        out << get_default_value();
}

static option_declarations * g_option_declarations = nullptr;
static mutex *               g_option_declarations_guard = nullptr;

void initialize_option_declarations() {
    g_option_declarations       = new option_declarations();
    g_option_declarations_guard = new mutex();
}

void finalize_option_declarations() {
    delete g_option_declarations;
    delete g_option_declarations_guard;
}

option_declarations get_option_declarations() {
    option_declarations r;
    {
        unique_lock<mutex> lock(*g_option_declarations_guard);
        r = *g_option_declarations;
    }
    return r;
}

void register_option(name const & n, data_value_kind k, char const * default_value, char const * description) {
    unique_lock<mutex> lock(*g_option_declarations_guard);
    g_option_declarations->insert(n, option_declaration(n, k, default_value, description));
}
}
