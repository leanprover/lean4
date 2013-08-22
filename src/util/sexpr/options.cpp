/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include "options.h"
#include "option_declarations.h"
#include "sexpr_funcs.h"

namespace lean {
std::ostream & operator<<(std::ostream & out, option_kind k) {
    switch (k) {
    case BoolOption: out << "Bool"; break;
    case IntOption:  out << "Int"; break;
    case UnsignedOption: out << "Unsigned Int"; break;
    case DoubleOption: out << "Double"; break;
    case StringOption: out << "String"; break;
    case SExprOption: out << "S-Expression"; break;
    }
    return out;
}

static std::unique_ptr<option_declarations> g_option_declarations;

option_declarations & get_option_declarations_core() {
    if (!g_option_declarations)
        g_option_declarations.reset(new option_declarations());
    return *g_option_declarations;
}

option_declarations const & get_option_declarations() {
    return get_option_declarations_core();
}

mk_option_declaration::mk_option_declaration(name const & n, option_kind k, char const * default_value, char const * description) {
    get_option_declarations_core().insert(mk_pair(n, option_declaration(n, k, default_value, description)));
}

bool options::empty() const {
    return is_nil(m_value);
}

unsigned options::size() const {
    return length(m_value);
}

bool options::contains(name const & n) const {
    return ::lean::contains(m_value, [&](sexpr const & p) { return to_name(head(p)) == n; });
}

bool options::contains(char const * n) const {
    return ::lean::contains(m_value, [&](sexpr const & p) { return to_name(head(p)) == n; });
}

sexpr options::get_sexpr(name const & n, sexpr const & default_value) const {
    sexpr const * r = find(m_value, [&](sexpr const & p) { return to_name(head(p)) == n; });
    return r == nullptr ? default_value : tail(*r);
}

int options::get_int(name const & n, int default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_int(r) ? to_int(r) : default_value;
}

unsigned options::get_unsigned(name const & n, unsigned default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_int(r) ? static_cast<unsigned>(to_int(r)) : default_value;
}

bool options::get_bool(name const & n, bool default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_bool(r) ? to_bool(r) != 0 : default_value;
}

double options::get_double(name const & n, double default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_double(r) ? to_double(r) : default_value;
}

char const * options::get_string(name const & n, char const * default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_string(r) ? to_string(r).c_str() : default_value;
}

sexpr options::get_sexpr(char const * n, sexpr const & default_value) const {
    sexpr const * r = find(m_value, [&](sexpr const & p) { return to_name(head(p)) == n; });
    return r == nullptr ? default_value : tail(*r);
}

int options::get_int(char const * n, int default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_int(r) ? to_int(r) : default_value;
}

unsigned options::get_unsigned(char const * n, unsigned default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_int(r) ? static_cast<unsigned>(to_int(r)) : default_value;
}

bool options::get_bool(char const * n, bool default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_bool(r) ? to_bool(r) != 0 : default_value;
}

double options::get_double(char const * n, double default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_double(r) ? to_double(r) : default_value;
}

char const * options::get_string(char const * n, char const * default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_string(r) ? to_string(r).c_str() : default_value;
}

static char const * g_left_angle_bracket  = "\u27E8";
static char const * g_right_angle_bracket = "\u27E9";
static char const * g_arrow               = "\u21a6";

options options::update(name const & n, sexpr const & v) const {
    if (contains(n)) {
        return map(m_value, [&](sexpr p) {
                if (to_name(car(p)) == n)
                    return cons(car(p), v);
                else
                    return p;
            });
    } else {
        return options(cons(cons(sexpr(n), v), m_value));
    }
}

options join(options const & opts1, options const & opts2) {
    sexpr r = opts2.m_value;
    for_each(opts1.m_value, [&](sexpr const & p) {
            if (!opts2.contains(to_name(car(p))))
                r = cons(p, r);
        });
    return options(r);
}

format pp(options const & o) {
    format r;
    bool first = true;
    for_each(o.m_value, [&](sexpr const & p) {
            if (first) { first = false; } else { r += comma(); r += line(); }
            name const & n = to_name(head(p));
            unsigned sz = n.size();
            r += group(nest(sz+3, format{pp(head(p)), space(), format(g_arrow), space(), pp(tail(p))}));
        });
    return group(nest(1, format{format(g_left_angle_bracket), r, format(g_right_angle_bracket)}));
}

std::ostream & operator<<(std::ostream & out, options const & o) {
    out << g_left_angle_bracket;
    bool first = true;
    for_each(o.m_value, [&](sexpr const & p) {
            if (first) first = false; else out << ", ";
            out << head(p) << " " << g_arrow << " " << tail(p);
        });
    out << g_right_angle_bracket;
    return out;
}
}
