/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "options.h"
#include "sexpr_funcs.h"

namespace lean {

bool options::empty() const {
    return is_nil(m_value);
}

bool options::size() const {
    return length(m_value);
}

bool options::contains(name const & n) const {
    return ::lean::contains(m_value, [&](sexpr const & p) { return to_name(head(p)) == n; });
}

bool options::contains(char const * n) const {
    return ::lean::contains(m_value, [&](sexpr const & p) { return to_name(head(p)) == n; });
}

sexpr const & options::get_sexpr(name const & n, sexpr const & default_value) const {
    sexpr const * r = find(m_value, [&](sexpr const & p) { return to_name(head(p)) == n; });
    return r == nullptr ? default_value : *r;
}

int options::get_int(name const & n, int default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_int(r) ? to_int(r) : default_value;
}

bool options::get_bool(name const & n, bool default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_bool(r) ? to_bool(r) != 0 : default_value;
}

double options::get_double(name const & n, double default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_double(r) ? to_double(r) : default_value;
}

sexpr const & options::get_sexpr(char const * n, sexpr const & default_value) const {
    sexpr const * r = find(m_value, [&](sexpr const & p) { return to_name(head(p)) == n; });
    return r == nullptr ? default_value : *r;
}

int options::get_int(char const * n, int default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_int(r) ? to_int(r) : default_value;
}

bool options::get_bool(char const * n, bool default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_bool(r) ? to_bool(r) != 0 : default_value;
}

double options::get_double(char const * n, double default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_double(r) ? to_double(r) : default_value;
}

constexpr char const * left_angle_bracket  = "\u27E8";
constexpr char const * right_angle_bracket = "\u27E9";
constexpr char const * arrow               = "\u21a6";

options options::update(name const & n, sexpr const & v) const {
    return options(cons(cons(sexpr(n), v), m_value));
}

format pp(options const & o) {
    // TODO
    return format();
}

std::ostream & operator<<(std::ostream & out, options const & o) {
    out << left_angle_bracket;
    bool first = true;
    foreach(o.m_value, [&](sexpr const & p) {
            if (first) first = false; else out << ", ";
            out << head(p) << " " << arrow << " " << tail(p);
        });
    out << right_angle_bracket;
    return out;
}
}
