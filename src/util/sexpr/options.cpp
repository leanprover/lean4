/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <string>
#include "util/sstream.h"
#include "util/sexpr/options.h"
#include "util/sexpr/option_declarations.h"
#include "util/sexpr/sexpr_fn.h"

#ifndef LEAN_DEFAULT_VERBOSE
#define LEAN_DEFAULT_VERBOSE true
#endif

namespace lean {
static name * g_verbose    = nullptr;
static name * g_max_memory = nullptr;
static name * g_timeout    = nullptr;

void initialize_options() {
    g_verbose    = new name("verbose");
    g_max_memory = new name("max_memory");
    g_timeout    = new name("timeout");
    register_bool_option(*g_verbose, LEAN_DEFAULT_VERBOSE, "disable/enable verbose messages");
    register_unsigned_option(*g_max_memory, LEAN_DEFAULT_MAX_MEMORY, "maximum amount of memory available for Lean in megabytes");
    register_unsigned_option(*g_timeout, 0, "the (deterministic) timeout is measured as the maximum of memory allocations (in thousands) per task, the default is unbounded");
}

void finalize_options() {
    delete g_verbose;
    delete g_max_memory;
    delete g_timeout;
}

name const & get_verbose_opt_name() {
    return *g_verbose;
}

name const & get_max_memory_opt_name() {
    return *g_max_memory;
}

name const & get_timeout_opt_name() {
    return *g_timeout;
}

bool get_verbose(options const & opts) {
    return opts.get_bool(*g_verbose, LEAN_DEFAULT_VERBOSE);
}

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

static char const * g_left_angle_bracket  = "⟨";
static char const * g_right_angle_bracket = "⟩";
static char const * g_arrow               = "↦";
static char const * g_assign              = ":=";

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

/**
   \brief Return a new set of options based on \c opts by adding the prefix \c prefix.

   The procedure throws an exception if \c opts contains an options (o, v), s.t. prefix + o is
   an unknown option in Lean.
*/
options add_prefix(name const & prefix, options const & opts) {
    option_declarations const & decls = get_option_declarations();
    return map(opts.m_value, [&](sexpr const & p) {
            name n = prefix + to_name(car(p));
            if (!decls.contains(n))
                throw exception(sstream() << "unknown option '" << n << "'");
            return cons(sexpr(n), cdr(p));
        });
}

options remove_all_with_prefix(name const & prefix, options const & opts) {
    sexpr r;
    for_each(opts.m_value, [&](sexpr const & p) {
            if (!is_prefix_of(prefix, to_name(car(p))))
                r = cons(p, r);
        });
    return options(r);
}

format pp(options const & o) {
    bool unicode = get_pp_unicode(o);
    format r;
    bool first = true;
    char const * arrow = unicode ? g_arrow : g_assign;
    for_each(o.m_value, [&](sexpr const & p) {
            if (first) { first = false; } else { r += comma(); r += line(); }
            name const & n = to_name(head(p));
            unsigned sz = n.size();
            unsigned indent = unicode ? sz+3 : sz+4;
            r += group(nest(indent, pp(head(p)) + space() + format(arrow) + space() + pp(tail(p))));
        });
    format open  = unicode ? format(g_left_angle_bracket) : lp();
    format close = unicode ? format(g_right_angle_bracket) : rp();
    return group(nest(1, open + r + close));
}

void options::for_each(std::function<void(name const &)> const & fn) const {
    ::lean::for_each(m_value, [&](sexpr const & p) {
            fn(to_name(head(p)));
        });
}

std::ostream & operator<<(std::ostream & out, options const & o) {
    bool unicode = get_pp_unicode(o);
    out << (unicode ? g_left_angle_bracket : "(");
    bool first = true;
    for_each(o.m_value, [&](sexpr const & p) {
            if (first) first = false; else out << ", ";
            out << head(p) << " " << (unicode ? g_arrow : g_assign) << " " << tail(p);
        });
    out << (unicode ? g_right_angle_bracket : ")");
    return out;
}
}
