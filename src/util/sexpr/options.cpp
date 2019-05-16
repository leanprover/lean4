/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <string>
#include "runtime/sstream.h"
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
    case StringOption: out << "String"; break;
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

unsigned options::get_unsigned(name const & n, unsigned default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_int(r) ? static_cast<unsigned>(to_int(r)) : default_value;
}

bool options::get_bool(name const & n, bool default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_bool(r) ? to_bool(r) != 0 : default_value;
}

char const * options::get_string(name const & n, char const * default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_string(r) ? to_string(r).c_str() : default_value;
}

sexpr options::get_sexpr(char const * n, sexpr const & default_value) const {
    sexpr const * r = find(m_value, [&](sexpr const & p) { return to_name(head(p)) == n; });
    return r == nullptr ? default_value : tail(*r);
}

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

void options::for_each(std::function<void(name const &)> const & fn) const {
    ::lean::for_each(m_value, [&](sexpr const & p) {
            fn(to_name(head(p)));
        });
}
}
