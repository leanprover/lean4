/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include "util/sexpr/options.h"

namespace lean {
class expr;
class environment;
class abstract_type_context;

name const & get_formatter_hide_full_terms_name();
bool get_formatter_hide_full_terms(options const & opts);

class formatter {
    std::function<format(expr const &, options const &)> m_fn;
    options                             m_options;
public:
    formatter(options const & o, std::function<format(expr const &, options const &)> const & fn):m_fn(fn), m_options(o) {}
    format operator()(expr const & e) const { return m_fn(e, m_options); }
    options const & get_options() const { return m_options; }
    formatter update_options(options const & o) const { return formatter(o, m_fn); }
    template<typename T>
    formatter update_option_if_undef(name const & n, T v) const { return formatter(m_options.update_if_undef(n, v), m_fn); }
};

typedef std::function<formatter(environment const &, options const &, abstract_type_context &)> formatter_factory;

std::ostream & operator<<(std::ostream & out, expr const & e);

typedef std::function<format(formatter const &)> pp_fn;

void set_print_fn(std::function<void(std::ostream &, expr const &)> const & fn);

void initialize_formatter();
void finalize_formatter();
}
