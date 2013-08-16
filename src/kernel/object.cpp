/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "object.h"
#include "environment.h"

namespace lean {
object::~object() {}
void object::display(std::ostream & out, environment const & env) const { out << pp(env); }

anonymous_object::~anonymous_object() {}
bool         anonymous_object::has_name() const      { return false; }
name const & anonymous_object::get_name() const      { lean_unreachable(); return name::anonymous(); }
bool         anonymous_object::has_type() const      { return false; }
expr const & anonymous_object::get_type() const      { lean_unreachable(); return expr::null(); }
bool         anonymous_object::is_definition() const { return false; }
bool         anonymous_object::is_opaque() const     { lean_unreachable(); return false; }
expr const & anonymous_object::get_value() const     { lean_unreachable(); return expr::null(); }

named_object::named_object(name const & n, expr const & t):m_name(n), m_type(t) {}
named_object::~named_object() {}
bool         named_object::has_name() const      { return true; }
name const & named_object::get_name() const      { return m_name; }
bool         named_object::has_type() const      { return true; }
expr const & named_object::get_type() const      { return m_type; }

char const * definition::g_keyword = "Definition";
definition::definition(name const & n, expr const & t, expr const & v, bool opaque):named_object(n, t), m_value(v), m_opaque(opaque) {}
definition::~definition() {}
char const * definition::keyword() const       { return g_keyword; }
bool         definition::is_definition() const { return true; }
bool         definition::is_opaque() const     { return m_opaque; }
expr const & definition::get_value() const     { return m_value; }
format       definition::pp(environment const & env) const {
    expr_formatter & fmt = env.get_formatter();
    format def = format{highlight_command(format(keyword())), space(), format(get_name()), space(), colon(), space(),
                        fmt(get_type()), format(" :="), line(), fmt(get_value())};
    return group(fmt.nest(def));
}

char const * theorem::g_keyword = "Theorem";
theorem::theorem(name const & n, expr const & t, expr const & v):definition(n, t, v, true) {}
theorem::~theorem() {}
char const * theorem::keyword() const { return g_keyword; }

fact::fact(name const & n, expr const & t):named_object(n, t) {}
fact::~fact() {}
bool         fact::is_definition() const { return false; }
bool         fact::is_opaque() const     { lean_unreachable(); return false; }
expr const & fact::get_value() const     { lean_unreachable(); return expr::null(); }
format fact::pp(environment const & env) const {
    expr_formatter & fmt = env.get_formatter();
    format def = format{highlight_command(format(keyword())), space(), format(get_name()), space(), colon(), space(), fmt(get_type())};
    return group(fmt.nest(def));
}

char const * axiom::g_keyword = "Axiom";
axiom::axiom(name const & n, expr const & t):fact(n, t) {}
axiom::~axiom() {}
char const * axiom::keyword() const { return g_keyword; }

char const * variable::g_keyword = "Variable";
variable::variable(name const & n, expr const & t):fact(n, t) {}
variable::~variable() {}
char const * variable::keyword() const { return g_keyword; }
}

