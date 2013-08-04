/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "builtin.h"

namespace lean {

class bool_type_value : public value {
public:
    static char const * g_kind;
    virtual ~bool_type_value() {}
    char const * kind() const { return g_kind; }
    virtual expr get_type() const { return type(level()); }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const { return false; }
    virtual bool operator==(value const & other) const { return other.kind() == kind(); }
    virtual void display(std::ostream & out) const { out << "bool"; }
    virtual format pp() const { return format("bool"); }
    virtual unsigned hash() const { return 17; }
};

char const * bool_type_value::g_kind = "bool";

expr bool_type() {
    static thread_local expr r;
    if (!r)
        r = to_expr(*(new bool_type_value()));
    return r;
}

bool is_bool_type(expr const & e) {
    return is_value(e) && to_value(e).kind() == bool_type_value::g_kind;
}

class bool_value_value : public value {
    bool m_val;
public:
    static char const * g_kind;
    bool_value_value(bool v):m_val(v) {}
    virtual ~bool_value_value() {}
    char const * kind() const { return g_kind; }
    virtual expr get_type() const { return bool_type(); }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const { return false; }
    virtual bool operator==(value const & other) const {
        return other.kind() == kind() && m_val == static_cast<bool_value_value const &>(other).m_val;
    }
    virtual void display(std::ostream & out) const { out << (m_val ? "true" : "false"); }
    virtual format pp() const { return format(m_val ? "true" : "false"); }
    virtual unsigned hash() const { return m_val ? 3 : 5; }
    bool get_val() const { return m_val; }
};

char const * bool_value_value::g_kind = "bool_value";

expr bool_value(bool v) {
    return to_expr(*(new bool_value_value(v)));
}

bool is_bool_value(expr const & e) {
    return is_value(e) && to_value(e).kind() == bool_value_value::g_kind;
}

bool to_bool(expr const & e) {
    lean_assert(is_bool_value(e));
    return static_cast<bool_value_value const &>(to_value(e)).get_val();
}

bool is_true(expr const & e) {
    return is_bool_value(e) && to_bool(e);
}

bool is_false(expr const & e) {
    return is_bool_value(e) && !to_bool(e);
}

}
