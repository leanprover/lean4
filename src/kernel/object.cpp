/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/object.h"
#include "kernel/environment.h"

namespace lean {
typedef std::unordered_map<std::string, object_cell::reader> object_readers;
static std::unique_ptr<object_readers> g_object_readers;
object_readers & get_object_readers() {
    if (!g_object_readers)
        g_object_readers.reset(new object_readers());
    return *(g_object_readers.get());
}

void object_cell::register_deserializer(std::string const & k, reader rd) {
    object_readers & readers = get_object_readers();
    lean_assert(readers.find(k) == readers.end());
    readers[k] = rd;
}
void read_object(environment const & env, io_state const & ios, std::string const & k, deserializer & d) {
    object_readers & readers = get_object_readers();
    auto it = readers.find(k);
    lean_assert(it != readers.end());
    it->second(env, ios, d);
}

neutral_object_cell::neutral_object_cell():object_cell(object_kind::Neutral) {}

serializer & operator<<(serializer & s, param_names const & ps) {
    return write_list<name>(s, ps);
}

param_names read_params(deserializer & d) {
    return read_list<name>(d);
}

/**
   \brief Parametric kernel objects.
*/
class parametric_object_cell : public object_cell {
    name         m_name;
    param_names  m_params;
    level_cnstrs m_cnstrs;
    expr         m_type;
public:
    parametric_object_cell(object_kind k, name const & n, param_names const & params, level_cnstrs const & cs, expr const & t):
        object_cell(k), m_name(n), m_params(params), m_cnstrs(cs), m_type(t) {}
    virtual ~parametric_object_cell() {}

    virtual bool has_name() const { return true; }
    virtual name get_name() const { return m_name; }
    virtual expr get_type() const { return m_type; }
    virtual param_names const & get_params() const { return m_params; }
    virtual level_cnstrs const & get_level_cnstrs() const { return m_cnstrs; }
};

/**
   \brief Base class for Axioms and Variable declarations.
*/
class postulate_object_cell : public parametric_object_cell {
public:
    postulate_object_cell(name const & n, param_names const & params, level_cnstrs const & cs, expr const & t):
        parametric_object_cell(object_kind::Postulate, n, params, cs, t) {}
};

/**
   \brief Axioms
*/
class axiom_object_cell : public postulate_object_cell {
public:
    axiom_object_cell(name const & n, param_names const & params, level_cnstrs const & cs, expr const & t):
        postulate_object_cell(n, params, cs, t) {}
    virtual char const * keyword() const { return "axiom"; }
    virtual bool is_axiom() const { return true; }
    virtual void write(serializer & s) const { s << "ax" << get_name() << get_params() << get_level_cnstrs() << get_type(); }
};
static void read_axiom(environment const & env, io_state const &, deserializer & d) {
    name n          = read_name(d);
    param_names ps  = read_params(d);
    level_cnstrs cs = read_level_cnstrs(d);
    expr t          = read_expr(d);
    env->add_axiom(n, ps, cs, t);
}
static object_cell::register_deserializer_fn axiom_ds("ax", read_axiom);


/**
   \brief Variable (aka constant) declaration
*/
class variable_decl_object_cell : public postulate_object_cell {
public:
    variable_decl_object_cell(name const & n, param_names const & params, level_cnstrs const & cs, expr const & t):
        postulate_object_cell(n, params, cs, t) {}
    virtual char const * keyword() const { return "variable"; }
    virtual bool is_var_decl() const { return true; }
    virtual void write(serializer & s) const { s << "var" << get_name() << get_params() << get_level_cnstrs() << get_type(); }
};
static void read_variable(environment const & env, io_state const &, deserializer & d) {
    name n          = read_name(d);
    param_names ps  = read_params(d);
    level_cnstrs cs = read_level_cnstrs(d);
    expr t          = read_expr(d);
    env->add_var(n, ps, cs, t);
}
static object_cell::register_deserializer_fn var_decl_ds("var", read_variable);

/**
   \brief Base class for definitions: theorems and definitions.
*/
class definition_object_cell : public parametric_object_cell {
    expr     m_value;
    bool     m_opaque;
    unsigned m_weight;
public:
    definition_object_cell(name const & n, param_names const & params, level_cnstrs const & cs, expr const & t, expr const & v, unsigned weight):
        parametric_object_cell(object_kind::Definition, n, params, cs, t), m_value(v), m_opaque(false), m_weight(weight) {}
    virtual ~definition_object_cell() {}

    virtual bool is_definition() const   { return true; }
    virtual bool is_opaque() const       { return m_opaque; }
    virtual void set_opaque(bool f)      { m_opaque = f; }
    virtual expr get_value() const       { return m_value; }
    virtual char const * keyword() const { return "definition"; }
    virtual unsigned get_weight() const  { return m_weight; }
    virtual void write(serializer & s) const {
        s << "def" << get_name() << get_params() << get_level_cnstrs() << get_type() << get_value();
    }
};
static void read_definition(environment const & env, io_state const &, deserializer & d) {
    name n          = read_name(d);
    param_names ps  = read_params(d);
    level_cnstrs cs = read_level_cnstrs(d);
    expr t          = read_expr(d);
    expr v          = read_expr(d);
    env->add_definition(n, ps, cs, t, v);
}
static object_cell::register_deserializer_fn definition_ds("def", read_definition);

/**
   \brief Theorems
*/
class theorem_object_cell : public definition_object_cell {
public:
    theorem_object_cell(name const & n, param_names const & params, level_cnstrs const & cs, expr const & t, expr const & v):
        definition_object_cell(n, params, cs, t, v, 0) {
        set_opaque(true);
    }
    virtual char const * keyword() const { return "theorem"; }
    virtual bool is_theorem() const { return true; }
    virtual void write(serializer & s) const {
        s << "th" << get_name() << get_params() << get_level_cnstrs() << get_type() << get_value();
    }
};
static void read_theorem(environment const & env, io_state const &, deserializer & d) {
    name n          = read_name(d);
    param_names ps  = read_params(d);
    level_cnstrs cs = read_level_cnstrs(d);
    expr t          = read_expr(d);
    expr v          = read_expr(d);
    env->add_theorem(n, ps, cs, t, v);
}
static object_cell::register_deserializer_fn theorem_ds("th", read_theorem);

object mk_definition(name const & n, param_names const & ps, level_cnstrs const & cs, expr const & t, expr const & v, unsigned weight) {
    return object(new definition_object_cell(n, ps, cs, t, v, weight));
}
object mk_theorem(name const & n, param_names const & ps, level_cnstrs const & cs, expr const & t, expr const & v) {
    return object(new theorem_object_cell(n, ps, cs, t, v));
}
object mk_axiom(name const & n, param_names const & ps, level_cnstrs const & cs, expr const & t) {
    return object(new axiom_object_cell(n, ps, cs, t));
}
object mk_var_decl(name const & n, param_names const & ps, level_cnstrs const & cs, expr const & t) {
    return object(new variable_decl_object_cell(n, ps, cs, t));
}
}
