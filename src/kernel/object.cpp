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

/**
   \brief Named kernel objects.

   \remark All nonneutral objects have names.
*/
class named_object_cell : public object_cell {
    name m_name;
public:
    named_object_cell(object_kind k, name const & n):object_cell(k), m_name(n) {}
    virtual ~named_object_cell() {}

    virtual bool has_name() const { return true; }
    virtual name get_name() const { return m_name; }
};

/**
   \brief Universe variable name declaration.
*/
class uvar_declaration_object_cell : public named_object_cell {
    level m_level;
public:
    uvar_declaration_object_cell(name const & n, level const & l):
        named_object_cell(object_kind::UVarDeclaration, n), m_level(l) {}
    virtual ~uvar_declaration_object_cell() {}

    virtual bool has_cnstr_level() const  { return true; }
    virtual level get_cnstr_level() const { return m_level; }
    virtual char const * keyword() const  { return "Universe"; }
    virtual void write(serializer & s) const { s << "Universe" << get_name() << m_level; }
};
static void read_uvar_decl(environment const & env, io_state const &, deserializer & d) {
    name n    = read_name(d);
    level lvl = read_level(d);
    env->add_uvar(n, lvl);
}
static object_cell::register_deserializer_fn uvar_ds("Universe", read_uvar_decl);

/**
   \brief Builtin object.
*/
class builtin_object_cell : public object_cell {
    expr m_value;
    bool m_opaque;
public:
    builtin_object_cell(expr const & v):
        object_cell(object_kind::Builtin), m_value(v), m_opaque(false) { lean_assert(is_value(v)); }
    virtual ~builtin_object_cell() {}
    virtual bool has_name() const        { return true; }
    virtual name get_name() const        { return to_value(m_value).get_name(); }
    virtual bool has_type() const        { return true; }
    virtual expr get_type() const        { return to_value(m_value).get_type(); }
    virtual bool is_definition() const   { return true; }
    virtual bool is_opaque() const       { return m_opaque; }
    virtual void set_opaque(bool f)      { m_opaque = f; }
    virtual expr get_value() const       { return m_value; }
    virtual char const * keyword() const { return "Builtin"; }
    virtual bool is_builtin() const      { return true; }
    virtual void write(serializer & s) const { s << "Builtin" << m_value; }
};
static void read_builtin(environment const & env, io_state const &, deserializer & d) {
    expr v      = read_expr(d);
    env->add_builtin(v);
}
static object_cell::register_deserializer_fn builtin_ds("Builtin", read_builtin);


/**
   \brief Base class for capturing a set of builtin objects such as
      a) the natural numbers 0, 1, 2, ...
      b) the integers 0, -1, 1, -2, 2, ...
      c) the reals
      d) ...
   This object represents an infinite set of declarations.
   This is just a markup to sign that an environment depends on a
   particular builtin set of values.
*/
class builtin_set_object_cell : public object_cell {
    // The representative is only used to test if a builtin value
    // is in the same C++ class of the representative.
    expr m_representative;
public:
    builtin_set_object_cell(expr const & r):object_cell(object_kind::BuiltinSet), m_representative(r) { lean_assert(is_value(r)); }
    virtual ~builtin_set_object_cell() {}
    virtual bool has_name() const { return true; }
    virtual name get_name() const { return to_value(m_representative).get_name(); }
    virtual bool is_builtin_set() const { return true; }
    virtual bool in_builtin_set(expr const & v) const { return is_value(v) && typeid(to_value(v)) == typeid(to_value(m_representative)); }
    virtual char const * keyword() const { return "BuiltinSet"; }
    virtual void write(serializer & s) const { s << "BuiltinSet" << m_representative; }
};
static void read_builtin_set(environment const & env, io_state const &, deserializer & d) {
    env->add_builtin_set(read_expr(d));
}
static object_cell::register_deserializer_fn builtin_set_ds("BuiltinSet", read_builtin_set);

/**
   \brief Named (and typed) kernel objects.
*/
class named_typed_object_cell : public named_object_cell {
    expr m_type;
public:
    named_typed_object_cell(object_kind k, name const & n, expr const & t):
        named_object_cell(k, n), m_type(t) {}
    virtual ~named_typed_object_cell() {}

    virtual bool has_type() const { return true; }
    virtual expr get_type() const { return m_type; }
};

/**
   \brief Base class for Axioms and Variable declarations.
*/
class postulate_object_cell : public named_typed_object_cell {
public:
    postulate_object_cell(name const & n, expr const & t):
        named_typed_object_cell(object_kind::Postulate, n, t) {}
};

/**
   \brief Axioms
*/
class axiom_object_cell : public postulate_object_cell {
public:
    axiom_object_cell(name const & n, expr const & t):postulate_object_cell(n, t) {}
    virtual char const * keyword() const { return "Axiom"; }
    virtual bool is_axiom() const { return true; }
    virtual void write(serializer & s) const { s << "Axiom" << get_name() << get_type(); }
};
static void read_axiom(environment const & env, io_state const &, deserializer & d) {
    name n    = read_name(d);
    expr t    = read_expr(d);
    env->add_axiom(n, t);
}
static object_cell::register_deserializer_fn axiom_ds("Axiom", read_axiom);


/**
   \brief Variable (aka constant) declaration
*/
class variable_decl_object_cell : public postulate_object_cell {
public:
    variable_decl_object_cell(name const & n, expr const & t):postulate_object_cell(n, t) {}
    virtual char const * keyword() const { return "Variable"; }
    virtual bool is_var_decl() const { return true; }
    virtual void write(serializer & s) const { s << "Variable" << get_name() << get_type(); }
};
static void read_variable(environment const & env, io_state const &, deserializer & d) {
    name n    = read_name(d);
    expr t    = read_expr(d);
    env->add_var(n, t);
}
static object_cell::register_deserializer_fn var_decl_ds("Variable", read_variable);

/**
   \brief Base class for definitions: theorems and definitions.
*/
class definition_object_cell : public named_typed_object_cell {
    expr     m_value;
    bool     m_opaque;
    unsigned m_weight;
public:
    definition_object_cell(name const & n, expr const & t, expr const & v, unsigned weight):
        named_typed_object_cell(object_kind::Definition, n, t), m_value(v), m_weight(weight) {}
    virtual ~definition_object_cell() {}

    virtual bool is_definition() const   { return true; }
    virtual bool is_opaque() const       { return m_opaque; }
    virtual void set_opaque(bool f)      { m_opaque = f; }
    virtual expr get_value() const       { return m_value; }
    virtual char const * keyword() const { return "Definition"; }
    virtual unsigned get_weight() const  { return m_weight; }
    virtual void write(serializer & s) const { s << "Definition" << get_name() << get_type() << get_value(); }
};
static void read_definition(environment const & env, io_state const &, deserializer & d) {
    name n    = read_name(d);
    expr t    = read_expr(d);
    expr v    = read_expr(d);
    env->add_definition(n, t, v);
}
static object_cell::register_deserializer_fn definition_ds("Definition", read_definition);

/**
   \brief Theorems
*/
class theorem_object_cell : public definition_object_cell {
public:
    theorem_object_cell(name const & n, expr const & t, expr const & v):
        definition_object_cell(n, t, v, 0) {
        set_opaque(true);
    }
    virtual char const * keyword() const { return "Theorem"; }
    virtual bool is_theorem() const { return true; }
    virtual void write(serializer & s) const { s << "Theorem" << get_name() << get_type() << get_value(); }
};
static void read_theorem(environment const & env, io_state const &, deserializer & d) {
    name n    = read_name(d);
    expr t    = read_expr(d);
    expr v    = read_expr(d);
    env->add_theorem(n, t, v);
}
static object_cell::register_deserializer_fn theorem_ds("Theorem", read_theorem);

object mk_uvar_decl(name const & n, level const & l) { return object(new uvar_declaration_object_cell(n, l)); }
object mk_definition(name const & n, expr const & t, expr const & v, unsigned weight) { return object(new definition_object_cell(n, t, v, weight)); }
object mk_theorem(name const & n, expr const & t, expr const & v) { return object(new theorem_object_cell(n, t, v)); }
object mk_axiom(name const & n, expr const & t) { return object(new axiom_object_cell(n, t)); }
object mk_var_decl(name const & n, expr const & t) { return object(new variable_decl_object_cell(n, t)); }
object mk_builtin(expr const & v) { return object(new builtin_object_cell(v)); }
object mk_builtin_set(expr const & r) { return object(new builtin_set_object_cell(r)); }
}
