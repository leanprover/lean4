/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "object.h"
#include "environment.h"

namespace lean {
neutral_object_cell::neutral_object_cell():object_cell(object_kind::Neutral) {}
neutral_object_cell::~neutral_object_cell() {}
bool         neutral_object_cell::has_name() const        { return false; }
name const & neutral_object_cell::get_name() const        { lean_unreachable(); return name::anonymous(); }
bool         neutral_object_cell::has_cnstr_level() const { return false; }
level        neutral_object_cell::get_cnstr_level() const { lean_unreachable(); return level(); }
bool         neutral_object_cell::has_type() const        { return false; }
expr const & neutral_object_cell::get_type() const        { lean_unreachable(); return expr::null(); }
bool         neutral_object_cell::is_definition() const   { return false; }
bool         neutral_object_cell::is_opaque() const       { lean_unreachable(); return false; }
expr const & neutral_object_cell::get_value() const       { lean_unreachable(); return expr::null(); }

/**
   \brief Named kernel objects.

   \remark All nonneutral objects have names.
*/
class named_object_cell : public object_cell {
    name m_name;
public:
    named_object_cell(object_kind k, name const & n):object_cell(k), m_name(n) {}
    virtual ~named_object_cell() {}

    virtual bool has_name() const          { return true; }
    virtual name const & get_name() const  { return m_name; }
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

    virtual bool has_cnstr_level() const   { return true; }
    virtual level get_cnstr_level() const  { return m_level; }

    bool has_type() const          { return false; }
    expr const & get_type() const  { lean_unreachable(); return expr::null(); }
    bool is_definition() const     { return false; }
    bool is_opaque() const         { lean_unreachable(); return false; }
    expr const & get_value() const { lean_unreachable(); return expr::null(); }

    virtual char const * keyword() const { return "Universe"; }
};

/**
   \brief Named (and typed) kernel objects.
*/
class named_typed_object_cell : public named_object_cell {
    expr m_type;
public:
    named_typed_object_cell(object_kind k, name const & n, expr const & t):
        named_object_cell(k, n), m_type(t) {}
    virtual ~named_typed_object_cell() {}

    virtual bool has_type() const          { return true; }
    virtual expr const & get_type() const  { return m_type; }

    virtual bool has_cnstr_level() const   { return false; }
    virtual level get_cnstr_level() const  { lean_unreachable(); return level(); }
};

/**
   \brief Base class for Axioms and Variable declarations.
*/
class postulate_object_cell : public named_typed_object_cell {
public:
    postulate_object_cell(name const & n, expr const & t):
        named_typed_object_cell(object_kind::Postulate, n, t) {}

    bool is_definition() const     { return false; }
    bool is_opaque() const         { lean_unreachable(); return false; }
    expr const & get_value() const { lean_unreachable(); return expr::null(); }
};

/**
   \brief Axioms
*/
class axiom_object_cell : public postulate_object_cell {
public:
    axiom_object_cell(name const & n, expr const & t):postulate_object_cell(n, t) {}
    virtual char const * keyword() const { return "Axiom"; }
};

/**
   \brief Variable (aka constant) declaration
*/
class variable_decl_object_cell : public postulate_object_cell {
public:
    variable_decl_object_cell(name const & n, expr const & t):postulate_object_cell(n, t) {}
    virtual char const * keyword() const { return "Variable"; }
};

/**
   \brief Base class for definitions: theorems and definitions.
*/
class definition_object_cell : public named_typed_object_cell {
    expr m_value;
    bool m_opaque;
public:
    definition_object_cell(name const & n, expr const & t, expr const & v, bool opaque):
        named_typed_object_cell(object_kind::Definition, n, t), m_value(v), m_opaque(opaque) {}
    virtual ~definition_object_cell() {}

    bool is_definition() const     { return true; }
    bool is_opaque() const         { return m_opaque; }
    expr const & get_value() const { return m_value; }
    virtual char const * keyword() const { return "Definition"; }
};

/**
   \brief Theorems
*/
class theorem_object_cell : public definition_object_cell {
public:
    theorem_object_cell(name const & n, expr const & t, expr const & v):
        definition_object_cell(n, t, v, true) {}
    virtual char const * keyword() const { return "Theorem"; }
};

object mk_uvar_decl(name const & n, level const & l) { return object(new uvar_declaration_object_cell(n, l)); }
object mk_definition(name const & n, expr const & t, expr const & v, bool opaque) { return object(new definition_object_cell(n, t, v, opaque)); }
object mk_theorem(name const & n, expr const & t, expr const & v) { return object(new theorem_object_cell(n, t, v)); }
object mk_axiom(name const & n, expr const & t) { return object(new axiom_object_cell(n, t)); }
object mk_var_decl(name const & n, expr const & t) { return object(new variable_decl_object_cell(n, t)); }

static object g_null_object;

object const & object::null() {
    lean_assert(!g_null_object);
    return g_null_object;
}
}

