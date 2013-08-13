/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"

/*
  Kernel objects.

  We use abstract classes and virtual methods because a kernel
  frontend may need to create new objects for bookkeeping.
*/
namespace lean {
class environment;

/**
   \brief Abstract class used to represent kernel objects (i.e.,
   definitions, theorems, axioms, recursive definitions, etc)
*/
class object {
protected:
public:
    object() {}
    object(object const & o) = delete;
    object & operator=(object const & o) = delete;
    virtual ~object();

    /**
        \brief Return the keyword used to define this object in a Lean
        file. The keyword is also used to identify the class of an object.
    */
    virtual char const * keyword() const = 0;

    /** \brief Pretty print this object. */
    virtual format pp(environment const &) const = 0;

    /** \brief Display the object in the standard output. */
    virtual void display(std::ostream & out, environment const &) const;

    /** \brief Return true iff object has a name. */
    virtual bool has_name() const = 0;

    /** \brief Return object name. \pre has_name() */
    virtual name const & get_name() const = 0;

    /** \brief Return true iff object has a type. */
    virtual bool has_type() const = 0;

    /** \brief Return object type. \pre has_type() */
    virtual expr const & get_type() const = 0;

    /** \brief Return true iff object is a definition */
    virtual bool is_definition() const = 0;

    /** \brief Return true iff the definition is opaque. \pre is_definition() */
    virtual bool is_opaque() const = 0;

    /** \brief Return object value. \pre is_definition() */
    virtual expr const & get_value() const = 0;
};

/**
   \brief Anonymous objects are mainly used for bookkeeping.
*/
class anonymous_object : public object {
public:
    virtual ~anonymous_object();

    virtual bool has_name() const;
    virtual name const & get_name() const;

    virtual bool has_type() const;
    virtual expr const & get_type() const;

    virtual bool is_definition() const;
    virtual bool is_opaque() const;
    virtual expr const & get_value() const;
};

/**
   \brief Named (and typed) kernel objects.
*/
class named_object : public object {
    name m_name;
    expr m_type;
public:
    named_object(name const & n, expr const & t);
    virtual ~named_object();

    virtual bool has_name() const;
    virtual name const & get_name() const;

    virtual bool has_type() const;
    virtual expr const & get_type() const;
};

/**
   \brief Non-recursive definitions.
*/
class definition : public named_object {
    expr m_value;
    bool m_opaque; // Opaque definitions are ignored by definitional equality.
public:
    definition(name const & n, expr const & t, expr const & v, bool opaque);
    virtual ~definition();

    static char const * g_keyword;
    virtual char const * keyword() const;

    virtual bool is_definition() const;
    virtual bool is_opaque() const;
    virtual expr const & get_value() const;

    virtual format pp(environment const & env) const;
};

/**
   \brief A theorem is essentially an opaque definition.
*/
class theorem : public definition {
public:
    theorem(name const & n, expr const & t, expr const & v);
    virtual ~theorem();

    static char const * g_keyword;
    virtual char const * keyword() const;
};

/**
   \brief Base class for named objects that are not definitions.
*/
class fact : public named_object {
public:
    fact(name const & n, expr const & t);
    virtual ~fact();

    virtual bool is_definition() const;
    virtual bool is_opaque() const;
    virtual expr const & get_value() const;

    virtual format pp(environment const & env) const;
};

/**
   \brief Axioms
*/
class axiom : public fact {
public:
    axiom(name const & n, expr const & t);
    virtual ~axiom();

    static char const * g_keyword;
    virtual char const * keyword() const;
};

/**
   \brief Variable postulate. It is like an axiom since we are
   essentially postulating that a type is inhabited.
*/
class variable : public fact {
public:
    variable(name const & n, expr const & t);
    virtual ~variable();

    static char const * g_keyword;
    virtual char const * keyword() const;
};
}
