/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <memory>
#include "expr.h"
#include "level.h"

namespace lean {
/**
   \brief Lean environment for defining constants, inductive
   datatypes, universe variables, et.c
*/
class environment {
public:
    class object;
private:
    struct imp;
    std::shared_ptr<imp> m_imp;
    void check_type(name const & n, expr const & t, expr const & v);
    explicit environment(std::shared_ptr<imp> const & ptr);
    explicit environment(imp * new_ptr);
    unsigned get_num_objects() const;
    object const & get_object(unsigned i) const;
public:
    environment();
    ~environment();

    // =======================================
    // Parent/Child environment management
    /**
       \brief Create a child environment. This environment will only allow "read-only" operations until
       all children environments are deleted.
    */
    environment mk_child() const;

    /** \brief Return true iff this environment has children environments. */
    bool has_children() const;

    /** \brief Return true iff this environment has a parent environment. */
    bool has_parent() const;

    /**
        \brief Return parent environment of this environment.
        \pre has_parent()
    */
    environment parent() const;
    // =======================================

    // =======================================
    // Universe variables
    /**
       \brief Add a new universe variable with name \c n and constraint <tt>n >= l</tt>.
       Return the new variable.

       \remark An exception is thrown if a universe inconsistency is detected.
    */
    level add_uvar(name const & n, level const & l);
    level add_uvar(name const & n) { return add_uvar(n, level()); }

    /**
       \brief Return true iff the constraint l1 >= l2 is implied by the constraints
       in the environment.
    */
    bool is_ge(level const & l1, level const & l2) const;

    /** \brief Display universal variables, and their constraints */
    void display_uvars(std::ostream & out) const;

    /**
       \brief Return universal variable with the given name.
       Throw an exception if variable is not defined in this environment.
    */
    level get_uvar(name const & n) const;
    // =======================================

    // =======================================
    // Environment Objects
    enum class object_kind { Definition, Theorem, Var, Axiom };
    /**
        \brief Base class for environment objects
        It is just a place holder at this point.
    */
    class object {
    protected:
    public:
        object() {}
        object(object const & o) = delete;
        object & operator=(object const & o) = delete;

        virtual ~object() {}
        virtual object_kind kind() const = 0;
        virtual void display(std::ostream & out) const = 0;
        virtual format pp(environment const &) const = 0;
        virtual expr const & get_type() const = 0;
        virtual char const * header() const = 0;
    };

    class definition : public object {
        name m_name;
        expr m_type;
        expr m_value;
        bool m_opaque;
    public:
        definition(name const & n, expr const & t, expr const & v, bool opaque);
        virtual ~definition();
        virtual object_kind kind() const { return object_kind::Definition; }
        name const & get_name()  const { return m_name; }
        virtual expr const & get_type()  const { return m_type; }
        expr const & get_value() const { return m_value; }
        bool         is_opaque() const { return m_opaque; }
        virtual void display(std::ostream & out) const;
        virtual format pp(environment const & env) const;
        virtual char const * header() const { return "Definition"; }
    };

    class theorem : public definition {
    public:
        theorem(name const & n, expr const & t, expr const & v):definition(n, t, v, true) {}
        virtual object_kind kind() const { return object_kind::Theorem; }
        virtual char const * header() const { return "Theorem"; }
    };

    class fact : public object {
    protected:
        name m_name;
        expr m_type;
    public:
        fact(name const & n, expr const & t);
        virtual ~fact();
        name const & get_name()  const { return m_name; }
        virtual expr const & get_type()  const { return m_type; }
        virtual void display(std::ostream & out) const;
        virtual format pp(environment const &) const;
    };

    class axiom : public fact {
    public:
        axiom(name const & n, expr const & t):fact(n, t) {}
        virtual object_kind kind() const { return object_kind::Axiom; }
        virtual char const * header() const { return "Axiom"; }
    };

    class variable : public fact {
    public:
        variable(name const & n, expr const & t):fact(n, t) {}
        virtual object_kind kind() const { return object_kind::Var; }
        virtual char const * header() const { return "Variable"; }
    };

    friend bool is_definition(object const & o) { return o.kind() == object_kind::Definition; }
    friend bool is_axiom(object const & o) { return o.kind() == object_kind::Axiom; }
    friend bool is_var(object const & o) { return o.kind() == object_kind::Var; }
    friend bool is_fact(object const & o) { return is_axiom(o) || is_var(o); }

    friend definition const & to_definition(object const & o) { lean_assert(is_definition(o)); return static_cast<definition const &>(o); }
    friend fact const & to_fact(object const & o) { lean_assert(is_fact(o)); return static_cast<fact const &>(o); }

    /**
       \brief Add a new definition n : t := v.
       It throws an exception if v does not have type t.
       It throws an exception if there is already an object with the given name.
       If opaque == true, then definition is not used by normalizer.
    */
    void add_definition(name const & n, expr const & t, expr const & v, bool opaque = false);
    void add_theorem(name const & n, expr const & t, expr const & v);

    /**
       \brief Add a new definition n : infer_type(v) := v.
       It throws an exception if there is already an object with the given name.
       If opaque == true, then definition is not used by normalizer.
    */
    void add_definition(name const & n, expr const & v, bool opaque = false);

    /**
       \brief Add a new fact (Axiom or Fact) to the environment.
       It throws an exception if there is already an object with the given name.
    */
    void add_axiom(name const & n, expr const & t);
    void add_var(name const & n, expr const & t);

    /**
       \brief Return the object with the given name.
       It throws an exception if the environment does not have an object with the given name.
    */
    object const & get_object(name const & n) const;

    /**
       \brief Return the object with the given name.
       Return nullptr if there is no object with the given name.
    */
    object const * get_object_ptr(name const & n) const;

    /** \brief Iterator for Lean environment objects. */
    class object_iterator {
        environment const & m_env;
        unsigned            m_idx;
        friend class environment;
        object_iterator(environment const & env, unsigned idx):m_env(env), m_idx(idx) {}
    public:
        object_iterator(object_iterator const & s):m_env(s.m_env), m_idx(s.m_idx) {}
        object_iterator & operator++() { ++m_idx; return *this; }
        object_iterator operator++(int) { object_iterator tmp(*this); operator++(); return tmp; }
        bool operator==(object_iterator const & s) const { lean_assert(&m_env == &(s.m_env)); return m_idx == s.m_idx; }
        bool operator!=(object_iterator const & s) const { return !operator==(s); }
        object const & operator*() { return m_env.get_object(m_idx); }
    };

    /** \brief Return an iterator to the beginning of the sequence of objects stored in this environment */
    object_iterator begin_objects() const { return object_iterator(*this, 0); }

    /** \brief Return an iterator to the end of the sequence of objects stored in this environment */
    object_iterator end_objects() const { return object_iterator(*this, get_num_objects()); }
    // =======================================

    // =======================================
    // Pretty printing
    /** \brief Display all objects stored in the environment */
    void display_objects(std::ostream & out) const;

    /** \brief Display universal variable constraints and objects stored in this environment and its parents. */
    void display(std::ostream & out) const;
    // =======================================
};
inline std::ostream & operator<<(std::ostream & out, environment const & env) { env.display(out); return out; }
}
