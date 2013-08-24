/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <memory>
#include "object.h"
#include "level.h"

namespace lean {
/**
   \brief Lean environment for defining constants, inductive
   datatypes, universe variables, et.c
*/
class environment {
private:
    struct imp;
    std::shared_ptr<imp> m_imp;
    void check_type(name const & n, expr const & t, expr const & v);
    explicit environment(std::shared_ptr<imp> const & ptr);
    explicit environment(imp * new_ptr);
    unsigned get_num_objects(bool local) const;
    object const & get_object(unsigned i, bool local) const;
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

    /**
       \brief Return universal variable with the given name.
       Throw an exception if variable is not defined in this environment.
    */
    level get_uvar(name const & n) const;
    // =======================================

    // =======================================
    // Environment Objects
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
       \brief Register the given unanymous object in this environment.
       The environment assume the object ownership.
    */
    void add_neutral_object(neutral_object_cell * o);

    /**
       \brief Return the object with the given name.
       It throws an exception if the environment does not have an object with the given name.
    */
    object const & get_object(name const & n) const;

    /**
       \brief Find a given object in the environment. Return the null
       object if there is no object with the given name.

       \remark Object implements operator bool(), and the null object returns false.
    */
    object const & find_object(name const & n) const;

    /** \brief Return true iff the environment has an object with the given name */
    bool has_object(name const & n) const { return find_object(n); }

    /** \brief Iterator for Lean environment objects. */
    class object_iterator {
        environment const & m_env;
        unsigned            m_idx;
        bool                m_local;
        friend class environment;
        object_iterator(environment const & env, unsigned idx, bool local):m_env(env), m_idx(idx), m_local(local) {}
    public:
        object_iterator(object_iterator const & s):m_env(s.m_env), m_idx(s.m_idx), m_local(s.m_local) {}
        object_iterator & operator++() { ++m_idx; return *this; }
        object_iterator operator++(int) { object_iterator tmp(*this); operator++(); return tmp; }
        object_iterator & operator--() { --m_idx; return *this; }
        object_iterator operator--(int) { object_iterator tmp(*this); operator--(); return tmp; }
        bool operator==(object_iterator const & s) const { lean_assert(&m_env == &(s.m_env)); return m_idx == s.m_idx; }
        bool operator!=(object_iterator const & s) const { return !operator==(s); }
        object const & operator*() { return m_env.get_object(m_idx, m_local); }
        object const * operator->() { return &(m_env.get_object(m_idx, m_local)); }
    };

    /**
        \brief Return an iterator to the beginning of the sequence of
        objects stored in this environment.

        \remark The objects in this environment and ancestor
        environments are considered
    */
    object_iterator begin_objects() const { return object_iterator(*this, 0, false); }

    /**
        \brief Return an iterator to the end of the sequence of
        objects stored in this environment.

        \remark The objects in this environment and ancestor
        environments are considered
    */
    object_iterator end_objects() const { return object_iterator(*this, get_num_objects(false), false); }

    /**
        \brief Return an iterator to the beginning of the sequence of
        objects stored in this environment (objects in ancestor
        environments are ingored).
    */
    object_iterator begin_local_objects() const { return object_iterator(*this, 0, true); }

    /**
        \brief Return an iterator to the end of the sequence of
        objects stored in this environment (objects in ancestor
        environments are ingored).
    */
    object_iterator end_local_objects() const { return object_iterator(*this, get_num_objects(true), true); }
    // =======================================

    /** \brief Display universal variable constraints and objects stored in this environment and its parents. */
    void display(std::ostream & out) const;

    void set_interrupt(bool flag);
    void interrupt() { set_interrupt(true); }
    void reset_interrupt() { set_interrupt(false); }
};
}
