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
#include "expr_formatter.h"
#include "expr_locator.h"

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
    unsigned get_num_objects() const;
    object const & get_object(unsigned i) const;
public:
    environment();
    ~environment();

    /** \brief Set expression formatter. */
    void set_formatter(std::shared_ptr<expr_formatter> const & formatter);

    /** \brief Return expression formatter. */
    expr_formatter & get_formatter() const;

    /** \brief Set expression locator. */
    void set_locator(std::shared_ptr<expr_locator> const & locator);

    /** \brief Return expression locator. */
    expr_locator & get_locator() const;

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
    void add_anonymous_object(anonymous_object * o);

    /**
       \brief Return the object with the given name.
       It throws an exception if the environment does not have an object with the given name.
    */
    named_object const & get_object(name const & n) const;

    /**
       \brief Return the object with the given name.
       Return nullptr if there is no object with the given name.
    */
    named_object const * get_object_ptr(name const & n) const;

    /** \brief Return true iff the environment has an object with the given name */
    bool has_object(name const & n) const { return get_object_ptr(n) != nullptr; }

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

    /** \brief Display universal variable constraints and objects stored in this environment and its parents. */
    void display(std::ostream & out) const;
};
inline std::ostream & operator<<(std::ostream & out, environment const & env) { env.display(out); return out; }
}
