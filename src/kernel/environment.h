/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <memory>
#include "kernel/context.h"
#include "kernel/object.h"
#include "kernel/level.h"

namespace lean {
/**
   \brief Lean environment for defining constants, inductive
   datatypes, universe variables, et.c
*/
class environment {
private:
    struct imp;
    std::shared_ptr<imp> m_ptr;
    void check_type(name const & n, expr const & t, expr const & v);
    environment(std::shared_ptr<imp> const & parent, bool);
    explicit environment(std::shared_ptr<imp> const & ptr);
    friend class read_only_environment;
    friend class read_write_environment;
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
        \brief Add builtin value to the environment.

        \pre is_value(v)
    */
    void add_builtin(expr const & v);

    /**
       \brief Add a builtin value set to the environment.

       The set is registered by providing a representative of the set.
       Each builtin set of values is implemented by a C++ class.
       The environment will only accept object of the same class of
       the representative. This functionality is used to support
       infinite set of builtin values such as the natural numbers.

       \pre is_value(r);
    */
    void add_builtin_set(expr const & r);

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

    /**
       \brief Return the type of \c e in the given context and this environment.
    */
    expr infer_type(expr const & e, context const & ctx = context()) const;

    /**
       \brief Normalize \c e in the given context and this environment.
    */
    expr normalize(expr const & e, context const & ctx = context()) const;

    /**
       \brief Low-level function for accessing objects. Consider using iterators.
    */
    unsigned get_num_objects(bool local) const;
    /**
       \brief Low-level function for accessing objects. Consider using iterators.
    */
    object const & get_object(unsigned i, bool local) const;

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

    /**
       \brief Frontend can store data in environment extensions.
       Each extension is associated with a unique token/id.
       This token allows the frontend to retrieve/store an extension object
       in the environment
    */
    class extension {
        friend struct imp;
        imp *     m_env;
        unsigned  m_extid; // extension id
        extension const * get_parent_core() const;
    public:
        extension();
        virtual ~extension();
        /**
           \brief Return a constant reference for a parent extension,
           and a nullptr if there is no parent/ancestor, or if the
           parent/ancestor has an extension.
        */
        template<typename Ext> Ext const * get_parent() const {
            extension const * ext = get_parent_core();
            lean_assert(!ext || dynamic_cast<Ext const *>(ext) != nullptr);
            return static_cast<Ext const *>(ext);
        }
    };

    /**
       \brief Register an environment extension. Every environment
       object will contain this extension. The funciton mk creates a
       new instance of the extension.  The extension object can be
       retrieved using the token (unsigned integer) returned by this
       method.

       \remark The extension objects are created on demand.

       \see get_extension
    */
    typedef std::unique_ptr<extension> (*mk_extension)();
    static unsigned register_extension(mk_extension mk);

private:
    extension const & get_extension_core(unsigned extid) const;
    extension & get_extension_core(unsigned extid);

public:
    /**
       \brief Retrieve the extension associated with the token \c extid.
       The token is the value returned by \c register_extension.
    */
    template<typename Ext>
    Ext const & get_extension(unsigned extid) const {
        extension const & ext = get_extension_core(extid);
        lean_assert(dynamic_cast<Ext const *>(&ext) != nullptr);
        return static_cast<Ext const &>(ext);
    }

    template<typename Ext>
    Ext & get_extension(unsigned extid) {
        extension & ext = get_extension_core(extid);
        lean_assert(dynamic_cast<Ext*>(&ext) != nullptr);
        return static_cast<Ext&>(ext);
    }

public:
    typedef std::weak_ptr<imp> weak_ref;
    weak_ref to_weak_ref() const { return weak_ref(m_ptr); }
    environment(weak_ref const & r):m_ptr(r) { lean_assert(!r.expired()); }
};
}
