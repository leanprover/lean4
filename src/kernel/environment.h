/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <memory>
#include <vector>
#include <set>
#include <string>
#include <utility>
#include "util/lua.h"
#include "util/shared_mutex.h"
#include "util/name_map.h"
#include "kernel/object.h"
#include "kernel/level.h"

namespace lean {
class environment;
class ro_environment;
class type_checker;
class environment_extension;

/** \brief Implementation of the Lean environment. */
class environment_cell {
    friend class environment;
    friend class read_write_shared_environment;
    friend class read_only_shared_environment;
    // Remark: only named objects are stored in the dictionary.
    typedef name_map<object> object_dictionary;
    typedef std::tuple<level, level, int> constraint;
    std::weak_ptr<environment_cell>         m_this;
    // Children environment management
    atomic<unsigned>                        m_num_children;
    std::shared_ptr<environment_cell>       m_parent;
    // Object management
    std::vector<object>                     m_objects;
    object_dictionary                       m_object_dictionary;

    // std::unique_ptr<type_checker>           m_type_checker;
    std::set<name>                          m_imported_modules;   // set of imported files and builtin modules
    bool                                    m_trust_imported; // if true, then imported modules are not type checked.
    bool                                    m_type_check;     // auxiliary flag used to implement m_trust_imported.
    std::vector<std::unique_ptr<environment_extension>> m_extensions;
    friend class environment_extension;

    // This mutex is only used to implement threadsafe environment objects
    // in the external APIs
    shared_mutex                            m_mutex;

    environment env() const;

    void inc_children() { m_num_children++; }
    void dec_children() { m_num_children--; }

    environment_extension & get_extension_core(unsigned extid);
    environment_extension const & get_extension_core(unsigned extid) const;

    unsigned get_max_weight(expr const & e);
    void check_name_core(name const & n);
    void check_name(name const & n);

    void register_named_object(object const & new_obj);
    optional<object> get_object_core(name const & n) const;

    void check_no_mlocal(expr const & e);
    void check_type(name const & n, expr const & t, expr const & v);
    void check_type(expr const & t);
    void check_new_definition(name const & n, expr const & t, expr const & v);

    bool mark_imported_core(name n);
    bool load_core(std::string const & fname, io_state const & ios, optional<std::string> const & mod_name);
    bool already_imported(name const & n) const;
    /** \brief Return true iff the given file was not already marked as imported. It will also mark the file as imported. */
    bool mark_imported(char const * fname);

public:
    environment_cell();
    environment_cell(std::shared_ptr<environment_cell> const & parent);
    ~environment_cell();

    /** \brief Return true iff this environment has children environments. */
    bool has_children() const { return m_num_children > 0; }
    /** \brief Return true iff this environment has a parent environment */
    bool has_parent() const { return m_parent != nullptr; }

    /**
       \brief Return parent environment of this environment.
       \pre has_parent()
    */
    environment parent() const;

    /**
       \brief Create a child environment. This environment will only allow "read-only" operations until
       all children environments are deleted.
    */
    environment mk_child() const;

    // =======================================
    // Environment Objects

    /**
       \brief Add a new definition n : t := v.
       It throws an exception if v does not have type t.
       It throws an exception if there is already an object with the given name.
    */
    void add_definition(name const & n, expr const & t, expr const & v, bool opaque = false);
    void add_opaque_definition(name const & n, expr const & t, expr const & v) { add_definition(n, t, v, true); }
    void add_theorem(name const & n, expr const & t, expr const & v);

    /**
       \brief Add a new definition n : infer_type(v) := v.
       It throws an exception if there is already an object with the given name.
    */
    void add_definition(name const & n, expr const & v, bool opaque = false);

    /**
       \brief Set the given definition as opaque (or not)

       \remark It throws an error if \c n is not a definition.
    */
    void set_opaque(name const & n, bool opaque);

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
    object get_object(name const & n) const;

    /**
       \brief Find a given object in the environment. Return the null
       object if there is no object with the given name.
    */
    optional<object> find_object(name const & n) const { return get_object_core(n); }

    /** \brief Return true iff the environment has an object with the given name */
    bool has_object(name const & n) const { return static_cast<bool>(find_object(n)); }

    /**
       \brief Type check the given expression, and return the type of \c e in the given context and this environment.
    */
    expr type_check(expr const & e) const;

    /**
       \brief Return the type of \c e in the given context and this environment.
    */
    expr infer_type(expr const & e) const;

    /**
       \brief Normalize \c e in the given context and this environment.
    */
    expr normalize(expr const & e) const;

    /**
       \brief Return true iff \c e is a proposition.
    */
    bool is_proposition(expr const & e) const;

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
        std::shared_ptr<environment_cell const> m_env;
        unsigned                                m_idx;
        bool                                    m_local;
        friend class environment_cell;
        object_iterator(std::shared_ptr<environment_cell const> && env, unsigned idx, bool local):m_env(env), m_idx(idx), m_local(local) {}
    public:
        object_iterator(object_iterator const & s):m_env(s.m_env), m_idx(s.m_idx), m_local(s.m_local) {}
        object_iterator & operator++() { ++m_idx; return *this; }
        object_iterator operator++(int) { object_iterator tmp(*this); operator++(); return tmp; }
        object_iterator & operator--() { --m_idx; return *this; }
        object_iterator operator--(int) { object_iterator tmp(*this); operator--(); return tmp; }
        bool operator==(object_iterator const & s) const { lean_assert(m_env.get() == s.m_env.get()); return m_idx == s.m_idx; }
        bool operator!=(object_iterator const & s) const { return !operator==(s); }
        object const & operator*() { return m_env->get_object(m_idx, m_local); }
        object const * operator->() { return &(m_env->get_object(m_idx, m_local)); }
    };

    /**
        \brief Return an iterator to the beginning of the sequence of
        objects stored in this environment.

        \remark The objects in this environment and ancestor
        environments are considered
    */
    object_iterator begin_objects() const { return object_iterator(m_this.lock(), 0, false); }

    /**
        \brief Return an iterator to the end of the sequence of
        objects stored in this environment.

        \remark The objects in this environment and ancestor
        environments are considered
    */
    object_iterator end_objects() const { return object_iterator(m_this.lock(), get_num_objects(false), false); }

    /**
        \brief Return an iterator to the beginning of the sequence of
        objects stored in this environment (objects in ancestor
        environments are ingored).
    */
    object_iterator begin_local_objects() const { return object_iterator(m_this.lock(), 0, true); }

    /**
        \brief Return an iterator to the end of the sequence of
        objects stored in this environment (objects in ancestor
        environments are ingored).
    */
    object_iterator end_local_objects() const { return object_iterator(m_this.lock(), get_num_objects(true), true); }
    // =======================================

    /**
       \brief Register an environment extension. Every environment
       object will contain this extension. The funciton mk creates a
       new instance of the extension.  The extension object can be
       retrieved using the token (unsigned integer) returned by this
       method.

       \remark The extension objects are created on demand.

       \see get_extension
    */
    typedef std::unique_ptr<environment_extension> (*mk_extension)();
    static unsigned register_extension(mk_extension mk);

    /**
       \brief Retrieve the extension associated with the token \c extid.
       The token is the value returned by \c register_extension.
    */
    template<typename Ext>
    Ext const & get_extension(unsigned extid) const {
        environment_extension const & ext = get_extension_core(extid);
        lean_assert(dynamic_cast<Ext const *>(&ext) != nullptr);
        return static_cast<Ext const &>(ext);
    }

    template<typename Ext>
    Ext & get_extension(unsigned extid) {
        environment_extension & ext = get_extension_core(extid);
        lean_assert(dynamic_cast<Ext*>(&ext) != nullptr);
        return static_cast<Ext&>(ext);
    }

    void export_objects(std::string const & fname);
    bool import(std::string const & fname, io_state const & ios);
    void load(std::string const & fname, io_state const & ios);
    /** \brief Return true iff module \c n has already been imported */
    bool imported(std::string const & n) const;

    /**
        \brief When trusted_imported flag is true, the environment will
        not type check imported modules.
    */
    void set_trusted_imported(bool flag);

    /**
       \brief Execute function \c fn. Any object created by \c fn
       is not exported by the environment.
    */
    void auxiliary_section(std::function<void()> fn);
};

/**
   \brief Frontend can store data in environment extensions.
   Each extension is associated with a unique token/id.
   This token allows the frontend to retrieve/store an extension object
   in the environment
*/
class environment_extension {
    friend class environment_cell;
    environment_cell * m_env;
    unsigned           m_extid; // extension id
    environment_extension const * get_parent_core() const;
public:
    environment_extension();
    virtual ~environment_extension();
    /**
       \brief Return a constant reference for a parent extension,
       and a nullptr if there is no parent/ancestor, or if the
       parent/ancestor has an extension.
    */
    template<typename Ext> Ext const * get_parent() const {
        environment_extension const * ext = get_parent_core();
        lean_assert(!ext || dynamic_cast<Ext const *>(ext) != nullptr);
        return static_cast<Ext const *>(ext);
    }
};

/**
   \brief Reference to environment
*/
class environment {
    friend class ro_environment;
    friend class environment_cell;
    friend class read_write_shared_environment;
    std::shared_ptr<environment_cell> m_ptr;
    environment(std::shared_ptr<environment_cell> const & parent, bool);
    environment(std::shared_ptr<environment_cell> const & ptr);
public:
    environment();
    environment_cell * operator->() const { return m_ptr.get(); }
    environment_cell & operator*() const { return *(m_ptr.get()); }
};

/**
   \brief Read-only reference to environment.
*/
class ro_environment {
    friend class environment_cell;
    friend class read_only_shared_environment;
    std::shared_ptr<environment_cell const> m_ptr;
    ro_environment(std::shared_ptr<environment_cell const> const & p):m_ptr(p) {}
    friend int push_environment(lua_State * L, ro_environment const & env);
    environment cast_to_environment() const { return environment(std::const_pointer_cast<environment_cell>(m_ptr)); }
public:
    typedef std::weak_ptr<environment_cell const> weak_ref;
    ro_environment(environment const & env);
    ro_environment(weak_ref const & env);
    explicit operator weak_ref() const { return weak_ref(m_ptr); }
    weak_ref to_weak_ref() const { return weak_ref(m_ptr); }
    environment_cell const * operator->() const { return m_ptr.get(); }
    environment_cell const & operator*() const { return *(m_ptr.get()); }
};

/** \brief Return true iff the given object marks the begin of the of a sequence of imported objects. */
bool is_begin_import(object const & obj);
/** \brief Return true iff the given object marks the begin of the of a sequence of builtin imported objects. */
bool is_begin_builtin_import(object const & obj);
/** \brief Return true iff the given object marks the end of the of a sequence of imported objects. */
bool is_end_import(object const & obj);
/**
    \brief Return the module imported by the given import object.
    Return none if \c obj is not an import object.
*/
optional<std::string> get_imported_module(object const & obj);

/**
   \brief Return true iff \c obj is a set_opaque command mark.
*/
bool is_set_opaque(object const & obj);
/**
   \brief Return the identifier of a set_opaque command.
   \pre is_set_opaque(obj)
*/
name const & get_set_opaque_id(object const & obj);
/**
   \brief Return the flag of a set_opaque command.
   \pre is_set_opaque(obj)
*/
bool get_set_opaque_flag(object const & obj);
}
