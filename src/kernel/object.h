/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <string>
#include "util/rc.h"
#include "kernel/expr.h"
/*
  Kernel objects.

  We use abstract classes and virtual methods because a kernel
  frontend may need to create new objects for bookkeeping.
*/
namespace lean {
class io_state;
class object;
enum class object_kind { Definition, Postulate, Neutral };

class object_cell {
protected:
    friend class object;
    void dealloc() { delete this; }
    MK_LEAN_RC();
    object_kind m_kind;
    /** \brief Set the opaque flag */
    virtual void set_opaque(bool ) { lean_unreachable(); } // LCOV_EXCL_LINE
public:
    object_cell(object_kind k):m_rc(1), m_kind(k) {}
    virtual ~object_cell() {}

    object_kind kind() const { return m_kind; }

    /**
        \brief Return the keyword used to define this object in a Lean
        file. The keyword is also used to identify the class of an object.
    */
    virtual char const * keyword() const = 0;

    /** \brief Return true iff object has a name. */
    virtual bool has_name() const { return false; }
    /** \brief Return object name. \pre has_name() */
    virtual name get_name() const { lean_unreachable(); } // LCOV_EXCL_LINE

    /** \brief Return true iff object has a type. */
    virtual bool has_type() const { return false; }
    /** \brief Return object type. \pre has_type() */
    virtual expr get_type() const { lean_unreachable(); } // LCOV_EXCL_LINE

    /** \brief Return true iff object is a definition */
    virtual bool is_definition() const { return false; }
    /** \brief Return true iff the definition is opaque. \pre is_definition() */
    virtual bool is_opaque() const { lean_unreachable(); } // LCOV_EXCL_LINE
    /** \brief Return object value. \pre is_definition() */
    virtual expr get_value() const { lean_unreachable(); } // LCOV_EXCL_LINE

    virtual bool is_axiom() const { return false; }
    virtual bool is_theorem() const { return false; }
    virtual bool is_var_decl() const { return false; }

    virtual unsigned get_weight() const { return 0; }

    virtual void write(serializer & ) const = 0;
    typedef void (*reader)(environment const & env, io_state const & ios, deserializer & d);
    static void register_deserializer(std::string const & k, reader rd);
    struct register_deserializer_fn {
        register_deserializer_fn(std::string const & k, reader rd) { register_deserializer(k, rd); }
    };
};

/**
   \brief Neutral objects are mainly used for bookkeeping in
   frontends built on top of the kernel.
   The kernel does *not* create neutral objects.
*/
class neutral_object_cell : public object_cell {
public:
    neutral_object_cell();
};

/**
   \brief Environment objects: definitions, theorems, axioms, universe
   variable declarations, etc.
*/
class object {
    object_cell * m_ptr;
    explicit object(object_cell * ptr):m_ptr(ptr) {}
    friend class environment_cell;
    void set_opaque(bool f) { m_ptr->set_opaque(f); }
public:
    object(object const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    object(object && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~object() { if (m_ptr) m_ptr->dec_ref(); }

    friend void swap(object & a, object & b) { std::swap(a.m_ptr, b.m_ptr); }

    object & operator=(object const & s) { LEAN_COPY_REF(s); }
    object & operator=(object && s) { LEAN_MOVE_REF(s); }

    object_kind kind() const { return m_ptr->kind(); }

    friend object mk_definition(name const & n, expr const & t, expr const & v, unsigned weight);
    friend object mk_theorem(name const & n, expr const & t, expr const & v);
    friend object mk_axiom(name const & n, expr const & t);
    friend object mk_var_decl(name const & n, expr const & t);
    friend object mk_neutral(neutral_object_cell * c);

    char const * keyword() const { return m_ptr->keyword(); }
    bool has_name() const { return m_ptr->has_name(); }
    name get_name() const { return m_ptr->get_name(); }
    bool has_type() const { return m_ptr->has_type(); }
    expr get_type() const { return m_ptr->get_type(); }
    bool is_definition() const { return m_ptr->is_definition(); }
    bool is_opaque() const { return m_ptr->is_opaque(); }
    expr get_value() const { return m_ptr->get_value(); }
    unsigned get_weight() const { return m_ptr->get_weight(); }

    bool is_axiom() const { return m_ptr->is_axiom(); }
    bool is_theorem() const { return m_ptr->is_theorem(); }
    bool is_var_decl() const { return m_ptr->is_var_decl(); }

    void write(serializer & s) const { m_ptr->write(s); }
    object_cell const * cell() const { return m_ptr; }
};

inline optional<object> none_object() { return optional<object>(); }
inline optional<object> some_object(object const & o) { return optional<object>(o); }
inline optional<object> some_object(object && o) { return optional<object>(std::forward<object>(o)); }

object mk_definition(name const & n, expr const & t, expr const & v, unsigned weight);
object mk_theorem(name const & n, expr const & t, expr const & v);
object mk_axiom(name const & n, expr const & t);
object mk_var_decl(name const & n, expr const & t);
inline object mk_neutral(neutral_object_cell * c) { lean_assert(c->get_rc() == 1); return object(c); }

void read_object(environment const & env, io_state const & ios, std::string const & k, deserializer & d);

/**
   \brief Helper function whether we should unfold an definition or not.

   1- We unfold non-opaque definitions.
   2- We never unfold theorems.
*/
inline bool should_unfold(object const & obj) { return obj.is_definition() && !obj.is_theorem() && !obj.is_opaque(); }
inline bool should_unfold(optional<object> const & obj) { return obj && should_unfold(*obj); }
}
