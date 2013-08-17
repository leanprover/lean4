/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"
#include "rc.h"
/*
  Kernel objects.

  We use abstract classes and virtual methods because a kernel
  frontend may need to create new objects for bookkeeping.
*/
namespace lean {
enum class object_kind { UVarDeclaration, Definition, Postulate, Neutral };

class object_cell {
    void dealloc() { delete this; }
    MK_LEAN_RC();
    object_kind m_kind;
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
    virtual bool has_name() const = 0;
    /** \brief Return object name. \pre has_name() */
    virtual name const & get_name() const = 0;

    /** \brief Has constraint level associated with it (for universal variables). */
    virtual bool has_cnstr_level() const = 0;
    /** \brief Return the constraint level associated with the object. */
    virtual level get_cnstr_level() const = 0;

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
   \brief Neutral objects are mainly used for bookkeeping in
   frontends built on top of the kernel.
   The kernel does *not* create neutral objects.
*/
class neutral_object_cell : public object_cell {
public:
    neutral_object_cell();
    virtual ~neutral_object_cell();

    virtual bool has_name() const;
    virtual name const & get_name() const;

    virtual bool has_cnstr_level() const;
    virtual level get_cnstr_level() const;

    virtual bool has_type() const;
    virtual expr const & get_type() const;

    virtual bool is_definition() const;
    virtual bool is_opaque() const;
    virtual expr const & get_value() const;
};

/**
   \brief Environment objects: definitions, theorems, axioms, universe
   variable declarations, etc.
*/
class object {
    object_cell * m_ptr;
    explicit object(object_cell * ptr):m_ptr(ptr) {}
public:
    object():m_ptr(nullptr) {}
    object(object const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    object(object && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~object() { if (m_ptr) m_ptr->dec_ref(); }

    static object const & null();

    friend void swap(object & a, object & b) { std::swap(a.m_ptr, b.m_ptr); }

    void release() { if (m_ptr) m_ptr->dec_ref(); m_ptr = nullptr; }

    object & operator=(object const & s) { LEAN_COPY_REF(object, s); }
    object & operator=(object && s) { LEAN_MOVE_REF(object, s); }

    operator bool() const { return m_ptr != nullptr; }

    object_kind kind() const { return m_ptr->kind(); }

    friend object mk_uvar_decl(name const & n, level const & l);
    friend object mk_definition(name const & n, expr const & t, expr const & v, bool opaque);
    friend object mk_theorem(name const & n, expr const & t, expr const & v);
    friend object mk_axiom(name const & n, expr const & t);
    friend object mk_var_decl(name const & n, expr const & t);
    friend object mk_neutral(neutral_object_cell * c);

    char const * keyword() const { return m_ptr->keyword(); }
    bool has_name() const { return m_ptr->has_name(); }
    name const & get_name() const { return m_ptr->get_name(); }
    bool has_type() const { return m_ptr->has_type(); }
    bool has_cnstr_level() const { return m_ptr->has_cnstr_level(); }
    level get_cnstr_level() const { return m_ptr->get_cnstr_level(); }
    expr const & get_type() const { return m_ptr->get_type(); }
    bool is_definition() const { return m_ptr->is_definition(); }
    bool is_opaque() const { return m_ptr->is_opaque(); }
    expr const & get_value() const { return m_ptr->get_value(); }

    object_cell const * cell() const { return m_ptr; }
};
object mk_uvar_decl(name const & n, level const & l);
object mk_definition(name const & n, expr const & t, expr const & v, bool opaque);
object mk_theorem(name const & n, expr const & t, expr const & v);
object mk_axiom(name const & n, expr const & t);
object mk_var_decl(name const & n, expr const & t);
inline object mk_neutral(neutral_object_cell * c) { lean_assert(c->get_rc() == 1); return object(c); }
}
