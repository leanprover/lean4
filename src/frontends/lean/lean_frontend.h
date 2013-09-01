/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "environment.h"
#include "state.h"
#include "lean_operator_info.h"

namespace lean {
/**
   \brief Object for managing the environment, parser, pretty printer,
   elaborator, etc.
*/
class frontend {
    struct imp;
    std::shared_ptr<imp> m_imp;
    explicit frontend(imp * new_ptr);
    explicit frontend(std::shared_ptr<imp> const & ptr);
    state & get_state_core();
public:
    frontend();
    ~frontend();

    /**
       @name Parent/Child frontend management.
    */
    /*@{*/
    /**
        \brief Create a child environment. This frontend object will
        only allow "read-only" operations until all children frontend
        objects are deleted.
    */
    frontend mk_child() const;

    /** \brief Return true iff this fronted has children frontend. */
    bool has_children() const;

    /** \brief Return true iff this frontend has a parent frontend. */
    bool has_parent() const;

    /** \brief Return parent frontend */
    frontend parent() const;
    /*@}*/

    /**
       @name Environment API
    */
    /*@{*/
    /** \brief Coercion frontend -> environment. */
    environment const & get_environment() const;
    operator environment const &() const { return get_environment(); }

    level add_uvar(name const & n, level const & l);
    level add_uvar(name const & n);
    level get_uvar(name const & n) const;
    void add_definition(name const & n, expr const & t, expr const & v, bool opaque = false);
    void add_theorem(name const & n, expr const & t, expr const & v);
    void add_definition(name const & n, expr const & v, bool opaque = false);
    void add_axiom(name const & n, expr const & t);
    void add_var(name const & n, expr const & t);
    object const & get_object(name const & n) const;
    object const & find_object(name const & n) const;
    bool has_object(name const & n) const;
    typedef environment::object_iterator object_iterator;
    object_iterator begin_objects() const;
    object_iterator end_objects() const;
    object_iterator begin_local_objects() const;
    object_iterator end_local_objects() const;
    /*@}*/

    /**
       @name Notation for parsing and pretty printing.
    */
    /*@{*/
    void add_infix(name const & opn, unsigned precedence, expr const & d);
    void add_infixl(name const & opn, unsigned precedence, expr const & d);
    void add_infixr(name const & opn, unsigned precedence, expr const & d);
    void add_prefix(name const & opn, unsigned precedence, expr const & d);
    void add_postfix(name const & opn, unsigned precedence, expr const & d);
    void add_mixfixl(unsigned sz, name const * opns, unsigned precedence, expr const & d);
    void add_mixfixr(unsigned sz, name const * opns, unsigned precedence, expr const & d);
    void add_mixfixc(unsigned sz, name const * opns, unsigned precedence, expr const & d);
    void add_mixfixo(unsigned sz, name const * opns, unsigned precedence, expr const & d);
    /**
        \brief Return the operator (if one exists) associated with the
        given expression.

        \remark If an operator is not associated with \c e, then
        return the null operator.

        \remark This is used for pretty printing.
    */
    operator_info find_op_for(expr const & e) const;
    /**
       \brief Return the operator (if one exists) that can appear at
       the beginning of a language construct.

        \remark If there isn't a nud operator starting with \c n, then
        return the null operator.

        \remark This is used for parsing.
    */
    operator_info find_nud(name const & n) const;
    /**
       \brief Return the operator (if one exists) that can appear
       inside of a language construct.

        \remark If there isn't a led operator starting with \c n, then
        return the null operator.

        \remark This is used for parsing.
    */
    operator_info find_led(name const & n) const;
    /*@}*/

    /**
       @name Implicit arguments.
    */
    /**
       \brief Mark the given arguments of \c n as implicit.
       The bit-vector array specify the position of the implicit arguments.
    */
    void mark_implicit_arguments(name const & n, unsigned sz, bool const * mask);
    void mark_implicit_arguments(name const & n, std::initializer_list<bool> const & l);
    void mark_implicit_arguments(expr const & n, std::initializer_list<bool> const & l) { mark_implicit_arguments(const_name(n), l); }
    /** \brief Return true iff \c n has implicit arguments */
    bool has_implicit_arguments(name const & n) const;
    /** \brief Return the position of the arguments that are implicit. */
    std::vector<bool> const & get_implicit_arguments(name const & n) const;
    /**
        \brief This frontend associates an definition with each
        definition (or postulate) that has implicit arguments. The
        additional definition has explicit arguments, and it is called
        n::explicit. The explicit version can be used when the Lean
        frontend can't figure out the value for the implicit
        arguments.
    */
    name const & get_explicit_version(name const & n) const;
    /*@}*/

    /**
       @name Coercions

       We support a very basic form of coercion. It is an expression
       with type T1 -> T2. This expression can be used to convert
       an expression of type T1 into an expression of type T2 whenever
       T2 is expected, but T1 was provided.
    */
    /**
       \brief Add a new coercion to the frontend.
       It throws an exception if f does not have type T1 -> T2, or if there is already a
       coercion from T1 to T2.
    */
    void add_coercion(expr const & f);
    /**
        \brief Return a coercion from given_type to expected_type if it exists.
        Return the null expression if there is no coercion from \c given_type to
        \c expected_type.

        \pre The expressions \c given_type and \c expected_type are normalized
    */
    expr get_coercion(expr const & given_type, expr const & expected_type);
    /**
       \brief Return true iff the given expression is a coercion. That is, it was added using
       \c add_coercion.
    */
    bool is_coercion(expr const & f);
    /*@}*/

    /**
       @name State management.
    */
    /*@{*/
    state const & get_state() const;
    operator state const &() const { return get_state(); }
    void set_options(options const & opts);
    template<typename T> void set_option(name const & n, T const & v) { get_state_core().set_option(n, v); }
    void set_regular_channel(std::shared_ptr<output_channel> const & out);
    void set_diagnostic_channel(std::shared_ptr<output_channel> const & out);
    /*@}*/

    /**
       @name Interrupts.
    */
    void set_interrupt(bool flag);
    void interrupt() { set_interrupt(true); }
    void reset_interrupt() { set_interrupt(false); }
    /*@}*/
};
}
