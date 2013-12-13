/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <vector>
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/expr_pair.h"
#include "frontends/lean/operator_info.h"

namespace lean {
/**
   \brief Wrapper for environment/state that provides additional objects
   that are specific to the Lean frontend.

   This wrapper provides APIs for accessing/using the Lean frontend
   extension data in the environment.
*/
class frontend {
    environment m_env;
    io_state    m_state;
public:
    frontend();
    frontend(environment const & env, io_state const & s);

    frontend mk_child() const { return frontend(m_env->mk_child(), m_state); }
    bool has_children() const { return m_env->has_children(); }
    bool has_parent() const { return m_env->has_parent(); }

    environment const & get_environment() const { return m_env; }
    operator environment const &() const { return get_environment(); }
    operator ro_environment() const { return ro_environment(m_env); }

    /**
       @name Environment API
    */
    /*@{*/
    level add_uvar(name const & n, level const & l) { return m_env->add_uvar(n, l);  }
    level add_uvar(name const & n) { return m_env->add_uvar(n); }
    level get_uvar(name const & n) const { return m_env->get_uvar(n); }
    void add_definition(name const & n, expr const & t, expr const & v, bool opaque = false) { m_env->add_definition(n, t, v, opaque); }
    void add_theorem(name const & n, expr const & t, expr const & v) { m_env->add_theorem(n, t, v); }
    void add_definition(name const & n, expr const & v, bool opaque = false) { m_env->add_definition(n, v, opaque); }
    void add_axiom(name const & n, expr const & t) { m_env->add_axiom(n, t); }
    void add_var(name const & n, expr const & t) { m_env->add_var(n, t); }
    object get_object(name const & n) const { return m_env->get_object(n); }
    optional<object> find_object(name const & n) const { return m_env->find_object(n); }
    bool has_object(name const & n) const { return m_env->has_object(n); }
    typedef environment_cell::object_iterator object_iterator;
    object_iterator begin_objects() const { return m_env->begin_objects(); }
    object_iterator end_objects() const { return m_env->end_objects(); }
    object_iterator begin_local_objects() const { return m_env->begin_local_objects(); }
    object_iterator end_local_objects() const { return m_env->end_local_objects(); }
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
    void add_mixfixl(std::initializer_list<name> const & l, unsigned p, expr const & d) { add_mixfixl(l.size(), l.begin(), p, d); }
    void add_mixfixr(std::initializer_list<name> const & l, unsigned p, expr const & d) { add_mixfixr(l.size(), l.begin(), p, d); }
    void add_mixfixc(std::initializer_list<name> const & l, unsigned p, expr const & d) { add_mixfixc(l.size(), l.begin(), p, d); }
    void add_mixfixo(std::initializer_list<name> const & l, unsigned p, expr const & d) { add_mixfixo(l.size(), l.begin(), p, d); }
    /**
        \brief Return the operator (if one exists) associated with the
        given expression.

        \remark If an operator is not associated with \c e, then
        return the null operator.

        \remark This is used for pretty printing.

        \remark If unicode is false, then only operators containing
        safe ASCII chars are considered.
    */
    operator_info find_op_for(expr const & e, bool unicode) const;
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
    void mark_implicit_arguments(expr const & n, std::initializer_list<bool> const & l);
    /**
       \brief Syntax sugar for mark_implicit_arguments(n, {true, ..., true}), with prefix_sz true's.
    */
    void mark_implicit_arguments(name const & n, unsigned prefix_sz);
    void mark_implicit_arguments(expr const & n, unsigned prefix_sz);
    /** \brief Return true iff \c n has implicit arguments */
    bool has_implicit_arguments(name const & n) const;
    /** \brief Return the position of the arguments that are implicit. */
    std::vector<bool> const & get_implicit_arguments(name const & n) const;
    /**
        \brief Return the position of the arguments that are implicit.
        \remark If \c n is not a constant, then return the empty vector.
    */
    std::vector<bool> const & get_implicit_arguments(expr const & n) const;
    /**
        \brief This frontend associates an definition with each
        definition (or postulate) that has implicit arguments. The
        additional definition has explicit arguments, and it is called
        n::explicit. The explicit version can be used when the Lean
        frontend can't figure out the value for the implicit
        arguments.
    */
    name const & get_explicit_version(name const & n) const;
    /**
       \brief Return true iff \c n is the name of the "explicit"
       version of an object with implicit arguments
    */
    bool is_explicit(name const & n) const;
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
    */
    optional<expr> get_coercion(expr const & from_type, expr const & to_type) const;

    /**
       \brief Return the list of coercions for the given type.
       The result is a list of pairs (to_type, function).
    */
    list<expr_pair> get_coercions(expr const & from_type) const;

    /**
       \brief Return true iff the given expression is a coercion. That is, it was added using
       \c add_coercion.
    */
    bool is_coercion(expr const & f) const;
    /*@}*/

    /**
       @name State management.
    */
    /*@{*/
    io_state const & get_state() const { return m_state; }
    operator io_state const &() const { return m_state; }
    io_state & get_state() { return m_state; }
    operator io_state &() { return m_state; }
    options get_options() const { return m_state.get_options(); }
    void set_options(options const & opts) { return m_state.set_options(opts); }
    template<typename T> void set_option(name const & n, T const & v) { m_state.set_option(n, v); }
    void set_regular_channel(std::shared_ptr<output_channel> const & out) { m_state.set_regular_channel(out); }
    void set_diagnostic_channel(std::shared_ptr<output_channel> const & out) { m_state.set_diagnostic_channel(out); }
    /*@}*/
};

bool is_explicit(ro_environment const & env, name const & n);
bool has_implicit_arguments(ro_environment const & env, name const & n);
name const & get_explicit_version(ro_environment const & env, name const & n);
std::vector<bool> const & get_implicit_arguments(ro_environment const & env, name const & n);
bool is_coercion(ro_environment const & env, expr const & f);
operator_info find_op_for(ro_environment const & env, expr const & e, bool unicode);
}
