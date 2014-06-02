/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <vector>
#include "kernel/environment.h"

namespace lean {
namespace scope {
typedef std::vector<expr> dependencies; // local var dependencies

class abstraction_context {
protected:
    environment m_env;
public:
    abstraction_context(environment const & env):m_env(env) {}
    virtual ~abstraction_context() {}

    environment const & env() { return m_env; }
    void update_env(environment const & env) { m_env = env; }

    virtual level convert(level const & e) = 0;
    virtual expr  convert(expr const & e) = 0;
    virtual level_param_names mk_level_deps() = 0;
    virtual dependencies      mk_var_deps() = 0;
    virtual expr  Pi(expr e, dependencies const & deps) = 0;
    virtual expr  Fun(expr e, dependencies const & deps) = 0;

    virtual void add_decl_info(name const & n, level_param_names const & ps, dependencies const & deps, expr const & type) = 0;
};

typedef std::function<void(abstraction_context & ctx)> abstraction_fn;

/** \brief Add a function that should be executed when a section is closed. */
environment add(environment const & env, abstraction_fn const & fn);

/**
    \brief Add the global level declaration to the environment and current section.
    If there are no active sections, then this function behaves like \c module::add_global_level.
*/
environment add_global_level(environment const & env, name const & l);

/**
    \brief Add the given declaration to the environment and currenct section.
    If there are no active sections, then this function behaves like \c module::add.
*/
environment add(environment const & env, certified_declaration const & d, binder_info const & bi = binder_info());

/**
    \brief Add the given declaration to the environment and currenct section.
    This method throws an exception if the trust_level <= LEAN_BELIEVER_TRUST_LEVEL
    If there are no active sections, then this function behaves like \c module::add.
*/
environment add(environment const & env, declaration const & d, binder_info const & bi = binder_info());

/**
   \brief Create a section scope. When a section is closed all definitions and theorems are relativized with
   respect to var_decls and axioms. That is, var_decls and axioms become new arguments for the definitions and axioms.
*/
environment begin_section(environment const & env);

/**
   \brief Create a namespace scope. A namespace is just a mechanism
   for appending the prefix n to declarations added to the
   environment.
*/
environment begin_namespace(environment const & env, char const * n);

/**
   \brief End/close a scoped created using \c begin_section_scope or \c begin_namespace_scope.
   Throws an exception if there is no open scope.
*/
environment end(environment const & env);

/** \brief Return true iff the given environment has open sections. */
bool has_open_sections(environment const & env);

/**
   \brief Return the current namespace for \c env. The namespace is composed by the sequence
   of names provided to \c begin_namespace_scope.
*/
name const & get_namespace(environment const & env);

/**
   \brief Return the name of \c n in the current namespace of \c env.
   Example: if the current namespace is <tt>foo.bar</tt> and \c n is <tt>foo.bar.bla.1</tt>, then
   the result is <tt>bla.1</tt>.
*/
name get_name_in_namespace(environment const & env, name const & n);

/** \brief Find a declaration named \c n in \c env by taking the active namespaces into account. */
optional<declaration> find(environment const & env, name const & n);
}
}
