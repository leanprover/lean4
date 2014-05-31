/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/lua.h"
#include "kernel/environment.h"

namespace lean {
/**
   \brief Create a section scope. When a section is closed all definitions and theorems are relativized with
   respect to var_decls and axioms. That is, var_decls and axioms become new arguments for the definitions and axioms.
*/
environment begin_section_scope(environment const & env);

/**
   \brief Create a namespace scope. A namespace is just a mechanism
   for appending the prefix n to declarations added to the
   environment.
*/
environment begin_namespace_scope(environment const & env, char const * n);

/**
   \brief End/close a scoped created using \c begin_section_scope or \c begin_namespace_scope.
   Throws an exception if there is no open scope.
*/
environment end_scope(environment const & env);

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

void open_scope(lua_State * L);
}
