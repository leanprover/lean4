/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "util/shared_mutex.h"
#include "kernel/environment.h"

namespace lean {
/** \brief Auxiliary object used when multiple threads are trying to populate the same environment. */
class shared_environment {
    environment          m_env;
    mutable mutex        m_mutex;
public:
    shared_environment();
    shared_environment(environment const & env);
    /** \brief Return a copy of the current environment. This is a constant time operation. */
    environment get_environment() const;
    environment env() const { return get_environment(); }
    /**
        \brief Add the given certified declaration to the environment.
        This is a constant time operation.
        It blocks this object for a small amount of time.
    */
    void add(certified_declaration const & d);
    /**
        \brief Replace the axiom with name <tt>t.get_declaration().get_name()</tt> with the theorem t.get_declaration().
        This is a constant time operation.
        It blocks this object for a small amount of time.
    */
    void replace(certified_declaration const & t);
    /**
       \brief Update the environment using the given function.
       This procedure blocks access to this object.
    */
    void update(std::function<environment(environment const &)> const & f);
};
}
