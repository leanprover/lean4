/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "kernel/environment.h"

namespace lean {
/** \brief Auxiliary exception that stores the "real" exception, and a new
    environment that should replace the one in the parser.
    This is a trick to simulate commands that had "partial success".
    Example: we may have failed to type check a proof, but we may have succeeded
    in checking the theorem's type. So, we may store the theorem as an axiom, and
    continue. This feature is useful to avoid a cascade of error messages when
    a heavily useful theorem is broken in the beginning of the file.
*/
class update_environment_exception : public exception {
    environment                m_env;
    std::shared_ptr<throwable> m_exception;
public:
    update_environment_exception(environment const & env, std::shared_ptr<throwable> const & ex):
        exception("exception"), m_env(env), m_exception(ex) {}
    virtual ~update_environment_exception() {}
    virtual throwable * clone() const { return new update_environment_exception(m_env, m_exception); }
    virtual void rethrow() const { throw *this; }
    virtual char const * what() const noexcept { return m_exception->what(); }
    throwable const & get_exception() const { return *(m_exception.get()); }
    environment const & get_env() const { return m_env; }
};
}
