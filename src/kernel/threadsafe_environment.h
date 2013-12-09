/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/shared_mutex.h"
#include "kernel/environment.h"

namespace lean {
/**
   \brief The environment object is not thread safe.
   The helper classes \c read_only_environment and \c read_write_environment
   provides thread safe access to the environment object.

   \remark We do not use these classes internally.
   They are only used for implementing external APIs.
*/
class read_only_environment {
    environment   m_env;
    shared_lock   m_lock;
public:
    read_only_environment(environment const & env);
    ~read_only_environment();
    operator environment const &() const { return m_env; }
    environment const * operator->() const { return &m_env; }
};

/**
   \brief See \c read_only_environment
*/
class read_write_environment {
    environment     m_env;
    exclusive_lock  m_lock;
public:
    read_write_environment(environment const & env);
    ~read_write_environment();
    operator environment &() { return m_env; }
    environment * operator->() { return &m_env; }
};
}
