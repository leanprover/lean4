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
   The helper classes \c read_only_shared_environment and \c read_write_shared_environment
   provides thread safe access to the environment object.

   \remark We do not use these classes internally.
   They are only used for implementing external APIs.
*/
class read_only_shared_environment {
    ro_environment m_env;
    shared_lock    m_lock;
public:
    read_only_shared_environment(ro_environment const & env);
    ~read_only_shared_environment();
    operator ro_environment const &() const { return m_env; }
    environment_cell const * operator->() const { return m_env.m_ptr.get(); }
    environment_cell const & operator*() const { return *(m_env.m_ptr.get()); }
};

/**
   \brief See \c read_only_shared_environment
*/
class read_write_shared_environment {
    environment     m_env;
    exclusive_lock  m_lock;
public:
    read_write_shared_environment(environment const & env);
    ~read_write_shared_environment();
    operator environment const &() const { return m_env; }
    operator ro_environment() const { return ro_environment(m_env); }
    environment_cell * operator->() const { return m_env.m_ptr.get(); }
    environment_cell & operator*() const { return *(m_env.m_ptr.get()); }
};
}
