/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
class local_instance {
    name m_class_name;
    expr m_local;
public:
    local_instance(name const & n, expr const & e):
        m_class_name(n), m_local(e) {}
    name const & get_class_name() const { return m_class_name; }
    expr const & get_local() const { return m_local; }
    friend bool operator==(local_instance const & l1, local_instance const & l2) {
        return mlocal_name(l1.m_local) == mlocal_name(l2.m_local);
    }
};

inline bool operator!=(local_instance const & l1, local_instance const & l2) {
    return !(l1 == l2);
}

typedef list<local_instance> local_instances;
}
