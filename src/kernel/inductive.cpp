/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"

namespace lean {

environment environment::add_inductive_decls(inductive_decls const & decls) const {
    std::cout << "add_inductive_decls\n";
    for (expr const & p : decls.m_params) {
        std::cout << "param>> " << p << " : " << mlocal_type(p) << "\n";
    }
    for (inductive_decl const & d : decls.m_decls) {
        std::cout << "ind>>   " << d.m_name << " : " << d.m_type << "\n";
        for (constructor const & c : d.m_constructors) {
            std::cout << ">>       " << c << " : " << mlocal_type(c) << "\n";
        }
    }
    // TODO(Leo)
    return *this;
}
}
