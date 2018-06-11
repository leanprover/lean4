/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"

namespace lean {

environment environment::add_inductive_decls(inductive_decls const & decls) const {
#if 1
    std::cout << "add_inductive_decls\n";
    for (inductive_decl const & d : decls.m_decls) {
        std::cout << "ind>>   " << d.m_name << " : " << d.m_type << "\n";
        for (constructor const & c : d.m_constructors) {
            std::cout << ">>       " << c.first << " : " << c.second << "\n";
        }
    }
#endif
    // TODO(Leo)
    return *this;
}
}
