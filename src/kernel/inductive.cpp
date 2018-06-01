/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"

namespace lean {

environment environment::add_inductive_decls(inductive_decls const & /* decls */) const {
    return *this;
}

}
