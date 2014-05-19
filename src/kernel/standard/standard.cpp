/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/inductive/inductive.h"

namespace lean {
/** \brief Create standard Lean environment */
environment mk_environment(unsigned trust_lvl) {
    return environment(trust_lvl,
                       true /* Type.{0} is proof irrelevant */,
                       true /* Eta */,
                       true /* Type.{0} is impredicative */,
                       list<name>() /* No type class has proof irrelevance */,
                       inductive::mk_extension() /* builtin support for inductive datatypes */);
}
}
