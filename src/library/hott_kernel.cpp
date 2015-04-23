/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/inductive/inductive.h"
#include "kernel/hits/hits.h"
#include "library/inductive_unifier_plugin.h"

namespace lean {
using inductive::inductive_normalizer_extension;
/** \brief Create Lean environment for Homotopy Type Theory */
environment mk_hott_environment(unsigned trust_lvl) {
    environment env = environment(trust_lvl,
                                  false /* Type.{0} is not proof irrelevant */,
                                  true  /* Eta */,
                                  false /* Type.{0} is not impredicative */,
                                  /* builtin support for inductive and hits */
                                  compose(std::unique_ptr<normalizer_extension>(new inductive_normalizer_extension()),
                                          std::unique_ptr<normalizer_extension>(new hits_normalizer_extension())));
    return set_unifier_plugin(env, mk_inductive_unifier_plugin());
}
}
