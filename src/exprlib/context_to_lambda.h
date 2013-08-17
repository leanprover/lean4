/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "context.h"
namespace lean {
/**
   \brief Given the context (n_1 : T_1 [:= V_1]) ... (n_k : T_k [:= V_k]) and expression e into,
   return the "meaningless" lambda expression:

   (lambda (n_1 : (foo T_1 V_1)) ... (lambda (n_k : (foo T_k V_k)) e))

   The constant "foo" is irrelevant, it is just used as a marker.
   It is used to "glue" T_i and V_i.

   This little hack allows us to use the machinery for instantiating
   lambdas with contexts.

   \remark If a context entry (n_i : T_i [:= V_i]) does not have a
   value V_i, then we just use (foo T_i).
*/
expr context_to_lambda(context const & c, expr const & e);
}
