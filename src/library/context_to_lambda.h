/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/context.h"
namespace lean {
/**
   \brief Given the context (n_1 : T_1 [:= V_1]) ... (n_k : T_k [:= V_k]) and expression e into,
   return the "meaningless" lambda expression:

   (lambda (n_1 : (fake T_1 V_1)) ... (lambda (n_k : (fake T_k V_k)) e))

   The constant "fake" is irrelevant, it is just used as a marker.
   It is used to "glue" T_i and V_i.

   This little hack allows us to use the machinery for instantiating
   lambdas with contexts.

   \remark If a context entry (n_i : T_i [:= V_i]) does not have a
   value V_i, then we just use (fake T_i).
*/
expr context_to_lambda(context const & c, expr const & e);
/**
   \brief Return true if \c e is a fake context created using
   context_to_lambda.
   (lambda (n_1 : (fake T_1 V_1)) ... (lambda (n_k : (fake T_k V_k)) e))
*/
bool is_fake_context(expr const & e);
/**
   \brief Return the name n_1 of the head of the (fake) context
   (lambda (n_1 : (fake T_1 V_1)) ... (lambda (n_k : (fake T_k V_k)) e))

   \pre is_fake_context(e)
*/
name const & fake_context_name(expr const & e);
/**
   \brief Return the domain T_1 of the head of the (fake) context
   (lambda (n_1 : (fake T_1 V_1)) ... (lambda (n_k : (fake T_k V_k)) e))

   \pre is_fake_context(e)
*/
expr const & fake_context_domain(expr const & e);
/**
   \brief Return the value V_1 of the head of the (fake) context
   (lambda (n_1 : (fake T_1 V_1)) ... (lambda (n_k : (fake T_k V_k)) e))

   \pre is_fake_context(e)
   \remark If the head does not have a value, then return a null expression
*/
expr const & fake_context_value(expr const & e);
/**
   \brief Return the rest (lambda (n_2 : (fake T_2 V_2)) ... (lambda (n_k : (fake T_k V_k)) e)) of the fake context
   (lambda (n_1 : (fake T_1 V_1)) ... (lambda (n_k : (fake T_k V_k)) e))

   \pre is_fake_context(e)
*/
expr const & fake_context_rest(expr const & e);
}
