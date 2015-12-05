/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
namespace lean {
namespace blast {
/** \brief Return true iff \c e is of the form (not a) or (a -> false), and false otherwise */
bool is_not(expr const & e, expr & a);
bool is_not(expr const & e);
bool is_false(expr const & e);
}}
