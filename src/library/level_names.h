/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "kernel/declaration.h"
#include "kernel/inductive/inductive.h"
namespace lean {
/**
    \brief Return a declaration equivalent to \c d, but where level parameter names
    do not conflict with global parameter names also used in \c d.
*/
declaration sanitize_level_params(declaration const & d);
/**
   \brief Return new level parameters and inductive decls equivalent to \c decls,
   but where level parameter names do not conflict with global parameter names also used in \c decls.
*/
pair<level_param_names, list<inductive::inductive_decl>> sanitize_level_params(level_param_names const & ls,
                                                                               list<inductive::inductive_decl> const & decls);
}
