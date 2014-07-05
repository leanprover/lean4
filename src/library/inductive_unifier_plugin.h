/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/unifier_plugin.h"
namespace lean {
/** \brief Return a unifier plugin that handles constraints containing eliminators and introductions */
unifier_plugin mk_inductive_unifier_plugin();
}
