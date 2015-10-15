/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_set.h"
#include "kernel/environment.h"

namespace lean {
name_set get_relevant_thms(environment const & env, double p, double c, name_set const & relevant_symbols);
name_set get_relevant_thms(environment const & env, options const & o, name_set const & relevant_symbols);
void initialize_meng_paulson();
void finalize_meng_paulson();
}
