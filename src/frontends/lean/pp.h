/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sexpr/options.h"
#include "kernel/context.h"
#include "kernel/formatter.h"

namespace lean {
class frontend;
class environment;
formatter mk_pp_formatter(ro_environment const & env);
std::ostream & operator<<(std::ostream & out, frontend const & fe);
/** \brief Return true iff the given object is supported by this pretty printer. */
bool supported_by_pp(object const & obj);
}
