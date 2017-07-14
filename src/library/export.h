/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
void export_as_lowtext(std::ostream & out, environment const & env,
    optional<list<name>> const & decls);
void export_all_as_lowtext(std::ostream & out, environment const & env) {
    return export_as_lowtext(out, env, {});
}
}
