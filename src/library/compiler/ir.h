/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "library/compiler/util.h"
namespace lean {
namespace ir {
typedef object_ref decl;
std::string decl_to_string(decl const & d);
void test(decl const & d);
environment compile(environment const & env, options const & opts, comp_decls const & decls);
}
}
