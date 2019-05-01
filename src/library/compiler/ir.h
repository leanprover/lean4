/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/compiler/util.h"
namespace lean {
namespace ir {
typedef object_ref decl;
std::string decl_to_string(decl const & d);
}
ir::decl to_ir_decl(environment const & env, comp_decl const & d);
}
