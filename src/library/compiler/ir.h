/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "library/elab_environment.h"
#include "library/compiler/util.h"
#include "library/ir_types.h"
namespace lean {
namespace ir {
typedef object_ref decl;
std::string decl_to_string(decl const & d);
void test(decl const & d);
elab_environment compile(elab_environment const & env, options const & opts, comp_decls const & decls);
elab_environment add_extern(elab_environment const & env, name const & fn);
LEAN_EXPORT string_ref emit_c(elab_environment const & env, name const & mod_name);
void emit_llvm(elab_environment const & env, name const & mod_name, std::string const &filepath);
}
void initialize_ir();
void finalize_ir();
}
