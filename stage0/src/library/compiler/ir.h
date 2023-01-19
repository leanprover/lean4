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
/*
inductive IRType
| float | uint8 | uint16 | uint32 | uint64 | usize
| irrelevant | object | tobject
| struct (leanTypeName : Option Name) (types : Array IRType) : IRType
| union (leanTypeName : Name) (types : Array IRType) : IRType

Remark: we don't create struct/union types from C++.
*/
enum class type { Float, UInt8, UInt16, UInt32, UInt64, USize, Irrelevant, Object, TObject };

typedef nat        var_id;
typedef nat        jp_id;
typedef name       fun_id;
typedef object_ref arg;
typedef object_ref expr;
typedef object_ref param;
typedef object_ref fn_body;
typedef object_ref alt;
typedef object_ref decl;

typedef object_ref decl;
std::string decl_to_string(decl const & d);
void test(decl const & d);
environment compile(environment const & env, options const & opts, comp_decls const & decls);
environment add_extern(environment const & env, name const & fn);
string_ref emit_c(environment const & env, name const & mod_name);
void emit_llvm(environment const & env, name const & mod_name, std::string const &filepath);
}
void initialize_ir();
void finalize_ir();
}
