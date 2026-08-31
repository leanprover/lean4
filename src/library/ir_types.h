/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/elab_environment.h"
namespace lean {
namespace ir {
/*
inductive IRType
| float | uint8 | uint16 | uint32 | uint64 | usize
| irrelevant | object | tobject
| float32
| struct (leanTypeName : Option Name) (types : Array IRType) : IRType
| union (leanTypeName : Name) (types : Array IRType) : IRType
| tagged
| void

Remark: we don't create struct/union types from C++.
*/
enum class type { Float, UInt8, UInt16, UInt32, UInt64, USize, Irrelevant, Object, TObject, Float32, Struct, Union, Tagged, Void };

typedef nat        var_id;
typedef nat        jp_id;
typedef name       fun_id;
typedef object_ref arg;
typedef object_ref expr;
typedef object_ref param;
typedef object_ref fn_body;
typedef object_ref alt;
typedef object_ref decl;

}
}

