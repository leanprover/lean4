/*
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Dany Fabian
*/

#pragma once
#include "lean/object.h"
#include "util/incbin.h"
#include "util/object_ref.h"

namespace lean {
extern "C" obj_res lean_list_to_array(obj_arg type, obj_arg elems);
object_ref list_to_array(object_ref list);

namespace ir {
INCBIN(LeanRuntimeBitCode, "library/compiler/libleanruntime.bc");

extern "C" obj_res lean_ir_get_decls(b_obj_arg env);
extern "C" obj_res lean_ir_emit_llvm(b_obj_arg env, b_obj_arg mod_name, obj_arg world);

}

}
