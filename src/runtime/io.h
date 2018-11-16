/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "runtime/object.h"
namespace lean {
obj_res io_prim_put_str(b_obj_arg s, obj_arg w);
obj_res io_prim_get_line(obj_arg w);
obj_res io_prim_handle_mk(b_obj_arg s, uint8 mode, uint8 bin, obj_arg w);
obj_res io_prim_handle_is_eof(b_obj_arg h, obj_arg w);
obj_res io_prim_handle_flush(b_obj_arg h, obj_arg w);
obj_res io_prim_handle_close(b_obj_arg h, obj_arg w);
obj_res io_prim_handle_get_line(b_obj_arg h, obj_arg w);
}
