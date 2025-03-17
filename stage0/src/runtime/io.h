/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <stdio.h>
#include <string>
#include <lean/lean.h>

namespace lean {
inline lean_obj_res io_result_mk_ok(lean_obj_arg a) { return lean_io_result_mk_ok(a); }
inline lean_obj_res io_result_mk_error(lean_obj_arg e) { return lean_io_result_mk_error(e); }
LEAN_EXPORT lean_obj_res io_result_mk_error(char const * msg);
LEAN_EXPORT lean_obj_res io_result_mk_error(std::string const & msg);
inline lean_obj_res decode_io_error(int errnum, b_lean_obj_arg fname) { return lean_decode_io_error(errnum, fname); }
inline lean_obj_res decode_uv_error(int errnum, b_lean_obj_arg fname) { return lean_decode_uv_error(errnum, fname); }
LEAN_EXPORT lean_obj_res io_wrap_handle(FILE * hfile);
void initialize_io();
void finalize_io();
}
