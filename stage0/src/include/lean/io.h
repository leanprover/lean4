/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <stdio.h>
#include <string>
#include <lean/object.h>

namespace lean {
inline obj_res io_result_mk_ok(obj_arg a) { return lean_io_result_mk_ok(a); }
inline obj_res io_result_mk_error(obj_arg e) { return lean_io_result_mk_error(e); }
obj_res io_result_mk_error(char const * msg);
obj_res io_result_mk_error(std::string const & msg);
obj_res decode_io_error(int errnum, b_obj_arg fname);
obj_res io_wrap_handle(FILE * hfile);
void initialize_io();
void finalize_io();
}
