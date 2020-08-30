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
obj_res set_io_result(obj_arg a);
obj_res set_io_error(obj_arg e);
obj_res set_io_error(char const * msg);
obj_res set_io_error(std::string const & msg);
obj_res decode_io_error(int errnum, b_obj_arg fname);
obj_res io_wrap_handle(FILE * hfile);
void initialize_io();
void finalize_io();
}
