/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "runtime/object.h"
namespace lean {
obj_res set_io_result(obj_arg r, obj_arg a);
obj_res set_io_error(obj_arg r, obj_arg e);
obj_res set_io_error(obj_arg r, char const * msg);
obj_res set_io_error(obj_arg r, std::string const & msg);
void initialize_io();
void finalize_io();
}
