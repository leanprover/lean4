/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include "kernel/environment.h"
#include "runtime/object.h"

namespace lean {
namespace ir {
uint32 run_main(environment const & env, int argv, char * argc[]);
}
void initialize_ir_interpreter();
void finalize_ir_interpreter();
}
