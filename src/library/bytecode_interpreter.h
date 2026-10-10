/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include "library/elab_environment.h"
#include "runtime/object.h"

namespace lean {
namespace interpreter {
}
void initialize_bytecode_interpreter();
void finalize_bytecode_interpreter();
}
