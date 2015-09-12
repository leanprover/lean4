/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "compiler/preprocess_rec.h"
namespace lean{
void initialize_compiler_module() {
    initialize_preprocess_rec();
}
void finalize_compiler_module() {
    finalize_preprocess_rec();
}
}
