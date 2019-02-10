/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
string_ref mk_extern_call(environment const & env, string_ref const & backend, string_refs const & attrs);
void initialize_extern_attribute();
void finalize_extern_attribute();
}
