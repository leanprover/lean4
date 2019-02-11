/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
bool emit_extern_call_core(std::ostream & out, environment const & env, name const & backend, name const & fn, string_refs const & attrs);
void emit_extern_call(std::ostream & out, environment const & env, name const & backend, name const & fn, string_refs const & attrs);
void initialize_extern_attribute();
void finalize_extern_attribute();
}
