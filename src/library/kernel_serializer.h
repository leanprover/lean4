/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "runtime/serializer.h"
#include "kernel/declaration.h"
#include "kernel/inductive/inductive.h"

namespace lean {
serializer & operator<<(serializer & s, declaration const & d);
declaration read_declaration(deserializer & d);
inline deserializer & operator>>(deserializer & d, declaration & decl) { decl = read_declaration(d); return d; }

serializer & operator<<(serializer & s, inductive::certified_inductive_decl const & d);
inductive::certified_inductive_decl read_certified_inductive_decl(deserializer & d);

void initialize_kernel_serializer();
void finalize_kernel_serializer();
}
