/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name.h"
#include "api/exception.h"
#include "api/lean_name.h"
namespace lean {
inline name * to_name(lean_name n) { return reinterpret_cast<name *>(n); }
inline name const & to_name_ref(lean_name n) { return *reinterpret_cast<name *>(n); }
inline lean_name of_name(name * n) { return reinterpret_cast<lean_name>(n); }
void to_buffer(unsigned sz, lean_name const * ns, buffer<name> & r);

inline list<name> * to_list_name(lean_list_name n) { return reinterpret_cast<list<name> *>(n); }
inline list<name> const & to_list_name_ref(lean_list_name n) { return *reinterpret_cast<list<name> *>(n); }
inline lean_list_name of_list_name(list<name> * n) { return reinterpret_cast<lean_list_name>(n); }
}
