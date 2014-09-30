/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/int64.h"
#include "kernel/environment.h"

namespace lean {
environment update_fingerprint(environment const & env, unsigned h);
uint64 get_fingerprint(environment const & env);
void initialize_fingerprint();
void finalize_fingerprint();
}
