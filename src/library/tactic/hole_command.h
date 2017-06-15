/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
optional<name> is_hole_command(environment const & env, name const & n);
void initialize_hole_command();
void finalize_hole_command();
}
