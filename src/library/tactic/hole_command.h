/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
namespace lean {
optional<name> is_hole_command(environment const & env, name const & n);
void get_hole_commands(environment const & env, buffer<pair<name, std::string>> & r);
void initialize_hole_command();
void finalize_hole_command();
}
