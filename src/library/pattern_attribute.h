/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
bool has_pattern_attribute(environment const & env, name const & d);
environment set_pattern_attribute(environment const & env, name const & d);
void initialize_pattern_attribute();
void finalize_pattern_attribute();
}
