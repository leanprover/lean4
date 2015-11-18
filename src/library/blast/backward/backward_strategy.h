/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
namespace blast {
optional<expr> apply_backward_strategy();

void initialize_backward_strategy();
void finalize_backward_strategy();
}}
