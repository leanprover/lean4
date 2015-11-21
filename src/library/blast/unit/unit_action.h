/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/blast/action_result.h"

namespace lean {
namespace blast {
action_result unit_action(unsigned hidx);

void initialize_unit_action();
void finalize_unit_action();
}}
