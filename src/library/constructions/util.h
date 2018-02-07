/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_generator.h"

namespace lean {
name_generator mk_constructions_name_generator();
void initialize_constructions_util();
void finalize_constructions_util();
}
