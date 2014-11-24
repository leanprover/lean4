/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
class parser;
environment find_cmd(parser & p);
void initialize_find_cmd();
void finalize_find_cmd();
}
