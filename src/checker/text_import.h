/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "kernel/environment.h"
#include <iostream>

namespace lean {

void import_from_text(std::istream & in, environment & env);

}
