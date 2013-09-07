/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "natlib.h"
#include "intlib.h"
#include "reallib.h"
#include "specialfnlib.h"

namespace lean {
class environment;
/**
   \brief Import all arithmetic related builtin libraries.
*/
void import_arithlibs(environment & env);
}
