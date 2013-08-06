/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "environment.h"

namespace lean {
/**
   \brief Create top-level environment with builtin objects.
*/
environment mk_toplevel();
}
