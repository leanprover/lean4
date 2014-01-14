/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/exception.h"
#include "kernel/pos_info_provider.h"
#include "kernel/io_state.h"

namespace lean {
/**
   \brief Display exception in the regular stream of \c ios, using the configuration options and formatter from \c ios.
   Exceptions that contain expressions use the given \c pos_info_provider (if available) to retrieve line number information.
*/
void display_error(io_state const & ios, pos_info_provider const * p, exception const & ex);
}
