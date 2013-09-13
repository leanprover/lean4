/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/kernel_exception.h"
#include "library/formatter.h"
#include "library/state.h"

namespace lean {
/** \brief Pretty print an arbitrary kernel exception using the given formatter */
format pp(formatter const & fmt, kernel_exception const & ex, options const & opts = options());
format pp(unknown_name_exception const & ex, options const & opts = options());
format pp(already_declared_exception const & ex, options const & opts = options());
format pp(formatter const & fmt, app_type_mismatch_exception const & ex, options const & opts = options());
format pp(formatter const & fmt, function_expected_exception const & ex, options const & opts = options());
format pp(formatter const & fmt, type_expected_exception const & ex, options const & opts = options());
format pp(formatter const & fmt, def_type_mismatch_exception const & ex, options const & opts = options());
regular const & operator<<(regular const & out, kernel_exception const & ex);
diagnostic const & operator<<(diagnostic const & out, kernel_exception const & ex);
}
