/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/io_state.h"

namespace lean {
class elaborator_exception : public formatted_exception {
public:
    elaborator_exception(expr const & e, format const & fmt):formatted_exception(e, fmt) {}
    elaborator_exception(expr const & e, sstream const & strm):formatted_exception(e, format(strm.str())) {}
};
}
