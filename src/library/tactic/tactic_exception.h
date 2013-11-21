/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/exception.h"

namespace lean {
class tactic_exception : public exception {
public:
    tactic_exception(char const * msg):exception(msg) {}
    tactic_exception(std::string const & msg):exception(msg) {}
    tactic_exception(sstream const & strm):exception(strm) {}
};
}
