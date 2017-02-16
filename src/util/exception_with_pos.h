/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include <exception>
#include <string>
#include <memory>
#include "util/message_definitions.h"
#include "util/exception.h"

namespace lean {
class exception_with_pos : public exception {
protected:
    exception_with_pos() {}
public:
    exception_with_pos(char const * msg): exception(msg) {}
    exception_with_pos(std::basic_string<char> const & msg): exception(msg) {}
    exception_with_pos(sstream const & strm): exception(strm) {}
    virtual optional<pos_info> get_pos() const = 0;
};
}
