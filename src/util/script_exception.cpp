/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <string>
#include "util/script_exception.h"

namespace lean {
char const * script_exception::what() const noexcept {
    static thread_local std::string buffer;
    std::ostringstream strm;
    switch (get_source()) {
    case source::String:  strm << "[string]:" << get_line() << ":" << get_msg() << "\n"; break;
    case source::File:    strm << get_filename() << ":" << get_line() << ":" << get_msg() << "\n"; break;
    case source::Unknown: return get_msg();
    }
    buffer = strm.str();
    return buffer.c_str();
}
}
