/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <sstream>
#include "runtime/exception.h"
#include "runtime/thread.h"
#include "runtime/sstream.h"

namespace lean {
throwable::throwable(char const * msg):m_msg(msg) {}
throwable::throwable(std::string const & msg):m_msg(msg) {}
throwable::throwable(sstream const & strm):m_msg(strm.str()) {}
throwable::~throwable() noexcept {}
char const * throwable::what() const noexcept { return m_msg.c_str(); }

stack_space_exception::stack_space_exception(char const * component_name):
    m_msg((sstream() << "deep recursion was detected at '" << component_name << "' (potential solution: increase stack space in your system)").str()) {
}

memory_exception::memory_exception(char const * component_name):
    m_msg((sstream() << "excessive memory consumption detected at '" << component_name << "' (potential solution: increase memory consumption threshold)").str()) {
}

char const * heartbeat_exception::what() const noexcept {
    return "(deterministic) timeout";
}
}
