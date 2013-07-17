/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved. 
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura 
*/
#include "exception.h"

namespace lean {

exception::exception(char const * msg):m_msg(msg) {
}

exception::exception(std::string const & msg):m_msg(msg) {
}

exception::exception(exception const & e):m_msg(e.m_msg) {
}

exception::~exception() noexcept {
}

char const * exception::what() const noexcept {
    return m_msg.c_str();
}

}
