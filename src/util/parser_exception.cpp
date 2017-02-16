/*
  Copyright (c) 2017 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Sebastian Ullrich
*/
#include <string>
#include "util/parser_exception.h"

namespace lean {
MK_THREAD_LOCAL_GET_DEF(std::string, get_g_buffer);
char const * parser_exception::what() const noexcept {
  try {
    std::string & buffer = get_g_buffer();
    std::ostringstream s;
    s << m_fname << ":" << m_pos.first << ":" << m_pos.second << ": error: " << m_msg;
    buffer = s.str();
    return buffer.c_str();
  } catch (std::exception & ex) {
    // failed to generate extended message
    return m_msg.c_str();
  }
}
}
