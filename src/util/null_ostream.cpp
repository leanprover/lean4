/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <fstream>
#include "util/thread.h"
#include "util/null_ostream.h"

namespace lean {
int null_streambuf::overflow(int c) {
    setp(m_buffer, m_buffer+sizeof(m_buffer));
    return (c == std::ifstream::traits_type::eof()) ? '\0' : c;
}

MK_THREAD_LOCAL_GET_DEF(null_streambuf, get_null_streambuf);

null_streambuf * null_ostream::rdbuf() const {
    return &get_null_streambuf();
}
}
