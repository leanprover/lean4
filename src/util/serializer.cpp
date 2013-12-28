/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/serializer.h"

namespace lean {
std::string deserializer_core::read_string() {
    std::string r;
    while (true) {
        char c = m_in.get();
        if (c == 0)
            break;
        r += c;
    }
    return r;
}
}
