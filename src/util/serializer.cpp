/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/serializer.h"

namespace lean {
void serializer_core::write_unsigned(unsigned i) {
    static_assert(sizeof(i) == 4, "unexpected unsigned size");
    m_out.put((i >> 24) & 0xff);
    m_out.put((i >> 16) & 0xff);
    m_out.put((i >> 8) & 0xff);
    m_out.put(i & 0xff);
}

void serializer_core::write_int(int i) {
    static_assert(sizeof(i) == 4, "unexpected int size");
    write_unsigned(i);
}

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

unsigned deserializer_core::read_unsigned() {
    unsigned r;
    static_assert(sizeof(r) == 4, "unexpected unsigned size");
    r  = static_cast<unsigned>(m_in.get()) << 24;
    r |= static_cast<unsigned>(m_in.get()) << 16;
    r |= static_cast<unsigned>(m_in.get()) << 8;
    r |= static_cast<unsigned>(m_in.get());
    return r;
}

int deserializer_core::read_int() {
    return read_unsigned();
}
}
