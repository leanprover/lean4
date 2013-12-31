/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <limits>
#include <stdio.h>
#include <ios>
#include "util/serializer.h"
#include "util/exception.h"

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

#define BIG_BUFFER 1024

void serializer_core::write_double(double d) {
    std::ostringstream out;
    // TODO(Leo): the following code may miss precision.
    // We should use std::ios::hexfloat, but it is not supported by
    // g++ yet.
    out.flags (std::ios::scientific);
    out.precision(std::numeric_limits<double>::digits10 + 1);
    out << std::hex << d;
    write_string(out.str());
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

double deserializer_core::read_double() {
    // TODO(Leo): use std::hexfloat as soon as it is supported by g++
    std::istringstream in(read_string());
    double r;
    in >> r;
    return r;
}

void throw_corrupted_file() {
    throw exception("corrupted binary file");
}
}
