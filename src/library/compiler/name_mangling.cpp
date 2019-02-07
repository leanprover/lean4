/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <fstream>
#include <string>
#include "runtime/utf8.h"
#include "util/name.h"

namespace lean {
static std::string mangle(std::string const & s) {
    std::string out;
    size_t i = 0;
    while (i < s.size()) {
        unsigned c = next_utf8(s, i);
        if (c < 255) {
            if (isalnum(c)) {
                out += static_cast<unsigned char>(c);
            } else if (c == '_') {
                out += "__";
            } else {
                out += "_x_";
                out += ('0' + (c / 16));
                out += ('0' + (c % 16));
            }
        } else {
            out += "_u_";
            out += ('0' + (c / 4096));
            c %= 4096;
            out += ('0' + (c / 256));
            c %= 256;
            out += ('0' + (c / 16));
            out += ('0' + (c % 16));
        }
    }
    return out;
}

static void mangle(name const & n, std::string & out) {
    if (n.is_anonymous()) {
        return;
    } else if (n.is_numeral()) {
        mangle(n.get_prefix(), out);
        out += "_";
        out += n.get_numeral().to_std_string();
        out += "_";
    } else {
        lean_assert(n.is_string());
        if (!n.get_prefix().is_anonymous()) {
            mangle(n.get_prefix(), out);
            out += "_";
        }
        out += mangle(n.get_string().to_std_string());
    }
}

std::string mangle(name const & n, bool add_prefix) {
    std::string out;
    if (add_prefix) out += "l_";
    mangle(n, out);
    return out;
}
}
