/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <fstream>
#include "runtime/utf8.h"
#include "library/module.h"
#include "library/compiler/emit_cpp.h"

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
                out += "_x";
                out += ('0' + (c / 16));
                out += ('0' + (c % 16));
            }
        } else {
            out += "_u";
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
        mangle(n.get_prefix(), out);
        out += "_s";
        std::string s = mangle(n.get_string().to_std_string());
        unsigned len  = s.size();
        out += std::to_string(len);
        out += "_";
        out += s;
    }
}

std::string mangle(name const & n) {
    std::string out("_l");
    mangle(n, out);
    return out;
}

environment emit_cpp(environment const & env, comp_decls const & /* ds */) {
    // TODO(Leo)
    return env;
}

void print_cpp_code(std::ofstream & out, environment const & /* env */, module_name const & m, list<module_name> const & deps) {
    out << "// Lean compiler output\n";
    out << "// Module: " << m << "\n";
    out << "// Imports:"; for (module_name const & d : deps) out << " " << d; out << "\n";
    // TODO(Leo)
}
}
