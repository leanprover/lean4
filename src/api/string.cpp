/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <string.h> // NOLINT
#include "api/lean_string.h"
#include "api/string.h"

namespace lean {
char const * mk_string(std::string const & s) {
    char * r  = new char[s.size() + 1];
    for (unsigned i = 0; i < s.size(); i++)
        r[i] = s[i];
    r[s.size()] = 0;
    return r;
}

char const * mk_string(char const * s) {
    unsigned sz = strlen(s);
    char * r  = new char[sz + 1];
    for (unsigned i = 0; i < sz; i++)
        r[i] = s[i];
    r[sz] = 0;
    return r;
}

void del_string(char const * s) {
    delete[] s;
}
}

void lean_string_del(char const * s) {
    lean::del_string(s);
}
