/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/interrupt.h"
#include "util/utf8.h"
#include "library/vm/vm_string.h"

namespace lean {
static void to_string(vm_obj o, std::string & s) {
    check_system("to_string");
    while (!is_simple(o)) {
        push_unicode_scalar(s, cidx(cfield(o, 0)));
        o  = cfield(o, 1);
    }
}

std::string to_string(vm_obj const & o) {
    std::string r;
    to_string(o, r);
    return r;
}

vm_obj to_obj(std::string const & str) {
    buffer<unsigned> tmp;
    utf8_decode(str, tmp);
    vm_obj   r = mk_vm_simple(0);
    unsigned i = tmp.size();
    while (i > 0) {
        --i;
        vm_obj args[2] = { mk_vm_simple(tmp[i]), r };
        r = mk_vm_constructor(1, 2, args);
    }
    return r;
}
}
