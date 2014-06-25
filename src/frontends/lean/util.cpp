/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "library/scoped_ext.h"
#include "frontends/lean/parser.h"

namespace lean {
void check_atomic(name const & n) {
    if (!n.is_atomic())
        throw exception(sstream() << "invalid declaration name '" << n << "', identifier must be atomic");
}

void check_in_section(parser const & p) {
    if (!in_section(p.env()))
        throw exception(sstream() << "invalid command, it must be used in a section");
}
}
