/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/pos_info_provider.h"

namespace lean {
format pos_info_provider::pp(expr const & e) const {
    try {
        auto p = get_pos_info(e);
        return paren(format{format("line"), colon(), space(), format(p.first), colon(), space(), format("pos"), colon(), space(), format(p.second)});
    } catch (exception &) {
        return format();
    }
}
}
