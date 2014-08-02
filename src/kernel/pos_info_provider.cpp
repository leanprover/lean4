/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/pos_info_provider.h"

namespace lean {
char const * pos_info_provider::get_file_name() const {
    return "unknown";
}
format pos_info_provider::pp(expr const & e) const {
    try {
        auto p = get_pos_info_or_some(e);
        return format{format(get_file_name()), colon(), format(p.first), colon(), format(p.second), colon()};
    } catch (exception &) {
        return format();
    }
}
}
