/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/opt_cmd.h"

namespace lean {
options set_show_goal(options const & _opts, unsigned line, unsigned col) {
    options opts = _opts;
    opts = opts.update(name("show_goal"), true);
    opts = opts.update(name("line"), line);
    opts = opts.update(name("column"), col);
    return opts;
}

bool has_show_goal(options const & opts, unsigned & line, unsigned & col) {
    if (opts.get_bool("show_goal")) {
        line = opts.get_unsigned("line", 0);
        col  = opts.get_unsigned("column", 0);
        return true;
    } else {
        return false;
    }
}
}
