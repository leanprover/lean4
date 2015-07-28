/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/opt_cmd.h"

namespace lean {
static options set_line_col(options const & _opts, unsigned line, unsigned col) {
    options opts = _opts;
    opts = opts.update(name("line"), line);
    opts = opts.update(name("column"), col);
    return opts;
}

static bool has_show(options const & opts, name const & kind, unsigned & line, unsigned & col) {
    if (opts.get_bool(kind)) {
        line = opts.get_unsigned("line", 0);
        col  = opts.get_unsigned("column", 0);
        return true;
    } else {
        return false;
    }
}

options set_show_goal(options const & opts, unsigned line, unsigned col) {
    return set_line_col(opts.update(name("show_goal"), true), line, col);
}

bool has_show_goal(options const & opts, unsigned & line, unsigned & col) {
    return has_show(opts, "show_goal", line, col);
}

options set_show_hole(options const & opts, unsigned line, unsigned col) {
    return set_line_col(opts.update(name("show_hole"), true), line, col);
}

bool has_show_hole(options const & opts, unsigned & line, unsigned & col) {
    return has_show(opts, "show_hole", line, col);
}
}
