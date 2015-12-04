/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/io_state_stream.h"

namespace lean {
io_state_stream const & operator<<(io_state_stream const & out, endl_class) {
    out.get_stream() << std::endl;
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, expr_kind const & k) {
    out.get_stream() << k;
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, expr const & e) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(group(out.get_formatter()(e)), opts);
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, ext_exception const & ex) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(ex.pp(out.get_formatter()), opts);
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, format const & f) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(f, opts);
    return out;
}
}
