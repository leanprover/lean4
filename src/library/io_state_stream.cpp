/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/io_state_stream.h"
#include "kernel/kernel_exception.h"
namespace lean {
io_state_stream const & operator<<(io_state_stream const & out, endl_class) {
    out.get_stream() << std::endl;
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, expr const & e) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(out.get_formatter()(e, opts), opts);
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, object const & obj) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(out.get_formatter()(obj, opts), opts);
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, environment const & env) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(out.get_formatter()(env, opts), opts);
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, kernel_exception const & ex) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(ex.pp(out.get_formatter(), opts), opts);
    return out;
}
}
