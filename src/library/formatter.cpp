/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include "kernel/kernel_exception.h"
#include "library/printer.h"
#include "library/formatter.h"

namespace lean {
class simple_formatter_cell : public formatter_cell {
public:
    virtual format operator()(expr const & e, options const & opts) {
        std::ostringstream s; s << e; return format(s.str());
    }
    virtual format operator()(context const & c, options const & opts) {
        std::ostringstream s; s << c; return format(s.str());
    }
    virtual format operator()(context const & c, expr const & e, bool format_ctx, options const & opts) {
        std::ostringstream s;
        if (format_ctx)
            s << c << "|-\n";
        s << mk_pair(e, c);
        return format(s.str());
    }
    virtual format operator()(object const & obj, options const & opts) {
        std::ostringstream s; s << obj; return format(s.str());
    }
    virtual format operator()(environment const & env, options const & opts) {
        std::ostringstream s; s << env; return format(s.str());
    }
};
formatter mk_simple_formatter() {
    return formatter(new simple_formatter_cell());
}
}
