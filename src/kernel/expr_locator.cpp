/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "expr_locator.h"
#include "exception.h"

namespace lean {
expr_locator::~expr_locator() {}
bool expr_locator::has_location(expr const & e) const { return false; }
std::pair<unsigned, unsigned> expr_locator::get_location(expr const & e) const { lean_unreachable(); return mk_pair(0, 0); }

std::shared_ptr<expr_locator> mk_dummy_expr_locator() {
    return std::shared_ptr<expr_locator>(new expr_locator());
}

void throw_exception(expr_locator const & loc, expr const & src, char const * msg) {
    if (loc.has_location(src)) {
        std::ostringstream s;
        auto p = loc.get_location(src);
        s << "(line: " << p.first << ", pos: " << p.second << ") " << msg;
        throw exception(s.str());
    } else {
        throw exception(msg);
    }
}

void throw_exception(expr_locator const & loc, expr const & src, format const & msg) {
    std::ostringstream s;
    s << msg;
    throw_exception(loc, src, s.str().c_str());
}
}
