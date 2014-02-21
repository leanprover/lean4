/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/sexpr/format.h"
#include "kernel/expr.h"

namespace lean {
/**
   \brief Abstract class for providing expression position information (line number and column).
*/
class pos_info_provider {
public:
    virtual ~pos_info_provider() {}
    /**
       \brief Return the line number and position associated with the given expression.
       Throws an exception if the given expression does not have this kind of information associated with it.
    */
    virtual std::pair<unsigned, unsigned> get_pos_info(expr const & e) const = 0;
    virtual char const * get_file_name() const;
    virtual std::pair<unsigned, unsigned> get_some_pos() const = 0;

    unsigned get_line(expr const & e) const { return get_pos_info(e).first; }
    unsigned get_pos(expr const & e) const { return get_pos_info(e).second; }
    /**
       \brief Pretty print position information for the given expression.
       Return a null format object if expression is not associated with position information.
    */
    virtual format pp(expr const & e) const;
};
}
