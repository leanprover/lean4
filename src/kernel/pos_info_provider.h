/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/sexpr/format.h"
#include "kernel/expr.h"
#include "util/message_definitions.h"

namespace lean {
/**
   \brief Abstract class for providing expression position information (line number and column).
*/
class pos_info_provider {
public:
    virtual ~pos_info_provider() {}
    /**
       \brief Return the line number and position associated with the given expression.
       Return none if the information is not available
    */
    virtual optional<pos_info> get_pos_info(expr const & e) const = 0;
    virtual char const * get_file_name() const;
    virtual pos_info get_some_pos() const = 0;
    pos_info get_pos_info_or_some(expr const & e) const {
        if (auto it = get_pos_info(e))
            return *it;
        else
            return get_some_pos();
    }

    virtual expr save_pos(expr const &, pos_info) {
        lean_unreachable();
    }

    /**
       \brief Pretty print position information for the given expression.
       Return a null format object if expression is not associated with position information.
    */
    virtual format pp(expr const & e) const;
};
}
