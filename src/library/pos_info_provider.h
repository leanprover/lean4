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
/* TEMPORARY HACK for getting position information until we have the new frontend */
expr save_pos(expr const & e, pos_info const & pos);
expr copy_pos(expr const & src, expr const & dest);
void erase_pos(expr const & e);
optional<pos_info> get_pos(expr const & e);
void reset_positions();

class pos_info_provider {
public:
    virtual ~pos_info_provider() {}
    virtual optional<pos_info> get_pos_info(expr const & e) const { return ::lean::get_pos(e); }
    virtual char const * get_file_name() const;
    virtual pos_info get_some_pos() const = 0;

    pos_info get_pos_info_or_some(expr const & e) const {
        if (auto it = get_pos_info(e))
            return *it;
        else
            return get_some_pos();
    }

    virtual expr save_pos(expr const & e, pos_info const & pos) { return ::lean::save_pos(e, pos); }

    /**
       \brief Pretty print position information for the given expression.
       Return a null format object if expression is not associated with position information.
    */
    virtual format pp(expr const & e) const;
};

void initialize_pos_info_provider();
void finalize_pos_info_provider();
}
