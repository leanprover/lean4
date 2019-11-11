/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/format.h"
#include "kernel/expr.h"
#include "util/message_definitions.h"

namespace lean {
/* TEMPORARY HACK for getting position information until we have the new frontend */
expr save_pos(expr const & e, pos_info const & pos);
expr copy_pos(expr const & src, expr const & dest);
expr unwrap_pos(expr const & e);
optional<pos_info> get_pos(expr const & e);
bool contains_pos(expr const & e);

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

// TEMP: these functions ignore position annotations

optional<expr> is_local_p(expr const & e);
name const & local_name_p(expr const & e);
name const & local_pp_name_p(expr const & e);
expr const & local_type_p(expr const & e);
binder_info local_info_p(expr const & e);
expr update_local_p(expr const & e, expr const & new_type);
expr update_local_p(expr const & e, expr const & new_type, binder_info bi);
expr update_local_p(expr const & e, binder_info bi);

expr abstract_p(expr const & e, unsigned n, expr const * subst);

expr Fun_p(unsigned num, expr const * locals, expr const & b);
inline expr Fun_p(expr const & local, expr const & b) { return Fun_p(1, &local, b); }
inline expr Fun_p(std::initializer_list<expr> const & locals, expr const & b) { return Fun_p(locals.size(), locals.begin(), b); }
template<typename T> expr Fun_p(T const & locals, expr const & b) { return Fun_p(locals.size(), locals.data(), b); }

expr Pi_p(unsigned num, expr const * locals, expr const & b);
inline expr Pi_p(expr const & local, expr const & b) { return Pi_p(1, &local, b); }
inline expr Pi_p(std::initializer_list<expr> const & locals, expr const & b) { return Pi_p(locals.size(), locals.begin(), b); }
template<typename T> expr Pi_p(T const & locals, expr const & b) { return Pi_p(locals.size(), locals.data(), b); }
}
