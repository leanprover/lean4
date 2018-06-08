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

expr replace_propagating_pos(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f, bool use_cache = true);
inline expr replace_propagating_pos(expr const & e, std::function<optional<expr>(expr const &)> const & f, bool use_cache = true) {
    return replace_propagating_pos(e, [&](expr const & e, unsigned) { return f(e); }, use_cache);
}
expr instantiate_propagating_pos(expr const & a, unsigned s, unsigned n, expr const * subst);
expr instantiate_propagating_pos(expr const & e, unsigned n, expr const * s);
expr instantiate_propagating_pos(expr const & e, std::initializer_list<expr> const & l);
expr instantiate_propagating_pos(expr const & e, unsigned i, expr const & s);
expr instantiate_propagating_pos(expr const & e, expr const & s);

expr abstract_propagating_pos(expr const & e, unsigned n, expr const * s);
inline expr abstract_propagating_pos(expr const & e, expr const & s) { return abstract_propagating_pos(e, 1, &s); }
expr abstract_propagating_pos(expr const & e, name const & l);

expr Fun_p(unsigned num, expr const * locals, expr const & b);
inline expr Fun_p(expr const & local, expr const & b) { return Fun_p(1, &local, b); }
inline expr Fun_p(std::initializer_list<expr> const & locals, expr const & b) { return Fun_p(locals.size(), locals.begin(), b); }
template<typename T> expr Fun_p(T const & locals, expr const & b) { return Fun_p(locals.size(), locals.data(), b); }

expr Pi_p(unsigned num, expr const * locals, expr const & b);
inline expr Pi_p(expr const & local, expr const & b) { return Pi_p(1, &local, b); }
inline expr Pi_p(std::initializer_list<expr> const & locals, expr const & b) { return Pi_p(locals.size(), locals.begin(), b); }
template<typename T> expr Pi_p(T const & locals, expr const & b) { return Pi_p(locals.size(), locals.data(), b); }
}
