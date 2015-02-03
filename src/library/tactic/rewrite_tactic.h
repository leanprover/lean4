/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic.h"
#include "library/tactic/location.h"

namespace lean {
enum class rewrite_multiplicity { Once, AtMostN, ExactlyN, ZeroOrMore, OneOrMore };

class rewrite_element {
    name                 m_lemma;
    bool                 m_symm;
    bool                 m_unfold;
    rewrite_multiplicity m_multiplicity;
    optional<unsigned>   m_num;
    location             m_location;
    rewrite_element(name const & l, bool symm, bool unfold, rewrite_multiplicity m, optional<unsigned> const & n,
                    location const & loc);
public:
    rewrite_element();
    static rewrite_element mk_unfold(name const & l, location const & loc);
    static rewrite_element mk_once(name const & l, bool symm, location const & loc);
    static rewrite_element mk_at_most_n(name const & l, unsigned n, bool symm, location const & loc);
    static rewrite_element mk_exactly_n(name const & l, unsigned n, bool symm, location const & loc);
    static rewrite_element mk_zero_or_more(name const & l, bool symm, location const & loc);
    static rewrite_element mk_one_or_more(name const & l, bool symm, location const & loc);
    name const & get_name() const { return m_lemma; }
    bool unfold() const { return m_unfold; }
    bool symm() const {
        lean_assert(!unfold());
        return m_symm;
    }
    rewrite_multiplicity multiplicity() const {
        lean_assert(!unfold());
        return m_multiplicity;
    }
    bool has_num() const {
        return multiplicity() == rewrite_multiplicity::AtMostN || multiplicity() == rewrite_multiplicity::ExactlyN;
    }
    unsigned num() const {
        lean_assert(has_num());
        return *m_num;
    }
    location get_location() const { return m_location; }

    friend serializer & operator<<(serializer & s, rewrite_element const & elem);
    friend deserializer & operator>>(deserializer & d, rewrite_element & e);
};

/** \brief Create a rewrite tactic expression, where elems was created using \c mk_rewrite_elements. */
expr mk_rewrite_tactic_expr(buffer<rewrite_element> const & elems);

/** \brief Create rewrite tactic that applies the given rewrite elements */
tactic mk_rewrite_tactic(buffer<rewrite_element> const & elems);

void initialize_rewrite_tactic();
void finalize_rewrite_tactic();
}
