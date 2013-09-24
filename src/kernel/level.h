/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <algorithm>
#include "util/name.h"
#include "util/sexpr/format.h"
#include "util/sexpr/options.h"

namespace lean {
class environment;
struct level_cell;
enum class level_kind { UVar, Lift, Max };
/**
   \brief Universe level.
*/
class level {
    friend class environment;
    level_cell * m_ptr;
    /** \brief Private constructor used by the environment to create a new universe variable named \c n with internal id \c u. */
    level(level const & l, unsigned k);
    level(level_cell * ptr);
    friend level to_level(level_cell * c);
    friend level_cell * to_cell(level const & l);
    friend level operator+(level const & l, unsigned k);
public:
    /** \brief Universe 0 */
    level();
    level(name const & n);
    level(level const & l);
    level(level&& s);
    ~level();

    unsigned hash() const;

    bool is_bottom() const;

    friend level_kind    kind       (level const & l);
    friend name const &  uvar_name  (level const & l);
    friend level const & lift_of    (level const & l);
    friend unsigned      lift_offset(level const & l);
    friend unsigned      max_size   (level const & l);
    friend level const & max_level  (level const & l, unsigned i);

    level & operator=(level const & l);
    level & operator=(level&& l);

    friend bool operator==(level const & l1, level const & l2);
    friend bool operator!=(level const & l1, level const & l2) { return !operator==(l1, l2); }
    friend bool operator<(level const & l1, level const & l2);
    friend void swap(level & l1, level & l2) { std::swap(l1, l2); }

    friend std::ostream & operator<<(std::ostream & out, level const & l);
};

level max(level const & l1, level const & l2);
level max(std::initializer_list<level> const & l);
level operator+(level const & l, unsigned k);

inline bool is_uvar(level const & l) { return kind(l) == level_kind::UVar;  }
inline bool is_lift(level const & l) { return kind(l) == level_kind::Lift; }
inline bool is_max (level const & l) { return kind(l) == level_kind::Max;  }

/** \brief Return a */
inline level const * max_begin_levels(level const & l) { return &max_level(l, 0); }
inline level const * max_end_levels(level const & l)   { return max_begin_levels(l) + max_size(l); }

/** \brief Pretty print the given level expression, unicode characters are used if \c unicode is \c true. */
format pp(level const & l, bool unicode);
/** \brief Pretty print the given level expression using the given configuration options. */
format pp(level const & l, options const & opts = options());
}
void print(lean::level const & l);
