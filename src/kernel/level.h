/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include "name.h"

namespace lean {
class environment;
struct level_cell;
typedef unsigned uvar;
enum class level_kind { UVar, Lift, Max };
/**
   \brief Universe level.
*/
class level {
    friend class environment;
    level_cell * m_ptr;
    /** \brief Private constructor used by the environment to create a new universe variable named \c n with internal id \c u. */
    level(name const & n, uvar u);
public:
    /** \brief Universe 0 */
    level();
    /** \brief Lift universe l by k (l + k) */
    level(level const & l, unsigned k);
    /** \brief New level that is >= max(l1,l2) */
    level(level const & l1, level const & l2);
    level(level const & l);
    level(level&& s);
    ~level();

    unsigned hash() const;

    friend level_kind    kind       (level const & l);
    friend name const &  uvar_name  (level const & l);
    friend uvar          uvar_idx   (level const & l);
    friend level const & lift_of    (level const & l);
    friend unsigned      lift_offset(level const & l);
    friend level const & max_level1 (level const & l);
    friend level const & max_level2 (level const & l);

    level & operator=(level const & l);
    level & operator=(level&& l);

    friend bool operator==(level const & l1, level const & l2);
    friend bool operator!=(level const & l1, level const & l2) { return !operator==(l1, l2); }
    friend void swap(level & l1, level & l2) { std::swap(l1, l2); }

    friend std::ostream & operator<<(std::ostream & out, level const & l);
};
inline level max(level const & l1, level const & l2) { return level(l1, l2); }
       level max(std::initializer_list<level> const & l);
inline level operator+(level const & l, unsigned k)  { return level(l, k); }
inline bool is_uvar(level const & l) { return kind(l) == level_kind::UVar;  }
inline bool is_lift(level const & l) { return kind(l) == level_kind::Lift; }
inline bool is_max (level const & l) { return kind(l) == level_kind::Max;  }
}
